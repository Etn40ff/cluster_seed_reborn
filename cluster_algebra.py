from types import MethodType
from sage.structure.element_wrapper import ElementWrapper
from sage.structure.sage_object import SageObject
from sage.structure.parent import Parent
from sage.rings.integer_ring import ZZ

################################################################################
# Elements of a cluster algebra
################################################################################

class ClusterAlgebraElement(ElementWrapper):

    def __init__(self, parent, value):
        ElementWrapper.__init__(self, parent=parent, value=value)

        # setup methods defined only in special cases
        if parent._is_principal:
            self.g_vector = MethodType(g_vector, self, self.__class__)
            self.is_homogeneous = MethodType(is_homogeneous, self, self.__class__)
            self.homogeneous_components = MethodType(homogeneous_components, self, self.__class__)

    # This function needs to be removed once AdditiveMagmas.Subobjects implements _add_
    def _add_(self, other):
        return self.parent().retract(self.lift() + other.lift())

    # I am not sure we want to have this function: its output is most of the times not in the algebra but it is convenient to have
    def _div_(self, other):
        return self.parent().retract(self.lift()/other.lift())

    # HACK: LaurentPolynomial_mpair does not know how to compute denominators, we need to lift to its fraction field
    def lift_to_field(self):
        return self.parent().lift_to_field(self)

    # this function is quite disgusting but at least it works for any element of
    # the algebra, can we do better?
    # For cluster variables yes we can do better: use CA4 Prop 7.16
    # It looks to me that Prop 7.16 in CA IV only works if you know the
    # F-polynomial; in particular one ask d_vector() of a cluster variable (or
    # maybe of a cluster monomial if we know the cluster decomposition). The
    # current implementation is uglier but more general.
    def d_vector(self):
        n = self.parent().rk
        one = self.parent().ambient_field()(1)
        factors = self.lift_to_field().factor()
        initial = []
        non_initial = []
        [(initial if x[1] > 0 and len(x[0].monomials()) == 1 else non_initial).append(x[0]**x[1]) for x in factors]
        initial = prod(initial+[one]).numerator()
        non_initial = prod(non_initial+[one]).denominator()
        v1 = vector(non_initial.exponents()[0][:n])
        v2 = vector(initial.exponents()[0][:n])
        return tuple(v1-v2)

    def _repr_(self):
        # use this to factor d-vector in the representation
        return repr(self.lift_to_field())


####
# Methods not always defined
####

def g_vector(self):
    components = self.homogeneous_components()
    if len(components) == 1:
        return components.keys()[0]
    else:
        raise ValueError("This element is not homogeneous.")

def is_homogeneous(self):
    return len(self.homogeneous_components()) == 1

def homogeneous_components(self):
    deg_matrix = block_matrix([[self.parent()._M0,-self.parent()._B0]])
    components = dict()
    x = self.lift()
    monomials = x.monomials()
    for m in monomials:
        gvect = tuple(deg_matrix*vector(m.exponents()[0]))
        if gvect in components:
            components[gvect] += self.parent().retract(x.monomial_coefficient(m)*m)
        else:
            components[gvect] = self.parent().retract(x.monomial_coefficient(m)*m)
    return components


################################################################################
# Seeds
################################################################################

class ClusterAlgebraSeed(SageObject):

    def __init__(self, B, C, G, parent):
        self._B = copy(B)
        self._C = copy(C)
        self._G = copy(G)
        self._parent = parent
        self._path = []

    def __copy__(self):
        other = type(self).__new__(type(self))
        other._B = copy(self._B)
        other._C = copy(self._C)
        other._G = copy(self._G)
        other._parent = self._parent
        other._path = copy(self._path)
        return other

    def __eq__(self, other):
        return frozenset(self.g_vectors()) == frozenset(other.g_vectors())
        # Why was I doing something so convoluted?
        # It looks like the idea was to consider seeds up to simultaneous permutation of rows and columns,
        # the relation P between the c-matrices determines if there could exist such a permutation,
        # the remaining checks then ask about the remaining data
        
        #P = self.c_matrix().inverse()*other.c_matrix()
        #return frozenset(P.columns()) == frozenset(identity_matrix(self.parent().rk).columns()) and self.g_matrix()*P == other.g_matrix() and P.inverse()*self.b_matrix()*P == other.b_matrix() and self.parent() == other.parent()

    def _repr_(self):
        if self._path == []:
            return "The initial seed of %s"%str(self.parent())
        elif self._path.__len__() == 1:
            return "The seed of %s obtained from the initial by mutating in direction %s"%(str(self.parent()),str(self._path[0]))
        else:
            return "The seed of %s obtained from the initial by mutating along the sequence %s"%(str(self.parent()),str(self._path))

    @property
    def depth(self):
        return len(self._path)

    def parent(self):
        return self._parent

    def b_matrix(self):
        return copy(self._B)

    def c_matrix(self):
        return copy(self._C)

    def c_vector(self, j):
        return tuple(self._C.column(j))

    def c_vectors(self):
        return map(tuple, self._C.columns())

    def g_matrix(self):
        return copy(self._G)

    def g_vector(self, j):
        return tuple(self._G.column(j))

    def g_vectors(self):
        return map(tuple, self._G.columns())

    def F_polynomial(self, j):
        return self.parent().F_polynomial(self.g_vector(j))

    def F_polynomials(self):
        return (self.parent().F_polynomial(g) for g in self.g_vectors())

    def cluster_variable(self, j):
        return self.parent().cluster_variable(self.g_vector(j))

    def cluster_variables(self):
        return (self.parent().cluster_variable(g) for g in self.g_vectors())

    def mutate(self, k, inplace=True, mutating_F=True):
        if inplace:
            seed = self
        else:
            seed = copy(self)

        n = seed.parent().rk

        if k not in xrange(n):
            raise ValueError('Cannot mutate in direction ' + str(k) + '.')

        # store mutation path
        if seed._path != [] and seed._path[-1] == k:
            seed._path.pop()
        else:
            seed._path.append(k)

        # find sign of k-th c-vector
        # Will this be used enough that it should be a built-in function?
        if any(x > 0 for x in seed._C.column(k)):
            eps = +1
        else:
            eps = -1

        # store the g-vector to be mutated in case we are mutating F-polynomials also
        old_g_vector = seed.g_vector(k)

        # G-matrix
        J = identity_matrix(n)
        for j in xrange(n):
            J[j,k] += max(0, -eps*seed._B[j,k])
        J[k,k] = -1
        seed._G = seed._G*J

        # g-vector path list
        g_vector = seed.g_vector(k)
        if g_vector not in seed.parent().g_vectors_so_far():
            seed.parent()._path_dict[g_vector] = copy(seed._path)
            # F-polynomials
            if mutating_F:
                seed.parent()._F_poly_dict[g_vector] = seed._mutated_F(k, old_g_vector)

        # C-matrix
        J = identity_matrix(n)
        for j in xrange(n):
            J[k,j] += max(0, eps*seed._B[k,j])
        J[k,k] = -1
        seed._C = seed._C*J

        # B-matrix
        seed._B.mutate(k)

        # wrap up
        if not inplace:
            return seed
    
    # I am perplexed by this (yet unfinished) function. I was expecting
    # mutate_initial do be a function of ClusterAlgebra: if we change the
    # initial seed all the g-vectors, F_polynomials and paths need to mutate
    # accordingly. Am I right?
    def mutate_initial(self, k, inplace=True, mutating_F=True):
        if inplace:
            seed = self
        else:
            seed = copy(self)

        n = seed.parent().rk

        if k not in xrange(n):
            raise ValueError('Cannot mutate in direction ' + str(k) + '.')

        #store mutation path
        if seed._path != [] and seed._path[0] == k:
            seed._path.pop(0)
        else:
            seed._path.insert(0,k)

    def _mutated_F(self, k, old_g_vector):
        alg = self.parent()
        pos = alg._U(1)
        neg = alg._U(1)
        for j in xrange(alg.rk):
            if self._C[j,k] > 0:
                pos *= alg._U.gen(j)**self._C[j,k]
            else:
                neg *= alg._U.gen(j)**(-self._C[j,k])
            if self._B[j,k] > 0:
                pos *= self.F_polynomial(j)**self._B[j,k]
            elif self._B[j,k] <0:
                neg *= self.F_polynomial(j)**(-self._B[j,k])
        # TODO: understand why using // instead of / here slows the code down by
        # a factor of 3 but in the original experiments we made at sage days it
        # was much faster with // (we were working with cluter variables at the
        # time).
        # By the way, as of August 28th 2015 we split in half the running time
        # compared to sage days. With my laptop plugged in I get
        # sage: A = ClusterAlgebra(['E',8])
        # sage: seeds = A.seeds()
        # sage: %time void = list(seeds)
        # CPU times: user 26.8 s, sys: 21 ms, total: 26.9 s
        # Wall time: 26.8 s
        #####
        # Bad news: as of 19/10/2015 we got a huge slowdown:
        # right now it takes 150s with / and 100s with //
        # what did we do wrong?
        ##
        # I figured it out: the problem is that casting the result to alg._U is
        # quite slow: it amounts to run // instead of / :(
        # do we need to perform this or can we be less precise here and allow
        # F-polynomials to be rational funtions?
        # I am partucularly unhappy about this, for the moment the correct and
        # slow code is commented
        #return alg._U((pos+neg)/alg.F_polynomial(old_g_vector))
        ##
        # One more comment: apparently even without casting the result is a
        # polynomial! This is really weird but I am not going to complain. I
        # suppose we should not do the casting then

        # DR: Now I get the same computation time for / and //, 49.7s while simultaneously rebuiling sage
        return (pos+neg)/alg.F_polynomial(old_g_vector)

    def mutation_sequence(self, sequence, inplace=True, mutating_F=True):
        seq = iter(sequence)

        if inplace:
            seed = self
        else:
            seed = self.mutate(next(seq), inplace=False, mutating_F=mutating_F)

        for k in seq:
            seed.mutate(k, inplace=True, mutating_F=mutating_F)

        if not inplace:
            return seed

    def path_from_initial_seed(self):
        return copy(self._path)

    # TODO: ideally we should allow to mutate in direction "this g-vector" or
    # "this cluster variable" or "sink", "urban renewal" and all the other
    # options provided by Gregg et al. To do so I guess the best option is to
    # have a generic function transforming all these into an index and use it as
    # a decorator. In this way we can also use it in this __contains__ even
    # though one may write weird things like "sink" in A.current_seed and get
    # True as an answer.
    def __contains__(self, element):
        if isinstance(element, ClusterAlgebraElement):
            cluster = [ self.cluster_variable(i) for i in xrange(self.parent().rk) ]
        else:
            element = tuple(element)
            cluster = self.g_vectors()
        return element in cluster

################################################################################
# Cluster algebras
################################################################################

class ClusterAlgebra(Parent):
    r"""
    INPUT:

    - ``data`` -- some data defining a cluster algebra.

    - ``scalars`` -- (default ZZ) the scalars on which the cluster algebra
      is defined.

    - ``cluster_variables_prefix`` -- string (default 'x').

    - ``cluster_variables_names`` -- a list of strings.  Superseedes
      ``cluster_variables_prefix``.

    - ``coefficients_prefix`` -- string (default 'y').

    - ``coefficients_names`` -- a list of strings. Superseedes
      ``cluster_variables_prefix``.

    - ``principal_coefficients`` -- bool (default: False). Superseedes any
      coefficient defined by ``data``.
    """

    Element = ClusterAlgebraElement

    def __init__(self, data, **kwargs):
        r"""
        See :class:`ClusterAlgebra` for full documentation.
        """
        # TODO: right now we use ClusterQuiver to parse input data. It looks like a good idea but we should make sure it is.
        # TODO: in base replace LaurentPolynomialRing with the group algebra of a tropical semifield once it is implemented

        # Temporary variables
        Q = ClusterQuiver(data)
        n = Q.n()
        B0 = Q.b_matrix()[:n,:]
        I = identity_matrix(n)
        if 'principal_coefficients' in kwargs and kwargs['principal_coefficients']:
            M0 = I
        else:
            M0 = Q.b_matrix()[n:,:]
        m = M0.nrows() + n

        # Ambient space for F-polynomials
        # NOTE: for speed purposes we need to have QQ here instead of the more natural ZZ. The reason is that _mutated_F is faster if we do not cast the result to polynomials but then we get "rational" coefficients
        self._U = PolynomialRing(QQ, ['u%s'%i for i in xrange(n)])

        # Storage for computed data
        self._path_dict = dict([ (v, []) for v in map(tuple,I.columns()) ])
        self._F_poly_dict = dict([ (v, self._U(1)) for v in self._path_dict ])

        # Determine the names of the initial cluster variables
        if 'cluster_variables_names' in kwargs:
            if len(kwargs['cluster_variables_names']) == n:
                variables = kwargs['cluster_variables_names']
            else:
                    raise ValueError("cluster_variables_names should be a list of %d valid variable names"%n)
        else:
            try:
                cluster_variables_prefix = kwargs['cluster_variables_prefix']
            except:
                cluster_variables_prefix = 'x'
            variables = [cluster_variables_prefix+'%s'%i for i in xrange(n)]
            # why not just put str(i) instead of '%s'%i?

        # Determine scalars
        try:
            scalars = kwargs['scalars']
        except:
            scalars = ZZ

        # Determine coefficients and setup self._base
        if m>n:
            if 'coefficients_names' in kwargs:
                if len(kwargs['coefficients_names']) == m-n:
                    coefficients = kwargs['coefficients_names']
                else:
                    raise ValueError("coefficients_names should be a list of %d valid variable names"%(m-n))
            else:
                try:
                    coefficients_prefix = kwargs['coefficients_prefix']
                except:
                    coefficients_prefix = 'y'
                if coefficients_prefix == cluster_variables_prefix:
                    offset = n
                else:
                    offset = 0
                coefficients = [coefficients_prefix+'%s'%i for i in xrange(offset,m-n+offset)]
            # TODO: (***) base should eventually become the group algebra of a tropical semifield
            base = LaurentPolynomialRing(scalars, coefficients)
        else:
            base = scalars
            # TODO: next line should be removed when (***) is implemented
            coefficients = []

        # setup Parent and ambient
        # TODO: (***) _ambient should eventually be replaced with LaurentPolynomialRing(base, variables)
        self._ambient = LaurentPolynomialRing(scalars, variables+coefficients)
        self._ambient_field = self._ambient.fraction_field()
        # TODO: understand why using Algebras() instead of Rings() makes A(1) complain of missing _lmul_
        Parent.__init__(self, base=base, category=Rings(scalars).Commutative().Subobjects(), names=variables+coefficients)

        # Data to compute cluster variables using separation of additions
        # BUG WORKAROUND: if your sage installation does not have trac:`19538` merged uncomment the following line and comment the next
        #self._y = dict([ (self._U.gen(j), prod([self._ambient.gen(n+i)**M0[i,j] for i in xrange(m-n)])) for j in xrange(n)])
        self._y = dict([ (self._U.gen(j), prod([self._base.gen(i)**M0[i,j] for i in xrange(m-n)])) for j in xrange(n)])
        self._yhat = dict([ (self._U.gen(j), prod([self._ambient.gen(i)**B0[i,j] for i in xrange(n)])*self._y[self._U.gen(j)]) for j in xrange(n)])

        # Have we principal coefficients?
        self._is_principal = (M0 == I)

        # Store initial data
        self._B0 = copy(B0)
        self._M0 = copy(M0)
        self._n = n
        self._m = m
        self.reset_current_seed()

        # Internal data for exploring the exchange graph
        self.reset_exploring_iterator()

        # Add methods that are defined only for special cases
        if n == 2:
            self.greedy_element = MethodType(greedy_element, self, self.__class__)
            self.greedy_coeff = MethodType(greedy_coeff, self, self.__class__)
            self.theta_basis_element = MethodType(theta_basis_element, self, self.__class__)

        # TODO: understand if we need this
        #self._populate_coercion_lists_()

    # enable standard coercions: everything that is in the base can be coerced
    def _coerce_map_from_(self, other):
        return self.base().has_coerce_map_from(other)

    def _repr_(self):
        return "Cluster Algebra of rank %s"%self.rk

    def _an_element_(self):
        return self.current_seed.cluster_variable(0)

    @property
    def rk(self):
        r"""
        The rank of ``self`` i.e. the number of cluster variables in any seed of
        ``self``.
        """
        return self._n

    @property
    def current_seed(self):
        r"""
        The current seed of ``self``.
        """
        return self._seed

    @current_seed.setter
    def current_seed(self, seed):
        r"""
        Set ``self._seed`` to ``seed`` if it makes sense.
        """
        if self.contains_seed(seed):
            self._seed = seed
        else:
            raise ValueError("This is not a seed in this cluster algebra.")

    def contains_seed(self, seed):
        computed_sd = self.initial_seed
        computed_sd.mutation_sequence(seed._path, mutating_F=False)
        return computed_sd == seed

    def reset_current_seed(self):
        r"""
        Reset the current seed to the initial one
        """
        self._seed = self.initial_seed

    @property
    def initial_seed(self):
        r"""
        Return the initial seed
        """
        n = self.rk
        I = identity_matrix(n)
        return ClusterAlgebraSeed(self._B0, I, I, self)

    @property
    def initial_b_matrix(self):
        n = self.rk
        return copy(self._B0)

    def g_vectors_so_far(self):
        r"""
        Return the g-vectors of cluster variables encountered so far.
        """
        return self._path_dict.keys()

    def F_polynomial(self, g_vector):
        g_vector= tuple(g_vector)
        try:
            return self._F_poly_dict[g_vector]
        except:
            # If the path is known, should this method perform that sequence of mutations to compute the desired F-polynomial?
            # Yes, perhaps with the a prompt first, something like:
            #comp = raw_input("This F-polynomial has not been computed yet.  It can be found using %s mutations.  Continue? (y or n):"%str(directions.__len__()))
            #if comp == 'y':
            #    ...compute the F-polynomial...
            if g_vector in self._path_dict:
                raise ValueError("The F-polynomial with g-vector %s has not been computed yet.  You probably explored the exchange tree with compute_F=False.  You can compute this F-polynomial by mutating from the initial seed along the sequence %s."%(str(g_vector),str(self._path_dict[g_vector])))
            else:
                raise ValueError("The F-polynomial with g-vector %s has not been computed yet."%str(g_vector))

    @cached_method(key=lambda a,b: tuple(b) )
    def cluster_variable(self, g_vector):
        g_vector = tuple(g_vector)
        if not g_vector in self.g_vectors_so_far():
            # Should we let the self.F_polynomial below handle raising the exception?
            raise ValueError("This Cluster Variable has not been computed yet.")
        F_std = self.F_polynomial(g_vector).subs(self._yhat)
        g_mon = prod([self.ambient().gen(i)**g_vector[i] for i in xrange(self.rk)])
        # LaurentPolynomial_mpair does not know how to compute denominators, we need to lift to its fraction field
        F_trop = self.ambient_field()(self.F_polynomial(g_vector).subs(self._y)).denominator()
        return self.retract(g_mon*F_std*F_trop)

    def find_cluster_variable(self, g_vector, depth=infinity):
        r"""
        Returns the shortest mutation path to obtain the cluster variable with
        g-vector ``g_vector`` from the initial seed.

        ``depth``: maximum distance from ``self.current_seed`` to reach.

        WARNING: if this method is interrupted then ``self._sd_iter`` is left in
        an unusable state. To use again this method it is then necessary to
        reset ``self._sd_iter`` via self.reset_exploring_iterator()
        """
        g_vector = tuple(g_vector)
        mutation_counter = 0
        while g_vector not in self.g_vectors_so_far() and self._explored_depth <= depth:
            try:
                seed = next(self._sd_iter)
                self._explored_depth = seed.depth
            except:
                raise ValueError("Could not find a cluster variable with g-vector %s up to mutation depth %s after performing %s mutations."%(str(g_vector),str(depth),str(mutation_counter)))

            # If there was a way to have the seeds iterator continue after the depth_counter reaches depth,
            # the following code would allow the user to continue searching the exchange graph
            #cont = raw_input("Could not find a cluster variable with g-vector %s up to mutation depth %s."%(str(g_vector),str(depth))+"  Continue searching? (y or n):")
            #if cont == 'y':
            #    new_depth = 0
            #    while new_depth <= depth:
            #        new_depth = raw_input("Please enter a new mutation search depth greater than %s:"%str(depth))
            #    seeds.send(new_depth)
            #else:
            #    raise ValueError("Could not find a cluster variable with g-vector %s after %s mutations."%(str(g_vector),str(mutation_counter)))

            mutation_counter += 1
        return copy(self._path_dict[g_vector])

    def ambient(self):
        return self._ambient

    def ambient_field(self):
        return self._ambient_field

    def lift_to_field(self, x):
        return self.ambient_field()(1)*x.value

    def lift(self, x):
        r"""
        Return x as an element of self._ambient
        """
        return x.value

    def retract(self, x):
        return self(x)

    def gens(self):
        r"""
        Return the generators of :meth:`self.ambient`
        """
        return map(self.retract, self.ambient().gens())

    def seeds(self, depth=infinity, mutating_F=True, from_current_seed=False):
        r"""
        Return an iterator producing all seeds of ``self`` up to distance
        ``depth`` from ``self.initial_seed`` or ``self.current_seed``.

        If ``mutating_F`` is set to false it does not compute F_polynomials
        """
        if from_current_seed:
            seed = self.current_seed
        else:
            seed = self.initial_seed

        yield seed
        depth_counter = 0
        n = self.rk
        cl = frozenset(seed.g_vectors())
        clusters = {}
        clusters[cl] = [ seed, range(n) ]
        gets_bigger = True
        while gets_bigger and depth_counter < depth:
            gets_bigger = False
            keys = clusters.keys()
            for key in keys:
                sd, directions = clusters[key]
                while directions:
                    i = directions.pop()
                    new_sd  = sd.mutate(i, inplace=False, mutating_F=mutating_F)
                    new_cl = frozenset(new_sd.g_vectors())
                    if new_cl in clusters:
                        j = map(tuple,clusters[new_cl][0].g_vectors()).index(new_sd.g_vector(i))
                        try:
                            clusters[new_cl][1].remove(j)
                        except:
                            pass
                    else:
                        gets_bigger = True
                        # doublecheck this way of producing directions for the new seed: it is taken almost verbatim fom ClusterSeed
                        new_directions = [ j for j in xrange(n) if j > i or new_sd.b_matrix()[j,i] != 0 ]
                        clusters[new_cl] = [ new_sd, new_directions ]
                        # Use this if we want to have the user pass info to the
                        # iterator
                        #new_depth = yield new_sd
                        #if new_depth > depth:
                        #    depth = new_depth
                        yield new_sd
            depth_counter += 1

    def reset_exploring_iterator(self, mutating_F=True):
        self._sd_iter = self.seeds(mutating_F=mutating_F)
        self._explored_depth = 0

    def explore_to_depth(self, depth):
        while self._explored_depth <= depth:
            try:
                seed = next(self._sd_iter)
                self._explored_depth = seed.depth
            except:
                break

    def cluster_fan(self, depth=infinity):
        seeds = self.seeds(depth=depth, mutating_F=False)
        cones = map(lambda s: Cone(s.g_vectors()), seeds)
        return Fan(cones)

    # DESIDERATA. Some of these are probably unrealistic
    def upper_cluster_algebra(self):
        pass

    def upper_bound(self):
        pass

    def lower_bound(self):
        pass

####
# Methods only defined for special cases
####

# Greedy elements exist only in rank 2
# Does not yet take into account coefficients, this can probably be done by
# using the greedy coefficients to write down the F-polynomials
def greedy_element(self, d_vector):
    b = abs(self._B0[0,1])
    c = abs(self._B0[1,0])
    a1 = d_vector[0]
    a2 = d_vector[1]
    # TODO: we need to have something like initial_cluster_variables so that we
    # do not have to use the generators of the ambient field. (this would also
    # make it better behaved when allowing different names)
    # Warning: there might be issues with coercions, make sure there are not
    x1 = self._ambient.gens()[0]
    x2 = self._ambient.gens()[1]
    if a1 < 0:
        if a2 < 0:
            return self.retract(x1**(-a1)*x2**(-a2))
        else:
            return self.retract(x1**(-a1)*((1+x2**c)/x1)**a2)
    elif a2 < 0:
        return self.retract(((1+x1**b)/x2)**a1*x2**(-a2))
    output = 0
    for p in xrange(0,a2+1):
        for q in xrange(0,a1+1):
            output += self.greedy_coefficient(d_vector,p,q)*x1**(b*p)*x2**(c*q)
    return self.retract(x1**(-a1)*x2**(-a2)*output)

# Is this function something we want to make public or do we want to make this a
# private method changing it to _greedy_coeff ?
# Since we are giving long names to things we might want to change this into
# greedy_coefficient
def greedy_coefficient(self,d_vector,p,q):
    b = abs(self._B0[0,1])
    c = abs(self._B0[1,0])
    a1 = d_vector[0]
    a2 = d_vector[1]
    p = Integer(p)
    q = Integer(q)
    if p == 0 and q == 0:
        return 1
    sum1 = 0
    for k in range(1,p+1):
        bin = 0
        if a2-c*q+k-1 >= k:
            bin = binomial(a2-c*q+k-1,k)
        sum1 += (-1)**(k-1)*self.greedy_coefficient(d_vector,p-k,q)*bin
    sum2 = 0
    for l in range(1,q+1):
        bin = 0
        if a1-b*p+l-1 >= l:
            bin = binomial(a1-b*p+l-1,l)
        sum2 += (-1)**(l-1)*self.greedy_coefficient(d_vector,p,q-l)*bin
    #print "sum1=",sum1,"sum2=",sum2
    return max(sum1,sum2)


# At the moment I know only how to compute theta basis in rank 2
# maybe we should let ClusterAlgebra have this method for any rank and have a
# NotImplementedError to encourage someone (read: Greg) to code this
# I think Greg already has some code to do this
# I asked about the code and it seems Greg has very little confidence in the code he has so far...
def theta_basis_element(self, g_vector):
    pass



################################################################################
# Elements of a tropical semifield
################################################################################

class TropicalSemifieldElement(ElementWrapper):

    def __init__(self, parent, value):
        ElementWrapper.__init__(self, parent=parent, value=value)

    def vector(self):
        try:
            return vector(self.lift().exponents()[0])
        except:
            return vector(ZZ, self.parent().ngens())

    def _add_(self, other):
        s = self.vector()
        o = other.vector()
        r = map(min,zip(s,o))
        v = self.parent().gens()
        return prod([ x**i for (x,i) in zip(v,r) ])

    def _repr_(self):
        return repr(self.lift())

    def __invert__(self):
        return self.parent().retract(self.lift().__invert__())

################################################################################
# Tropical Semifield
################################################################################

class TropicalSemifield(Parent):

    Element = TropicalSemifieldElement

    def __init__(self, n=1, prefix='x', names=None):

        # setup Parent and ambient
        if names == None:
            names = [prefix+'%s'%i for i in xrange(n)]
        Parent.__init__(self, base=ZZ, category=CommutativeRings().Subobjects(), names=names, gens=names)
        self._ambient = LaurentPolynomialRing(ZZ, names)

    def gens(self):
        return map(lambda x: self(x), self._ambient.gens())

    def ngens(self):
        return self._ambient.ngens()

    # enable standard coercions: everything that is in the base can be coerced
    def _coerce_map_from_(self, other):
        return self.base().has_coerce_map_from(other)

    def _repr_(self):
        return "Tropical Semifield on %s generators"%self.ngens()

    def _an_element_(self):
        return self(1)

    def lift(self, x):
        return x.value

    def retract(self, x):
        return self(x)

    def ambient(self):
        return self._ambient

    def is_field(self):
        return False

    def is_prime_field(self):
        return False

    # I'm not sure the term makes sense for a semifield, its group algebra certainly has to be an integral domain
    def is_integral_domain(self, proof=True):
        return True

    def is_finite(self):
        return False

