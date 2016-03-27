r"""
Tropicalized version of cluster algebras

AUTHORS:

- Salvatore Stella
"""
#*****************************************************************************
#       Copyright (C) 2013 Salvatore Stella <sstella@ncsu.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#*****************************************************************************


#######################
# Serious Issues
###
# * The plot is completely messed up (there might be issues with the relabeling)
#   It should be fixed: it was a problem in
#   _affine_acyclic_type_d_vectors_iter()
#   were I was assuming that the orbits are delta translations instead of
#   k*delta translations
#
#   sage: B=matrix([[0,2,0],[-1,0,1],[0,-2,0]])
#   sage: T=TropicalClusterAlgebra(B,depth=5)
#   sage: T.cartan_type()
#   ['B', 2, 1]^* relabelled by {0: 0, 1: 2, 2: 1}
#   sage: T.mutation_type()
#   ['BB', 2, 1]
#   sage: T
#   A combinatorial model for a cluster algebra of rank 3 and type ['BB', 2, 1]
#   sage: G=T.plot_cluster_fan_stereographically()

######################
# Note to self:
# this package can be made input/output agnostic by defining a decorator to take
# care of the translation. Do this before publishing. Maybe rename g_vectors to
# variables etc etc

from sage.combinat.root_system.cartan_type import CartanType_abstract, CartanType
from copy import copy
from sage.matrix.matrix import Matrix
from sage.combinat.cluster_algebra_quiver.quiver_mutation_type import QuiverMutationType_Irreducible, QuiverMutationType_Reducible, QuiverMutationType
from sage.structure.sage_object import SageObject
from sage.sets.all import Set
from sage.combinat.root_system.cartan_matrix import CartanMatrix
from sage.all import matrix
from sage.combinat.cluster_algebra_quiver.quiver import ClusterQuiver
from sage.combinat.permutation import Permutations
from sage.misc.cachefunc import cached_method
from sage.rings.infinity import infinity
from sage.rings.rational_field import QQ
from sage.modules.free_module_element import vector
from sage.combinat.subset import Subsets
from sage.misc.flatten import flatten
from sage.calculus.var import var
from sage.symbolic.relation import solve
from sage.rings.integer import Integer

class TropicalClusterAlgebra(SageObject):
    r"""
    A combinatorial model for cluster algebras

    The init function should be changed in order to be more consistent with
    ClusterSeed and QuiverMutationType
    """
    def __init__(self, data, coxeter=None, mutation_type=None, depth=infinity):
        
        data = copy(data)

        if isinstance(data, Matrix):
            if not data.is_skew_symmetrizable():
                raise ValueError("The input must be a skew symmetrizable integer matrix")
            self.B0 = data
            self.rk = self.B0.ncols()
        
        elif isinstance(data, CartanType_abstract):
            self.rk = data.rank()
            
            if Set(data.index_set()) != Set(range(self.rk)):
                relabelling = dict(zip(data.index_set(),range(self.rk)))
                data = data.relabel(relabelling)

            self.cartan_type.set_cache(data)
            
            if coxeter==None:
                coxeter = range(self.rk)
            if Set(coxeter) != Set(data.index_set()):
                raise ValueError("The Coxeter element need to be a list permuting the entries of the index set of the Cartan type")
            self.coxeter.set_cache(copy(coxeter))
            
            self.cartan_companion.set_cache(data.cartan_matrix())
            self.B0 = 2-self.cartan_companion()

            for i in range(self.rk):
                for j in range(i,self.rk):
                    a = coxeter[j]
                    b = coxeter[i]
                    self.B0[a,b] = -self.B0[a,b]

        elif type(data) in [QuiverMutationType_Irreducible, QuiverMutationType_Reducible]:
            self.__init__(data.b_matrix(),mutation_type=data, depth=depth)

        elif type(data)==list:
            self.__init__(CartanType(data), coxeter=coxeter, depth=depth)
        
        else:
            raise ValueError("Input is not valid")

        # this is a hack to deal with type ['D', n, 1] since mutation_type()
        # can't distinguish it
        if mutation_type:
            self.mutation_type.set_cache(QuiverMutationType(mutation_type))

        self._depth = depth
    
    def _repr_(self):
            r"""
            Returns the description of ``self``.
            """
            description = 'A combinatorial model for a cluster algebra of rank %d' %(self.rk)
            if self.mutation_type.is_in_cache():
                description += ' and type %s' %(self.mutation_type())
            return description

    def set_depth(self, depth):
        self._depth = depth
        self.g_vectors.clear_cache()

    @cached_method
    def mutation_type(self):
        r"""
        Taken from the cluster algebra package

        WARNING: quiver.mutation_type() is not able to identify type ['D', n, 1]
        as a temporary fix we allow to force the mutation type
        """
        return self.quiver().mutation_type()

    @cached_method
    def b_matrix(self, cluster='initial'):
        if cluster=='initial':
            return self.B0
       
        #review this part (fix sign)
        exchange = []
        for v in cluster:
            ex_v = [ x for x in self.g_vectors() if self.are_exchangeable(v,x) ]
            ex_v = [ x for x in ex_v if all([self.are_compatible(x,y) for y in cluster if y != v]) ]
            if len(ex_v) != 1:
                print (v,ex_v)
                raise ValueError("Did not find exchange. Try increasing depth")
            exchange.append(ex_v[0])
        vectors = []
        for (v,w) in zip(cluster, exchange):
            sign = self.exchange_sign(v,w)
            tsum = self.twisted_sum(v,w)
            vectors.append(vector(sign*(v+w-tsum)))
        V = matrix(vectors).transpose()
        C = matrix(map(vector,cluster)).inverse().transpose()
        return C*V
    
    @cached_method
    def exchange_sign(self, alpha, beta):
        if alpha in self.initial_cluster():
            return -1
        if beta in self.initial_cluster():
            return 1
        
        if self.is_finite():
            tau = self.tau_c
        elif self.is_affine():
            gck = self.gamma().associated_coroot()
            if alpha.scalar(gck) > 0 or beta.scalar(gck) > 0:
                tau = self.tau_c_inverse
            elif alpha.scalar(gck) < 0 or beta.scalar(gck) < 0:
                tau = self.tau_c
            else:
                sup_a = self._tube_support(alpha)
                sup_b = self._tube_support(beta)
                sup_a_red = [ x for x in sup_a if x not in sup_b ]
                if any( [ self.tau_c(x) in sup_b for x in sup_a_red ] ): 
                    return -1
                else:
                    return 1
        else:
            raise ValueError("Sign function defined only for finite and affine algebras")
        
        ta = tau(alpha)
        tb = tau(beta)
        if ta + tb == tau(alpha+beta):
            sign = 1
        else:
            sign = -1
        return sign*self.exchange_sign(ta,tb)

    @cached_method
    def euler_matrix(self):
        return 1+matrix(self.rk,map(lambda x: min(x,0),self.B0.list()))

    @cached_method
    def cartan_companion(self):
        return CartanMatrix(2-matrix(self.rk,map(abs,self.B0.list())))

    @cached_method
    def quiver(self, cluster='initial'):
        quiver = ClusterQuiver(self.b_matrix(cluster=cluster))
        #fix this: @lazy_attribute will force the evaluation
        if self.mutation_type.is_in_cache():
           quiver._mutation_type = self.mutation_type()
        return quiver

    def show(self):
        r"""
        Display the quiver associated to ``self``
        """
        self.quiver().show()

    @cached_method
    def is_finite(self):
        r"""
        Taken from the cluster algebra package
        """
        mt = self.mutation_type()
        if type(mt) is str:
            return False
        else:
            return mt.is_finite()

    @cached_method
    def is_affine(self):
        r"""
        Inspiration taken from cluster algebra package
        """
        mt = self.mutation_type()
        if type(mt) is str:
            return False
        else:
            return mt.is_affine()

    @cached_method
    def is_acyclic(self, cluster='initial'):
        r"""
        Returns True iff self is acyclic (i.e., if the underlying quiver is acyclic).
        Taken from ClusterSeed
        """
        return self.quiver(cluster=cluster)._digraph.is_directed_acyclic()

    @cached_method
    def cartan_type(self):
        r"""
        Returns the Cartan type of the Cartan companion of self.b_matrix()

        Only crystallographic types are implemented

        Warning: this function is redundant but the corresonding method in
        CartanType does not recognize all the types
        """
        A = self.cartan_companion()
        n = self.rk
        degrees_dict = dict(zip(range(n),map(sum,2-A)))
        degrees_set = Set(degrees_dict.values())

        types_to_check = [ ["A",n] ]
        if n > 1:
            types_to_check.append(["B",n])
        if n > 2:
            types_to_check.append(["C",n])
        if n > 3:
            types_to_check.append(["D",n])
        if n >=6 and n <= 8:
            types_to_check.append(["E",n])
        if n == 4:
            types_to_check.append(["F",n])
        if n == 2:
            types_to_check.append(["G",n])
        if n >1:
            types_to_check.append(["A", n-1,1])
            types_to_check.append(["B", n-1,1])
            types_to_check.append(["BC",n-1,2])
            types_to_check.append(["A", 2*n-2,2])
            types_to_check.append(["A", 2*n-3,2])
        if n>2:
            types_to_check.append(["C", n-1,1])
            types_to_check.append(["D", n,2])
        if n>3:
            types_to_check.append(["D", n-1,1])
        if n >=7 and n <= 9:
            types_to_check.append(["E",n-1,1])
        if n == 5:
            types_to_check.append(["F",4,1])
        if n == 3:
            types_to_check.append(["G",n-1,1])
            types_to_check.append(["D",4,3])
        if n == 5:
            types_to_check.append(["E",6,2])

        for ct_name in types_to_check:
            ct = CartanType(ct_name)
            if 0 not in ct.index_set():
                ct = ct.relabel(dict(zip(range(1,n+1),range(n))))
            ct_matrix = ct.cartan_matrix()
            ct_degrees_dict = dict(zip(range(n),map(sum,2-ct_matrix)))
            if Set(ct_degrees_dict.values()) != degrees_set:
                continue
            for p in Permutations(range(n)):
                relabeling = dict(zip(range(n),p))
                ct_new = ct.relabel(relabeling)
                if ct_new.cartan_matrix() == A:
                    return copy(ct_new)
        raise ValueError("Type not recognized")

    def dynkin_diagram(self):
        return self.cartan_type().dynkin_diagram()

    @cached_method
    def root_space(self):
        root_space = self.cartan_companion().root_system().root_space(QQ)
        return copy(root_space)

    @cached_method
    def weight_space(self):
        weight_space = self.cartan_companion().root_system().weight_space(QQ)
        return copy(weight_space)

    @cached_method
    def coxeter(self):
        r"""
        Returns a list expressing the coxeter element corresponding to self._B
        (twisted) reflections are applied from top of the list, for example
        [2, 1, 0] correspond to s_2s_1s_0

        Sources == non positive columns == leftmost letters
        """
        zero_vector = vector([0 for x in range(self.rk)])
        coxeter = []
        B = copy(self.B0)
        columns = B.columns()
        source = None
        for j in range(self.rk):
            for i in range(self.rk):
                if all(x <=0 for x in columns[i]) and columns[i] != zero_vector:
                    source = i
                    break
            if source == None:
                if B != matrix(self.rk):
                    raise ValueError("Unable to find a Coxeter element representing self.B0")
                coxeter += [ x for x in range(self.rk) if x not in coxeter]
                break
            coxeter.append(source)
            columns[source] = zero_vector
            B = matrix(columns).transpose()
            B[source] = zero_vector
            columns = B.columns()
            source = None
        return tuple(coxeter)

    @cached_method
    def initial_cluster(self):
        cluster = []
        for i in range(self.rk):
            c = list(self.coxeter())
            c.reverse()
            found = False
            while c:
                a = c.pop()
                if a == i: 
                    found = True
                    psi = self.simple_roots()[i]
                if found:
                    psi = self.simple_reflection(a, psi)
            cluster.append(psi)
        return tuple(cluster)

    @cached_method
    def simple_roots(self):
        return self.root_space().simple_roots()

    @cached_method
    def simple_reflections(self):
        return self.root_space().simple_reflections()

    @cached_method
    def simple_reflection(self, i, v):
        return self.root_space().simple_reflection(i)(v)

    @cached_method
    def c(self, v):
        sequence = list(self.coxeter())
        sequence.reverse()
        for i in sequence:
            v = self.simple_reflection(i, v)
        return v

    @cached_method
    def c_inverse(self, v):
        sequence = list(self.coxeter())
        for i in sequence:
            v = self.simple_reflection(i, v)
        return v

    @cached_method
    def tau_c(self, v):
        c = list(self.coxeter())
        psi = self.initial_cluster()
        psi_p = map(lambda x: -self.c(x), psi)
        v = self.c(v)
        v_n = 0
        while c:
            i = c.pop()
            d = min(v[i],0)
            v_n += d*psi[i]
            v += d*psi_p[i]
        return v - v_n
    
    @cached_method
    def tau_c_inverse(self, v):
        c = list(self.coxeter())
        c.reverse()
        psi = self.initial_cluster()
        v_n = 0
        while c:
            i = c.pop()
            d = -min(v[i],0)
            v_n += d*psi[i]
            v -= d*psi[i]
        return self.c_inverse(v) - v_n

    @cached_method
    def delta(self):
        """r
        Assume roots are labeled by range(self._n)
        """
        if self.is_affine():
            annihilator_basis = self.cartan_companion().transpose().integer_kernel().gens()
            delta = sum(
                    annihilator_basis[0][i]*self.simple_roots()[i]
                    for i in range(self.rk) )
            return delta
        else:
            raise ValueError("delta is defined only for affine types")
    
    @cached_method
    def gamma(self):
        """r
        Assume roots are labeled by range(self._n)
        Return the generalized eigenvector of the cartan matrix of eigenvalue 1
        in the span of the finite root system
        """
        if self.is_affine():
            C = [ self.c(x) for x in self.simple_roots() ]
            C = map(vector, C)
            C = matrix(C).transpose()
            delta = vector(self.delta())
            gamma = (C-1).solve_right(delta)
            # the following two lines could probably ve replaced by the
            # assumption i0 = 0
            ct = self.cartan_type()
            i0 = [ i for i in ct.index_set() if i not in ct.classical().index_set() ][0]
            gamma = gamma-gamma[i0]/delta[i0]*delta
            gamma = sum( [ gamma[i]*self.simple_roots()[i] for i in range(self.rk) ] )
            return gamma
        else:
            raise ValueError("gamma is defined only for affine types")

    @cached_method
    def g_vectors(self):
        if self.is_finite():
            g_vectors = self._g_vector_iter()
        elif self.is_affine():
            if self._depth != infinity:
                g_vectors = self._g_vector_iter()
            else:
                raise ValueError("d_vectors, for affine types, can only be computed up to a finite depth")
        else:
            raise ValueError("Not implemented yet")
        return tuple([ v for v in g_vectors ])

    def _g_vector_iter(self):
        depth = self._depth
        depth_counter = 0
        g_vectors = {}
        for v in self.initial_cluster():
            g_vectors[v] = ["forward", "backward"]
        if self.is_affine():
            for v in self.tubes_transversal():
                g_vectors[v] = ["forward", "backward"]
        gets_bigger = True
        while gets_bigger and depth_counter <= depth:
            gets_bigger = False
            constructed_vectors = g_vectors.keys()
            for v in constructed_vectors:
                directions = g_vectors[v]
                while directions:
                    next_move = directions.pop()
                    if next_move == "forward":
                        next_vector =  self.tau_c(v)
                        if next_vector not in g_vectors.keys():
                            g_vectors[next_vector] = ["forward"]
                            gets_bigger = True
                    if next_move == "backward":
                        next_vector = self.tau_c_inverse(v)
                        if next_vector not in g_vectors.keys():
                            g_vectors[next_vector] = ["backward"]
                            gets_bigger = True
                    if directions:
                        continue
                    yield v
            depth_counter += 1

    @cached_method
    def _positive_classical_roots_in_finite_orbits(self):
        if not self.is_affine():
            raise ValueError("Method defined only for affine algebras")
        rs = self.root_space()
        crs = rs.classical()
        injection = crs.module_morphism(on_basis=lambda i: rs.simple_root(i),codomain=rs)
        classical_roots = [ injection(x) for x in crs.positive_roots() ]
        gammacheck = self.gamma().associated_coroot()
        return tuple([ x for x in classical_roots if gammacheck.scalar(x) == 0 ])

    @cached_method
    def tubes_transversal(self):
        if not self.is_affine():
            raise ValueError("Transversal for tubes can be computed only in affine type")
        roots = self._positive_classical_roots_in_finite_orbits()
        transversal = [ x for x in roots if self.tau_c_inverse(x) not in roots]
        return tuple(transversal)

    @cached_method
    def tubes_bases(self):
        if not self.is_affine():
            raise ValueError("The bases of the tubes can be computed only in affine type")
        roots = self._positive_classical_roots_in_finite_orbits()
        sums = [ x+y for (x,y) in Subsets(roots, 2) ]
        simple_roots = [ x for x in roots if x not in sums]
        starting_points = [ x for x in simple_roots if x in self.tubes_transversal() ]
        bases = []
        for x in starting_points:
            done = False
            y = x
            basis = [ x ]
            while not done:
                y = self.tau_c(y)
                if y not in basis:
                    basis.append(y)
                else:
                    done = True
            bases.append(tuple(basis))
        return tuple(bases)

    @cached_method
    def affine_tubes(self):
        tubes = []
        bases = self.tubes_bases()
        for basis in bases:
            tube = [ basis ]
            length = len(basis)
            for i in range(1, length-1):
                layer = [ tube[-1][j] + basis[(j+i) % length] for j in range(length) ]
                tube.append(tuple(layer))
            tubes.append(tuple(tube))
        return tuple(tubes)

    def orbit(self, element):
        depth = self._depth
        if depth is infinity and not self.is_finite():
            raise ValueError("g_vectors, for infinite types, can only be computed up to a given depth")
        depth_counter = 0
        orbit = {}
        orbit[0] = element
        gets_bigger = True
        while gets_bigger and depth_counter < depth:
            gets_bigger = False
            forward = self.tau_c(orbit[depth_counter])
            backward = self.tau_c_inverse(orbit[-depth_counter])
            if forward != orbit[-depth_counter]:
                depth_counter += 1
                orbit[depth_counter] = forward
                if backward != forward:
                    orbit[-depth_counter] = backward
                    gets_bigger = True
        return orbit

    def ith_orbit(self, i):
        return self.orbit(self.initial_cluster()[i])

    @cached_method
    def _tube_support(self, alpha):
        gck = self.gamma().associated_coroot()
        if gck.scalar(alpha) != 0:
            raise ValueError("Root not in U_c")
        tubes = list(self.affine_tubes())
        ack = alpha.associated_coroot()
        while tubes:
            tube = tubes.pop()
            if any([ack.scalar(x) != 0 for x in tube[0]]):
                sup_a = []
                roots = flatten(tube)+[0]
                basis = tube[0]
                a = copy(alpha)
                while a != 0:
                    edges = [ x for x in basis if a-x in roots ]
                    sup_a += edges
                    while edges:
                        a = a-edges.pop()
                return tuple(sup_a)
        raise ValueError("Unable to compute support of root")

    @cached_method
    def _tube_nbh(self, alpha):
        sup_a = self._tube_support(alpha)
        nbh_a = [ self.tau_c(x) for x in sup_a if self.tau_c(x) not in sup_a ]
        nbh_a += [ self.tau_c_inverse(x) for x in sup_a if self.tau_c_inverse(x) not in sup_a ]
        nbh_a = Set(nbh_a)
        return tuple(nbh_a)

    @cached_method
    def compatibility_degree(self, alpha, beta):
        if self.is_finite():
            tube_contribution = -1
        elif self.is_affine():
            gck = self.gamma().associated_coroot()
            if any([gck.scalar(alpha) != 0, gck.scalar(beta) != 0]):
                tube_contribution = -1
            else:
                sup_a = self._tube_support(alpha)
                sup_b = self._tube_support(beta)
                if all([x in sup_b for x in sup_a]) or all([x in sup_a for x in sup_b]):
                    tube_contribution = -1
                else:
                    nbh_a = self._tube_nbh(alpha)
                    tube_contribution = len([ x for x in nbh_a if x in sup_b ])
        else:
            raise ValueError("compatibility degree is implemented only for finite and affine types")
        
        initial = self.initial_cluster()
        if alpha in initial:
            return max(beta[initial.index(alpha)],0)

        alphacheck = alpha.associated_coroot()

        if beta in initial:
            return max(alphacheck[initial.index(beta)],0)

        Ap = -matrix(self.rk, map(lambda x: max(x,0), self.b_matrix().list() ) )
        Am =  matrix(self.rk, map(lambda x: min(x,0), self.b_matrix().list() ) )

        a = vector(alphacheck)
        b = vector(beta)

        return max( -a*b-a*Am*b, -a*b-a*Ap*b, tube_contribution )

    @cached_method
    def are_compatible(self, alpha, beta):
        if self.compatibility_degree(alpha, beta) <= 0:
            return True
        return False

    @cached_method
    def are_exchangeable(self, alpha, beta):
        if self.compatibility_degree(alpha, beta) == 1 and self.compatibility_degree(beta, alpha) == 1:
            return True
        return False
    
    @cached_method
    def twisted_sum(self, alpha, beta):
        if not self.are_exchangeable(alpha, beta):
            raise ValueError("The roots are not exchangeable")
        if self.is_affine():
            gck = self.gamma().associated_coroot()
            if alpha.scalar(gck) > 0 or beta.scalar(gck) > 0:
                tau = self.tau_c_inverse
                tau_i = self.tau_c
            elif alpha.scalar(gck) < 0 or beta.scalar(gck) < 0:
                tau = self.tau_c
                tau_i = self.tau_c_inverse
            else:
                sup_a = self._tube_support(alpha)
                nbh_a = self._tube_nbh(alpha)
                sup_b = self._tube_support(beta)
                nbh_b = self._tube_nbh(beta)
                contrib_a = [x for x in sup_a if x not in sup_b + nbh_b]
                contrib_b = [x for x in sup_b if x not in sup_a + nbh_a]
                return sum(contrib_a+contrib_b)
                
        elif self.is_finite():
            tau = self.tau_c
            tau_i = self.tau_c_inverse
        else:
            raise ValueError("Not implemented")
        count = 1
        s1 = tau(alpha+beta)
        ta = tau(alpha)
        tb = tau(beta)
        while s1 == ta + tb:
            count += 1
            s1 = tau(s1)
            ta = tau(ta)
            tb = tau(tb)
        s2 = ta + tb
        for i in range(count):
            s2 = tau_i(s2)
        return s2

    def to_weight(self,x):
        weight_space = self.weight_space()
        Lambda = weight_space.fundamental_weights()
        for i in range(self.rk):
            if x == self.initial_cluster()[i]:
                return Lambda[i]
        x_coeff=vector(x)
        y_coeff = -self.euler_matrix()*x_coeff
        return sum([ Lambda[i]*Integer(y_coeff[i]) for i in range(self.rk) ])

            

##### Reviewed up to here 
    def clusters(self, depth=None):
        r"""
        FIXME: handle error id depth is not set
        """
        if depth == None:
            depth = self._depth
        if self._clusters[0] != depth:

            def compatible_following(l):
                out=[]
                while l:
                    x=l.pop()
                    comp_with_x=[y for y in l if self.compatibility_degree(x,y)==0]
                    if comp_with_x != []:
                        out.append((x,comp_with_x))
                    else:
                        out.append((x,))
                return out

            d_vectors = self.d_vectors(depth=depth)
            clusters = compatible_following(d_vectors)
            done = False
            while not done:
                new = []
                done = True
                for clus in clusters:
                    if type(clus[-1]) == list:
                        done = False
                        for y in compatible_following(clus[-1]):
                            new.append(clus[:-1]+y)
                    else:
                        new.append(clus)
                clusters = copy(new)
            self._clusters = [depth,[ Set(x) for x in  clusters if len(x) == self._n]]

        return copy(self._clusters[1])

    @cached_method
    def cluster_expansion(self, beta):
        if beta == 0:
            return dict()

        coefficients=beta.monomial_coefficients()
        if any ( x < 0 for x in coefficients.values() ):
            alpha = [ -x for x in self.initial_cluster() ]
            negative_part = dict( [(-alpha[x],-coefficients[x]) for x in
                    coefficients if coefficients[x] < 0 ] )
            positive_part = sum( [ coefficients[x]*alpha[x] for x in
                    coefficients if coefficients[x] > 0 ] )
            return dict( negative_part.items() +
                    self.cluster_expansion(positive_part).items() )

        if self.is_affine():
            if self.gamma().associated_coroot().scalar(beta) < 0:
                shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
                return dict( [ (self.tau_c_inverse()(x),shifted_expansion[x]) for x in
                    shifted_expansion ] )
            elif self.gamma().associated_coroot().scalar(beta) > 0:
                shifted_expansion = self.cluster_expansion( self.tau_c_inverse()(beta) )
                return dict( [ (self.tau_c()(x),shifted_expansion[x]) for x in
                    shifted_expansion ] )
            else:
                ###
                # Assumptions
                #
                # Two cases are possible for vectors in the interior of the cone
                # according to how many tubes there are:
                # 1) If there is only one tube then its extremal rays are linearly
                # independent, therefore a point is in the interior of the cone
                # if and only if it is a linear combination of all the extremal
                # rays with strictly positive coefficients. In this case solve()
                # should produce only one solution.
                # 2) If there are two or three tubes then the extreme rays are
                # linearly dependent. A vector is in the interior of the cone if
                # and only if it can be written as a strictly positive linear
                # combination of all the rays of at least one tube. In this case
                # solve() should return at least two solutions.
                #
                # If a vector is on one face of the cone than it can be written
                # uniquely as linear combination of the rays of that face (they
                # are linearly independent). solve() should return only one
                # solution no matter how many tubes there are.

                rays = flatten([ t[0] for t in self.affine_tubes() ])
                system = matrix( map( vector, rays ) ).transpose()
                x = vector( var ( ['x%d'%i for i in range(len(rays))] ) )
                eqs =  [ (system*x)[i] == vector(beta)[i] for i in
                        range(self._n)]
                ieqs = [ y >= 0 for y in x ]
                solutions = solve( eqs+ieqs, x, solution_dict=True )

                if not solutions:
                    # we are outside the cone
                    shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
                    return dict( [ (self.tau_c_inverse()(v),shifted_expansion[v]) for v in
                        shifted_expansion ] )

                if len(solutions) > 1 or all( v > 0 for v in solutions[0].values() ):
                    # we are in the interior of the cone
                    raise ValueError("Vectors in the interior of the cone do "
                        "not have a cluster expansion")

                # we are on the boundary of the cone
                solution_dict=dict( [(rays[i],solutions[0][x[i]]) for i in range(len(rays)) ] )
                tube_bases = [ t[0] for t in self.affine_tubes() ]
                connected_components = []
                index = 0
                for t in tube_bases:
                    component = []
                    for a in t:
                        if solution_dict[a] == 0:
                            if component:
                                connected_components.append( component )
                                component = []
                        else:
                            component.append( (a,solution_dict[a]) )
                    if component:
                        if connected_components:
                            connected_components[index] = ( component +
                                    connected_components[index] )
                        else:
                            connected_components.append( component )
                    index = len(connected_components)
                expansion = dict()
                while connected_components:
                    component = connected_components.pop()
                    c = min( [ a[1] for a in component] )
                    expansion[sum( [a[0] for a in component])] = c
                    component = [ (a[0],a[1]-c) for a in component ]
                    new_component = []
                    for a in component:
                        if a[1] == 0:
                            if new_component:
                                connected_components.append( new_component )
                                new_component = []
                        else:
                            new_component.append( a )
                    if new_component:
                        connected_components.append( new_component )
                return expansion

        if self.is_finite():
            shifted_expansion = self.cluster_expansion( self.tau_c()(beta) )
            return dict( [ (self.tau_c_inverse()(x),shifted_expansion[x]) for x
                in shifted_expansion ] )
               
    def to_g_vector(self,x):
        weight_space = self.weight_space()        
        Lambda = weight_space.fundamental_weights()
        for i in range(self._n):
            if x == self.initial_cluster()[i]:
                return Lambda[i]
        x_coeff=vector(x)
        y_coeff = -self.euler_matrix()*x_coeff 
        return sum([ Lambda[i]*Integer(y_coeff[i]) for i in range(self._n) ])

    def plot2d(self,depth=None):
        # FIXME: refactor this before publishing
        from sage.plot.line import line
        from sage.plot.graphics import Graphics
        if self._n !=2:
            raise ValueError("Can only 2d plot fans.")
        if depth == None:
            depth = self._depth
        if not self.is_finite() and depth==infinity:
            raise ValueError("For infinite algebras you must specify the depth.")

        colors = dict([(0,'red'),(1,'green')])
        G = Graphics()
        for i in range(2):
            orbit = self.ith_orbit(i,depth=depth)
            for j in orbit:
                G += line([(0,0),vector(orbit[j])],color=colors[i],thickness=0.5, zorder=2*j+1)
    
        G.set_aspect_ratio(1)
        G._show_axes = False
        return G

    def plot3d(self,depth=None):
        # FIXME: refactor this before publishing
        from sage.plot.graphics import Graphics
        from sage.plot.point import point
        from sage.misc.flatten import flatten
        from sage.plot.plot3d.shapes2 import sphere
        if self._n !=3:
            raise ValueError("Can only 3d plot fans.")
        if depth == None:
            depth = self._depth
        if not self.is_finite() and depth==infinity:
            raise ValueError("For infinite algebras you must specify the depth.")

        colors = dict([(0,'red'),(1,'green'),(2,'blue'),(3,'cyan')])
        G = Graphics()

        roots = self.d_vectors(depth=depth)
        compatible = []
        while roots:
            x = roots.pop()
            for y in roots:
                if self.compatibility_degree(x,y) == 0:
                    compatible.append((x,y))
        for (u,v) in compatible:
            G += _arc3d((_normalize(vector(u)),_normalize(vector(v))),thickness=0.5,color='black')

        for i in range(3):
            orbit = self.ith_orbit(i,depth=depth)
            for j in orbit:
                G += point(_normalize(vector(orbit[j])),color=colors[i],size=10,zorder=len(G.all))

        if self.is_affine():
            tube_vectors=map(vector,flatten(self.affine_tubes()))
            tube_vectors=map(_normalize,tube_vectors)
            for v in tube_vectors:
                G += point(v,color=colors[3],size=10,zorder=len(G.all))
            G += _arc3d((tube_vectors[0],tube_vectors[1]),thickness=5,color='gray',zorder=0)
        
        G += sphere((0,0,0),opacity=0.1,zorder=0)
        G._extra_kwds['frame']=False
        G._extra_kwds['aspect_ratio']=1 
        return G


    def plot_cluster_fan_stereographically(self, northsign=1, north=None, right=None, colors=None, d_vectors=False):
        from sage.plot.graphics import Graphics
        from sage.plot.point import point
        from sage.misc.flatten import flatten
        from sage.plot.line import line
        from sage.misc.functional import norm

        if self.rk !=3:
            raise ValueError("Can only stereographically project fans in 3d.")
        if not self.is_finite() and self._depth == infinity:
            raise ValueError("For infinite algebras you must specify the depth.")

        if north == None:
            if self.is_affine():
                north = vector(self.delta())
            else:
                north = vector( (-1,-1,-1) )
        if right == None:
            if self.is_affine():
                right = vector(self.gamma())
            else:
                right = vector( (1,0,0) )
        if colors == None:
            colors = dict([(0,'red'),(1,'green'),(2,'blue'),(3,'cyan'),(4,'yellow')])
        G = Graphics()

        roots = list(self.g_vectors())
        compatible = []
        while roots:
            x = roots.pop()
            if x in self.initial_cluster() and d_vectors:
                x1 = -self.simple_roots()[list(self.initial_cluster()).index(x)]
            else:
                x1 = x
            for y in roots:
                if self.compatibility_degree(x,y) == 0:
                    if y in self.initial_cluster() and d_vectors:
                        y1 = -self.simple_roots()[list(self.initial_cluster()).index(y)]
                    else:
                        y1 = y
                    compatible.append((x1,y1))
        for (u,v) in compatible:
            G += _stereo_arc(vector(u),vector(v),vector(u+v),north=northsign*north,right=right,thickness=0.5,color='black')

        for i in range(3):
            orbit = self.ith_orbit(i)
            if d_vectors: 
                orbit[0] = -self.simple_roots()[list(self.initial_cluster()).index(orbit[0])]
            for j in orbit:
                G += point(_stereo_coordinates(vector(orbit[j]),north=northsign*north,right=right),color=colors[i],zorder=len(G))

        if self.is_affine():
            tube_vectors = map(vector,flatten(self.affine_tubes()))
            for v in tube_vectors:
                G += point(_stereo_coordinates(v,north=northsign*north,right=right),color=colors[3],zorder=len(G))
            if north != vector(self.delta()):
                G += _stereo_arc(tube_vectors[0],tube_vectors[1],vector(self.delta()),north=northsign*north,right=right,thickness=2,color=colors[4],zorder=0)
            else:
                # FIXME: refactor this before publishing
                tube_projections = [
                        _stereo_coordinates(v,north=northsign*north,right=right)
                        for v in tube_vectors ]
                t=min((G.get_minmax_data()['xmax'],G.get_minmax_data()['ymax']))
                G += line([tube_projections[0],tube_projections[0]+t*(_normalize(tube_projections[0]-tube_projections[1]))],thickness=2,color=colors[4],zorder=0)
                G += line([tube_projections[1],tube_projections[1]+t*(_normalize(tube_projections[1]-tube_projections[0]))],thickness=2,color=colors[4],zorder=0)
        G.set_aspect_ratio(1)
        G._show_axes = False
        return G


#####
# Helper functions
#####
def _stereo_coordinates(x, north=(1,0,0), right=(0,1,0), translation=-1):
    r"""
    Project stereographically points from a sphere
    """
    from sage.misc.functional import norm
    north=_normalize(north)
    right=vector(right)
    right=_normalize(right-(right*north)*north)
    if norm(right) == 0:
        raise ValueError ("Right must not be linearly dependent from north")
    top=north.cross_product(right)
    x=_normalize(x)
    p=(translation-north*x)/(1-north*x)*(north-x)+x
    return vector((right*p, top*p ))

def _normalize(x):
    r"""
    make x of length 1
    """
    from sage.misc.functional import norm
    x=vector(x)
    if norm(x) == 0:
        return x
    return vector(x/norm(x))

#def _stereo_arc(x,y, xy=None,  north=(1,0,0), right=(0,1,0), translation=-1, **kwds):
#    from sage.misc.functional import norm, det, n
#    from sage.plot.line import line
#    from sage.plot.plot import parametric_plot
#    from sage.functions.trig import arccos, cos, sin
#    from sage.symbolic.constants import NaN
#    from sage.calculus.var import var
#    x=vector(x)
#    y=vector(y)
#    sx=n(_stereo_coordinates(x, north=north, right=right, translation=translation))
#    sy=n(_stereo_coordinates(y, north=north, right=right, translation=translation))
#    if xy == None:
#        sxy=n(_stereo_coordinates(x+y, north=north, right=right, translation=translation))
#    else:
#        sxy=n(_stereo_coordinates(xy, north=north, right=right, translation=translation))
#    m0=-matrix(3,[sx[0]**2+sx[1]**2, sx[1], 1, sy[0]**2+sy[1]**2, sy[1], 1,
#                 sxy[0]**2+sxy[1]**2, sxy[1], 1])
#    m1=matrix(3,[sx[0]**2+sx[1]**2, sx[0], 1, sy[0]**2+sy[1]**2, sy[0], 1,
#                 sxy[0]**2+sxy[1]**2, sxy[0], 1])
#    m2=matrix(3,[sx[0], sx[1], 1, sy[0], sy[1], 1, sxy[0], sxy[1], 1])
#    d=det(m2)*2
#    if d == 0:
#        return line([sx,sy], **kwds)
#    center=vector((-det(m0)/d,-det(m1)/d))
#    if det(matrix(2,list(sx-center)+list(sy-center)))==0:
#        return line([sx,sy], **kwds)
#    radius=norm(sx-center)
#    e1=_normalize(sx-center)
#    v2=_normalize(sy-center)
#    vxy=_normalize(sxy-center)
#    e2=_normalize(vxy-(vxy*e1)*e1)
#    angle=arccos(e1*vxy)+arccos(vxy*v2)
#    if angle < 0.1 or angle==NaN:
#        return line([sx,sy], **kwds)
#    var('t')
#    p=center+radius*cos(t)*e1+radius*sin(t)*e2
#    return parametric_plot( p, (t, 0, angle), **kwds)

def _arc3d((first_point,second_point),center=(0,0,0),**kwds):
    # FIXME: refactor this before publishing
    r"""
    Usese parametric_plot3d() to plot arcs of a circle.
    We only plot arcs spanning algles strictly less than pi.
    """
    # For sanity purposes convert the input to vectors
    from sage.misc.functional import norm
    from sage.modules.free_module_element import vector
    from sage.functions.trig import arccos, cos, sin 
    from sage.plot.plot3d.parametric_plot3d import parametric_plot3d
    center=vector(center)
    first_point=vector(first_point)
    second_point=vector(second_point)
    first_vector=first_point-center
    second_vector=second_point-center
    radius=norm(first_vector)
    if norm(second_vector)!=radius:
        raise ValueError("Ellipse not implemented")
    first_unit_vector=first_vector/radius
    second_unit_vector=second_vector/radius
    normal_vector=second_vector-(second_vector*first_unit_vector)*first_unit_vector
    if norm(normal_vector)==0:
        print (first_point,second_point)
        return 
    normal_unit_vector=normal_vector/norm(normal_vector)
    scalar_product=first_unit_vector*second_unit_vector
    if abs(scalar_product) == 1:
        raise ValueError("The points are alligned")
    angle=arccos(scalar_product)
    var('t')
    return parametric_plot3d(center+first_vector*cos(t)+radius*normal_unit_vector*sin(t),(0,angle),**kwds)


def _arc(p,q,s,**kwds):
    #rewrite this to use polar_plot and get points to do filled triangles
    from sage.misc.functional import det
    from sage.plot.line import line
    from sage.misc.functional import norm
    from sage.symbolic.all import pi
    from sage.plot.arc import arc

    p,q,s = map( lambda x: vector(x), [p,q,s])

    # to avoid running into division by 0 we set to be colinear vectors that are
    # almost colinear
    if abs(det(matrix([p-s,q-s])))<0.01:
        return line((p,q),**kwds)

    (cx,cy)=var('cx','cy')
    equations=[
            2*cx*(s[0]-p[0])+2*cy*(s[1]-p[1]) == s[0]**2+s[1]**2-p[0]**2-p[1]**2,
            2*cx*(s[0]-q[0])+2*cy*(s[1]-q[1]) == s[0]**2+s[1]**2-q[0]**2-q[1]**2
            ]
    c = vector( [solve( equations, (cx,cy), solution_dict=True )[0][i] for i in [cx,cy]] )
    
    r = norm(p-c)

    a_p, a_q, a_s = map(lambda x: atan2(x[1],x[0]), [p-c,q-c,s-c])
    a_p, a_q = sorted([a_p,a_q])
    if a_s < a_p or a_s > a_q:
        return arc( c, r, angle=a_q, sector=(0,2*pi-a_q+a_p), **kwds)
    return arc( c, r, angle=a_p, sector=(0,a_q-a_p), **kwds)

def _stereo_arc(x,y, xy=None,  north=(1,0,0), right=(0,1,0), translation=-1, **kwds):
    from sage.misc.functional import n
    x=vector(x)
    y=vector(y)
    sx=n(_stereo_coordinates(x, north=north, right=right, translation=translation))
    sy=n(_stereo_coordinates(y, north=north, right=right, translation=translation))
    if xy == None:
        xy=x+y
    sxy=n(_stereo_coordinates(xy, north=north, right=right, translation=translation))
    return _arc(sx,sy,sxy,**kwds)
