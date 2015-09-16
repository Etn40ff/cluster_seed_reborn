class LevelZeroMinor(SageObject):

    def __init__(self, b_matrix):
        """
        We assume that b_matrix is an orientation of an affine Dynkin diagram,
        and that the first column is the affine root.
        """

        if not b_matrix.is_skew_symmetrizable():
            raise ValueError("The input must be a skew symmetrizable integer matrix")
        self._B = copy(b_matrix)
        self._rank = self._B.ncols()
        self._ext_Cartan_mat = block_diagonal_matrix(2-matrix(self._rank,map(abs,self._B.list())),matrix(1))
        self._ext_Cartan_mat[0,self._rank] = 1
        self._ext_Cartan_mat[self._rank,0] = 1
        self._coxeter_word = self.coxeter()

        self._ext_symm_mat = diagonal_matrix(self._ext_Cartan_mat.is_symmetrizable(return_diag=True))
        self._ext_symm_mat *= self._ext_symm_mat.denominator()
        self._RootSystem = RootSystem(self._rank+1,self._ext_Cartan_mat,self._ext_symm_mat)
        self._coxeter_element = prod([self._RootSystem._simple_reflections[i] for i in self._coxeter_word])

        self._parameter_polynomial_ring = PolynomialRing(QQ,['t%s'%i for i in xrange(self._rank)]+['u%s'%i for i in xrange(self._rank)])
        self._polygens = self._parameter_polynomial_ring.gens()

        self._double_coxeter = [(i,-1) for i in self._coxeter_word]
        cv = list(self._coxeter_word)
        cv.reverse()
        self._double_coxeter += [(i,1) for i in cv]

        # create cluster algebra with principal coefficients
        self._cluster_algebra = ClusterAlgebra(block_matrix([[self._B],[identity_matrix(self._rank)]]))

        temp_coeff = []
        for i in xrange(self._rank):
            # next two lines depend on the implementation of weights by RootSystem
            root = self._RootSystem._fundamental_weights[i]-self._coxeter_element*self._RootSystem._fundamental_weights[i]
            coeff = self._polygens[self._rank+i]**(-1)*prod([self._polygens[j]**root[self._rank+1+j] for j in xrange(self._rank)]) 
            temp_coeff.append(coeff)

        self._coefficients = []
        for j in xrange(self._rank):
            coeff = temp_coeff[j]
            for i in self._coxeter_word:
                if i == j:
                    break
                else:
                    coeff *= temp_coeff[i]**self._ext_Cartan_mat[i,j]
            self._coefficients.append(coeff)

        clgens = self._cluster_algebra.ambient().gens()
        self._initial_cluster = dict([(clgens[i],self._polygens[self._rank+i]**(-1)) for i in xrange(self._rank)]+[(clgens[self._rank+i],self._coefficients[i]) for i in xrange(self._rank)])

    def coxeter(self):
        r"""
        Returns a list expressing the coxeter element corresponding to self._B
        (twisted) reflections are applied from top of the list, for example
        [2, 1, 0] correspond to s_2s_1s_0

        Sources == non positive columns == leftmost letters
        """
        zero_vector = vector([0 for x in range(self._rank)])
        coxeter = []
        B = copy(self._B)
        columns = B.columns()
        source = None
        for j in range(self._rank):
            for i in range(self._rank):
                if all(x <=0 for x in columns[i]) and columns[i] != zero_vector:
                    source = i
                    break
            if source == None:
                if B != matrix(self._rank):
                    raise ValueError("Unable to find a Coxeter element representing self._B")
                coxeter += [ x for x in range(self._rank) if x not in coxeter]
                break
            coxeter.append(source)
            columns[source] = zero_vector
            B = matrix(columns).transpose()
            B[source] = zero_vector
            columns = B.columns()
            source = None
        return tuple(coxeter)

    def affine_weight_multiplicity(self, highest_wt, wt):
        # return multiplicity of wt in level zero representation indexed by dominant finite-type highest_wt
        pass

    def validate_weight(self, xlist, wt1, wt2, highest_wt, alpha, pairing):
        # check whether there is an ambiguity in the next step of generic_evaluation
        if pairing >= 0:
            outward_alpha = alpha
        else:
            outward_alpha = -alpha
        current_wt = copy(wt1)
        current_wt_mult = self.affine_weight_multiplicity(highest_wt, current_wt)
        initial_wt_mult = current_wt_mult
        while current_wt_mult != 0:
            if current_wt_mult < initial_wt_mult:
                print "There was an ambiguity."
                print "initial_wt_mult = ", initial_wt_mult
                print "current_wt_mult = ", current_wt_mult
                print "current_wt = ", current_wt
                print "alpha = ", alpha
                print "xlist = ", xlist
                print "wt1 = ", wt1
                print "wt2 = ", wt2
            current_wt += outward_alpha
            current_wt_mult = self.affine_weight_multiplicity(highest_wt, current_wt)

    def level_zero_dominant_conjugate(self, wt):
        # return the dominant Weyl conjugate weight of wt
        pass

    def generic_evaluation3(self, xlist, wt1, wt2 = None, highest_wt = None):
        if highest_wt == None:
            highest_wt = level_zero_dominant_conjugate(wt1)
        if wt2 == None:
            wt2 = copy(wt1)
        if xlist == []:
            if wt1 == wt2:
                return 1
            else:
                return 0
        new_xlist = copy(xlist)
        i, eps = new_xlist.pop()
        alpha = eps * self._RootSystem._simple_roots[i]
        pairing = self._RootSystem.pairing(alpha, wt1)
        self.validate_weight(highest_wt, alpha, wt1, pairing)
        output = 0
        j = 0
        new_wt1 = copy(wt1)
        while self.affine_weight_multiplicity(new_wt1) != 0:
            if eps > 0:
                # this records the action of the matrix [[1,t],[0,1]]
                output += self.generic_evaluation3(new_xlist, new_wt1, wt2, highest_wt) * self._polygens[i]**j
            else:
                # this records the action of the matrix [[u^{-1},0],[1,u]] = [[1,0],[u,1]]*[[u^{-1},0],[0,u]]
                output += self.generic_evaluation3(new_xlist, new_wt1, wt2, highest_wt) * self._polygens[self._rank + i]**(pairing + j)
            j += 1
            new_wt1 += alpha
        return output

