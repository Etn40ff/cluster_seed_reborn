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
            root = self._RootSystem._fundamental_weights[i]-self._coxeter_element*self._RootSystem._fundamental_weights[i]
            coeff = self._polygens[self._rank+i]**(-1)*prod([self._polygens[j]**root[self._rank+1+j] for j in xrange(self._rank)]) 
            temp_coeff.append(coeff)
            print coeff

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
