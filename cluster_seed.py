from sage.matrix.matrix import Matrix     

class ClusterSeed2(SageObject):
    
    def __init__(self, data):
        if isinstance(data, Matrix):
            self._B0 = copy(data)
            self._n = self._B0.ncols()
            self._m = self._B0.nrows()
            self._B = copy(self._B0[:self._n,:self._n])
            if not self._B.is_skew_symmetrizable(positive=True):
                raise ValueError('data must have skew-symmetrizable principal part.')
            self._C = identity_matrix(self._n)
            self._G = identity_matrix(self._n)
            self._U = PolynomialRing(QQ,['u%s'%i for i in xrange(self._n)])
            self._F = dict([ (i,self._U(1)) for i in xrange(self._n) ])
            self._R = PolynomialRing(QQ,['x%s'%i for i in xrange(self._m)])
            self._y = dict([ (self._U.gen(j),prod([self._R.gen(i)**self._B0[i,j] for i in xrange(self._n,self._m)])) for j in xrange(self._n)])
            self._yhat = dict([ (self._U.gen(j),prod([self._R.gen(i)**self._B0[i,j] for i in xrange(self._m)])) for j in xrange(self._n)])
        # at the moment we only deal with b_matrices
        else:
            raise NotImplementedError('At the moment we only deal with matrices.')

    def __copy__(self):
        other = type(self).__new__(type(self))
        other._B0 = copy(self._B0)
        other._n = self._n
        other._m = self._m
        other._B = copy(self._B)
        other._C = copy(self._C)
        other._G = copy(self._G)
        other._U = copy(self._U)
        other._F = copy(self._F)
        other._R = copy(self._R)
        return other
    
    def mutate(self, sequence, inplace=True):
        if not isinstance(inplace, bool):
            raise ValueError('inplace must be boolean.')
        if inplace:
            seed = self
        else:
            seed = copy(self)
            
        if sequence in xrange(seed._n):
            seq = iter([sequence])
        else:
            seq = iter(sequence)
            
        for k in seq:
            if k not in xrange(seed._n):
                raise ValueError('Cannot mutate in direction' + str(k) + '.')
            
            # F-polynomials
            pos = seed._U(1)
            neg = seed._U(1)
            for j in xrange(seed._n):
                if seed._C[j,k] > 0:
                    pos *= seed._U.gen(j)**seed._C[j,k]
                else:
                    neg *= seed._U.gen(j)**(-seed._C[j,k])
                if seed._B[j,k] > 0:
                    pos *= seed._F[j]**seed._B[j,k]
                else:
                    neg *= seed._F[j]**(-seed._B[j,k])
            # can the following be improved?
            seed._F[k] = (pos+neg)//seed._F[k]

            # G-matrix
            J = identity_matrix(seed._n)
            if any(x > 0 for x in seed._C.column(k)):
                eps = +1
            else:
                eps = -1
            for j in xrange(seed._n):
                J[j,k] += max(0, -eps*seed._B[j,k])
            J[k,k] = -1
            seed._G = seed._G*J
            
            # C-matrix
            J = identity_matrix(seed._n)
            if any(x > 0 for x in seed._C.column(k)):
                eps = +1
            else:
                eps = -1
            for j in xrange(seed._n):
                J[k,j] += max(0, eps*seed._B[k,j])
            J[k,k] = -1
            seed._C = seed._C*J
            
            # B-matrix
            seed._B.mutate(k)
            
        if not inplace:
            return seed

    def cluster_variable(self, k):
        g_mon = prod([self._R.gen(i)**self._G[i,k] for i in xrange(self._n)])
        F_num = self._F[k].subs(self._yhat)
        F_den = self._F[k].subs(self._y).denominator()


         
