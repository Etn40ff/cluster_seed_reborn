import time
from sage.matrix.matrix import Matrix

class ClusterSeed2(SageObject):
    
    def __init__(self, data):
        if isinstance(data, Matrix):
            self._B0 = copy(data) #needed for cluster variables
            self._m = self._B0.nrows() #needed for cluster variables
            self._n = self._B0.ncols()
            self._B = copy(self._B0[:self._n,:self._n])
            if not self._B.is_skew_symmetrizable(positive=True):
                raise ValueError('data must have skew-symmetrizable principal part.')
            self._C = identity_matrix(self._n)
            self._G = identity_matrix(self._n)
            self._U = PolynomialRing(QQ,['u%s'%i for i in xrange(self._n)])
            self._F = dict([ (i,self._U(1)) for i in xrange(self._n) ])
            self._F_dict = dict([ (tuple(self._G.column(i)),self._U(1)) for i in xrange(self._n) ])
            self._R = PolynomialRing(QQ,['x%s'%i for i in xrange(self._m)]) #needed for cluster variables
            self._y = dict([ (self._U.gen(j),prod([self._R.gen(i)**self._B0[i,j] for i in xrange(self._n,self._m)])) for j in xrange(self._n)]) #needed for cluster variables
            self._yhat = dict([ (self._U.gen(j),prod([self._R.gen(i)**self._B0[i,j] for i in xrange(self._m)])) for j in xrange(self._n)]) #needed for cluster variables
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
        other._F_dict = self._F_dict
        other._R = copy(self._R)
        return other

    
    def mutate(self, sequence, inplace=True, mutating_F=True):
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

            # F-polynomials
            if mutating_F:
                gvect = tuple(seed._G.column(k))
                if not self._F_dict.has_key(gvect):
                    self._F_dict.setdefault(gvect,self._mutated_F(k))
                seed._F[k] = self._F_dict[gvect]
            
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


    def _mutated_F(self, k):
        pos = self._U(1)
        neg = self._U(1)
        for j in xrange(self._n):
            if self._C[j,k] > 0:
                pos *= self._U.gen(j)**self._C[j,k]
            else:
                neg *= self._U.gen(j)**(-self._C[j,k])
            if self._B[j,k] > 0:
                pos *= self._F[j]**self._B[j,k]
            else:
                neg *= self._F[j]**(-self._B[j,k])
        return (pos+neg)//self._F[k]


    def mutation_class_iter(self, depth=infinity, show_depth=False, return_paths=False, up_to_equivalence=True, only_sink_source=False ):
        depth_counter = 0
        n = self._n
        timer = time.time()
        if return_paths:
            yield (self,[])
        else:
            yield self
        if up_to_equivalence:
            cl = Set(self._G.columns())
        else:
            cl = tuple(self._G.columns())
        clusters = {}
        clusters[ cl ] = [ self, range(n), [] ]
        gets_bigger = True
        if show_depth:
            timer2 = time.time()
            dc = str(depth_counter)
            dc += ' ' * (5-len(dc))
            nr = str(len(clusters))
            nr += ' ' * (10-len(nr))
            print "Depth: %s found: %s Time: %.2f s"%(dc,nr,timer2-timer)
        while gets_bigger and depth_counter < depth:
            gets_bigger = False
            keys = clusters.keys()
            for key in keys:
                sd = clusters[key]
                while sd[1]:
                    i = sd[1].pop()
                    if not only_sink_source or all( entry >= 0 for entry in sd[0]._B.row( i ) ) or all( entry <= 0 for entry in sd[0]._B.row( i ) ):
                        sd2  = sd[0].mutate( i, inplace=False )
                        if up_to_equivalence:
                            cl2 = Set(sd2._G.columns())
                        else:
                            cl2 = tuple(sd2._G.columns())
                        if cl2 in clusters:
                            if not up_to_equivalence and i in clusters[cl2][1]:
                                clusters[cl2][1].remove(i)
                        else:
                            gets_bigger = True
                            if only_sink_source:
                                orbits = range(n)
                            else:
                                orbits = [ index for index in xrange(n) if index > i or sd2._B[index,i] != 0 ]

                            clusters[ cl2 ] = [ sd2, orbits, clusters[key][2]+[i] ]
                            if return_paths:
                                yield (sd2,clusters[cl2][2])
                            else:
                                yield sd2
            depth_counter += 1
            if show_depth and gets_bigger:
                timer2 = time.time()
                dc = str(depth_counter)
                dc += ' ' * (5-len(dc))
                nr = str(len(clusters))
                nr += ' ' * (10-len(nr))
                print "Depth: %s found: %s Time: %.2f s"%(dc,nr,timer2-timer)


    def cluster_variable(self, k):
        if k in range(self._n):
            g_mon = prod([self._R.gen(i)**self._G[i,k] for i in xrange(self._n)])
            F_std = self._F[k].subs(self._yhat)
            F_trop = self._F[k].subs(self._y).denominator()
            return g_mon*F_std*F_trop
        if isinstance(k,tuple) and k in self._F_dict.keys():
            g_mon = prod([self._R.gen(i)**k[i] for i in xrange(self._n)])
            F_std = self._F_dict[k].subs(self._yhat)
            F_trop = self._F_dict[k].subs(self._y).denominator()
            return g_mon*F_std*F_trop

        

         
