class SidestWeightMinor(SageObject):

    def __init__(self, data, coxeter=None, mutation_type=None):
        data = copy(data)

        if isinstance(data, Matrix):
            if not data.is_skew_symmetrizable():
                raise ValueError("The input must be a skew symmetrizable integer matrix")
            self._B = data
            self._rank = self._B.ncols()
            self._Cartan_mat = 2-matrix(self._rank,map(abs,self._B.list()))
            self._coxeter_word = self.coxeter()
        
        elif isinstance(data, CartanType_abstract):
            self._rank = data.rank()
            
            if Set(data.index_set()) != Set(range(self._rank)):
                relabelling = dict(zip(data.index_set(),range(self._rank)))
                data = data.relabel(relabelling)

            self._Cartan_mat = data.cartan_matrix()
            
            if coxeter==None:
                coxeter = range(self._rank)
            if Set(coxeter) != Set(data.index_set()):
                raise ValueError("The Coxeter element need to be a list permuting the entries of the index set of the Cartan type")
            self._coxeter_word.set_cache(copy(coxeter))
            self._B = 2-self._Cartan_mat

            for i in range(self._rank):
                for j in range(i,self._rank):
                    a = coxeter[j]
                    b = coxeter[i]
                    self._B[a,b] = -self._B[a,b]

        elif type(data) in [QuiverMutationType_Irreducible, QuiverMutationType_Reducible]:
            self.__init__(data.b_matrix(),mutation_type=data, depth=depth)

        elif type(data)==list:
            self.__init__(CartanType(data), coxeter=coxeter, depth=depth)
        
        else:
            raise ValueError("Input is not valid")

        self._symm_mat = diagonal_matrix(self._B.is_skew_symmetrizable(return_diag=True))
        self._RootSystem = RootSystem(self._rank,self._Cartan_mat,self._symm_mat)
        self._coxeter = prod([self._RootSystem._simple_reflections[i] for i in self._coxeter_word])

        self._parameter_polynomial_ring = PolynomialRing(QQ,['t%s'%i for i in xrange(self._rank)]+['u%s'%i for i in xrange(self._rank)])
        self._polygens = self._parameter_polynomial_ring.gens()

        cox_rev = [i+1 for i in self._coxeter_word]
        self._double_coxeter = [-i for i in cox_rev]
        cox_rev.reverse()
        self._double_coxeter += cox_rev

        extended_B = block_matrix([[self._B],[identity_matrix(self._rank)]])
        self._cluster_seed = ClusterSeed2(extended_B)
        self._salvo_cluster = TropicalClusterAlgebra(self._B)
        self._regular_glist = flatten(self._salvo_cluster.affine_tubes())
        self._regular_glist = map(lambda x: tuple(vector(self._salvo_cluster.to_weight(x))), self._regular_glist)

        temp_coeff = []
        self._w = self._RootSystem._fundamental_weights
        for i in xrange(self._rank):
            coeff = self.generic_evaluation(self._double_coxeter,self._coxeter*self._w[i],self._w[i])
            temp_coeff.append(coeff)

        self._coefficients = []
        for j in xrange(self._rank):
            coeff = temp_coeff[j]
            for i in self._coxeter_word:
                if i == j:
                    break
                else:
                    coeff *= temp_coeff[i]**self._Cartan_mat[i,j]
            self._coefficients.append(coeff)

        clgens = self._cluster_seed._R.gens()
        self._initial_cluster = dict([(clgens[i],self._polygens[self._rank+i]**(-1)) for i in xrange(self._rank)]+[(clgens[self._rank+i],self._coefficients[i]) for i in xrange(self._rank)])
    

    def g_to_weight(self,gvect):
        return sum([gvect[i]*self._w[i] for i in xrange(self._rank)])


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


    def generic_evaluation(self,xlist,wt1,wt2=None,bad_flag=False):
        if wt2 == None:
            wt2 = copy(wt1)
        if xlist == []:
            if wt1 == wt2:
                if bad_flag:
                    print "You are probably about to fall into a trap.  The non-extremal vectors are coming!"
                return 1
            else:
                return 0
        working_list = copy(xlist)
        sub = working_list.pop()
        if sub > 0:
            alpha = self._RootSystem._simple_roots[sub-1]
        else:
            alpha = -self._RootSystem._simple_roots[-sub-1]
        output = 0
        pairing = self._RootSystem.pairing(alpha,wt1)
        if (sub > 0 and -pairing > 1) or (sub < 0 and pairing > 1):
            bad_flag = True
            #print "You are probably about to fall into a trap.  The non-extremal vectors are coming!"
            #print "weight=",self._RootSystem.weightify(wt1)
            #print "root=",alpha
            #print "pairing=",pairing
        for j in xrange(max(-pairing+1,1)):
            if sub > 0:
                output += self.generic_evaluation(working_list,wt1+j*alpha,wt2,bad_flag)*self._polygens[sub-1]**j
            else:
                output += self.generic_evaluation(working_list,wt1+j*alpha,wt2,bad_flag)*self._polygens[self._rank-sub-1]**(pairing+j)
        return output


    def compare_constructions(self,glist):
        """
        Input: A list of g-vectors
        Output: A comparison of the cluster variables with these g-vectors (evaluated in the parameter ring) and the corresponding
                sidest weight minors evaluated at a generic point of the reduced double Bruhat cell
        """
        self._cluster_seed.find_cluster_variables(glist_tofind=glist)
        for gvect in glist:
            cl_minor = self._cluster_seed.cluster_variable(gvect).subs(self._initial_cluster)
            gen_minor = self.generic_evaluation(self._double_coxeter,self.g_to_weight(gvect))
            if cl_minor == gen_minor:
                print str(gvect)+": True"
            else:
                print str(gvect)+": False"
                #print "  Cluster minor=",cl_minor
                #print "  Generalized minor=",gen_minor
                print "  Diff=",cl_minor-gen_minor








#def psi(self,i,eps):
#    alpha = self.RootSystem.simple_root[i]
#    if eps > 0:
#        for j in xrange(i):
#            alpha = self.RootSystem.simple_reflections[c[i-1-j]]*alpha
#        return alpha
#    else:
#        for j in xrange(i+1,self._rank+1):
#            alpha = self.RootSystem.simple_reflections[c[j]]*alpha
#        return alpha