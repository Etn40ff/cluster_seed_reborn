class SidestWeightMinor(SageObject):

    def __init__(self, data, coxeter=None, mutation_type=None):
        data = copy(data)

        if isinstance(data, type(Matrix())):
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
        self._alpha = self._RootSystem._simple_roots
        self._coxeter = prod([self._RootSystem._simple_reflections[i] for i in self._coxeter_word])

        self._parameter_polynomial_ring = PolynomialRing(QQ,['t%s'%i for i in xrange(self._rank)]+['u%s'%i for i in xrange(self._rank)])
        self._polygens = self._parameter_polynomial_ring.gens()

        cox_rev = [i+1 for i in self._coxeter_word]
        self._double_coxeter = [-i for i in cox_rev]
        cox_rev.reverse()
        self._double_coxeter += cox_rev

        extended_B = block_matrix([[self._B],[identity_matrix(self._rank)]])
        self._cluster_algebra = ClusterAlgebra(extended_B)

        temp_coeff = []
        self._w = self._RootSystem._fundamental_weights
        for i in xrange(self._rank):
            coeff = self.generic_evaluation(self._double_coxeter,self._coxeter*self._w[i],self._w[i])
            temp_coeff.append(coeff)
            #print coeff

        self._coefficients = []
        for j in xrange(self._rank):
            coeff = temp_coeff[j]
            for i in self._coxeter_word:
                if i == j:
                    break
                else:
                    coeff *= temp_coeff[i]**self._Cartan_mat[i,j]
            self._coefficients.append(coeff)
            #print self._coefficients

        clgens = self._cluster_algebra.ambient().gens()
        self._initial_cluster = dict([(clgens[i],self._polygens[self._rank+i]**(-1)) for i in xrange(self._rank)]+[(clgens[self._rank+i],self._coefficients[i]) for i in xrange(self._rank)])
    

    def diff_root(self,wt1,wt2):
        """
        Input: A pair of weights
        Output: Their difference wt1-wt2 written as an element of the root lattice if possible, error otherwise.
        """
        if all(wt1[i]==wt2[i] for i in xrange(self._rank)):
            return wt1-wt2
        elif self._Cartan_mat.is_invertible():
            raise NotImplementedError("This should be possible and easy.")
        else:
            raise NotImplementedError("This will be more work.")


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
            start_wt = wt1+j*alpha
            if sub > 0:
                output += self.generic_evaluation(working_list,start_wt,wt2,bad_flag)*self._polygens[sub-1]**j
            else:
                output += self.generic_evaluation(working_list,start_wt,wt2,bad_flag)*self._polygens[self._rank-sub-1]**(pairing+j)
        return output

    def generic_evaluation2(self, xlist, wt1, convex=None, wt2=None):
        if convex == None:
            W = list(self._RootSystem.get_Weyl_Group())
            orbit = [ g*wt1 for g in W ]
            convex = Polyhedron(vertices=orbit).integral_points()
        if wt2 == None:
            wt2 = copy(wt1)
        if xlist == []:
            if wt1 == wt2:
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
        j = 0
        while wt1+j*alpha in convex:
            start_wt = wt1+j*alpha
            if sub > 0:
                output += self.generic_evaluation2(working_list,start_wt,convex=convex,wt2=wt2)*self._polygens[sub-1]**j
            else:
                output += self.generic_evaluation2(working_list,start_wt,convex=convex,wt2=wt2)*self._polygens[self._rank-sub-1]**(pairing+j)
            j += 1
        return output

    def affine_weight_multiplicity(self, highest_wt, wt):
        # return multiplicity of wt in level zero representation indexed by dominant finite-type highest_wt

    def validate_weight(self, highest_wt, alpha, wt, pairing):
        # check whether there is an ambiguity in the next step of generic_evaluation
        if pairing >= 0:
            outward_alpha = alpha
        else:
            outward_alpha = -alpha
        current_wt = copy(wt)
        current_wt_mult = self.affine_weight_multiplicity(highest_wt, current_wt)
        initial_wt_mult = current_wt_mult
        while current_wt_mult != 0:
            if current_wt_mult < initial_wt_mult:
                print "There was an ambiguity"
                break
            current_wt += outward_alpha
            current_wt_mult = self.affine_weight_multiplicity(highest_wt, current_wt)            

    def level_zero_dominant_conjugate(self, wt):
        # return the dominant Weyl conjugate weight of wt

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
        sub = new_xlist.pop()
        if sub > 0:
            alpha = self._RootSystem._simple_roots[sub-1]
        else:
            alpha = -self._RootSystem._simple_roots[-sub-1]
        pairing = self._RootSystem.pairing(alpha, wt1)
        self.validate_weight(highest_wt, alpha, wt1, pairing)
        output = 0
        j = 0
        while self.affine_weight_multiplicity(wt1 + j*alpha) != 0:
            new_wt1 = wt1 + j*alpha
            if sub > 0:
                output += self.generic_evaluation3(new_xlist, new_wt1, wt2, highest_wt) * self._polygens[sub-1]**j
            else:
                output += self.generic_evaluation3(new_xlist, new_wt1, wt2, highest_wt) * self._polygens[self._rank-sub-1]**(pairing + j)
            j += 1
        return output

    def compare_constructions(self,glist):
        """
        Input: A list of g-vectors
        Output: A comparison of the cluster variables with these g-vectors (evaluated in the parameter ring) and the corresponding
                sidest weight minors evaluated at a generic point of the reduced double Bruhat cell
        """
        for gvect in glist:
            self._cluster_algebra.find_cluster_variable(gvect)
            cl_minor = self._cluster_algebra.cluster_variable(gvect).lift().subs(self._initial_cluster)
            gen_minor = self.generic_evaluation(self._double_coxeter,self.g_to_weight(gvect))
            if cl_minor == gen_minor:
                print str(gvect)+": True"
            else:
                print str(gvect)+": False"
                #print "  Cluster minor=",cl_minor
                #print "  Generalized minor=",gen_minor
                print "  Diff=",cl_minor-gen_minor

    def compare_constructions2(self,glist):
        """
        Input: A list of g-vectors
        Output: A comparison of the cluster variables with these g-vectors (evaluated in the parameter ring) and the corresponding
                sidest weight minors evaluated at a generic point of the reduced double Bruhat cell
        """
        for gvect in glist:
            self._cluster_algebra.find_cluster_variable(gvect)
            cl_minor = self._cluster_algebra.cluster_variable(gvect).lift().subs(self._initial_cluster)
            gen_minor = self.generic_evaluation2(self._double_coxeter,self.g_to_weight(gvect))
            if cl_minor == gen_minor:
                print str(gvect)+": True"
            else:
                print str(gvect)+": False"
                #print "  Cluster minor=",cl_minor
                #print "  Generalized minor=",gen_minor
                print "  Diff=",cl_minor-gen_minor

