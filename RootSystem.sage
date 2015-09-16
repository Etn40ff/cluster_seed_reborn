class RootSystem(SageObject):
    """
    The root system associated to a symmetrizable Cartan matrix, following the setup given in [Berenstein-Rupel, Section 4].
    
    Attributes:
        ._ambient_space
        ._cartan_matrix
        ._coroot_lattice
        ._fundamental_weights
        ._rank
        ._root_lattice
        ._simple_reflections
        ._simple_roots
        ._simple_coroots
        ._symmetrizing_matrix
        ._symmetric_cartan_matrix
        ._weight_lattice
        ._Weyl_group
        ._zero
        
    Methods:
        .__init__
        .braid_action
        .commutation_matrix_from_list
        .cuspidal_decomposition
        .decompose_root
        .Euler_Ringel_pairing
        .fundamental_weights
        .simple_coroots
        .simple_reflections
        .simple_roots
        .Weyl_Group
        .height
        .is_decreasing_cuspidal
        .is_dominant
        .is_positive
        .latex_coroot
        .latex_root
        .latex_weight
        .pairing
        .phi_strings
        .reflection_across
        .string
        .symmetric_pairing
        .w
        .weightify
    """
    
    def __init__(self, n, A, D):
        """
        INPUT:
            n - the rank of the root system
            A - symmetrizable generalized Cartan matrix
            D - diagonal matrix so that DM is symmetric
        """
        #Initialize the combinatorial data
        self._rank = n
        self._cartan_matrix = A
        self._symmetrizing_matrix = D
        self._symmetric_cartan_matrix = D*A

        #Initialize the lattice data
        self._ambient_space = VectorSpace(QQ,2*self._rank)
        B = self._ambient_space.basis()

        self._fundamental_weights = []
        for i in range(0,self._rank):
            self._fundamental_weights.append(B[i])
        self._weight_lattice = self._ambient_space.subspace_with_basis(self._fundamental_weights)
        
        self._simple_roots = []
        for i in range(self._rank,2*self._rank):
            self._simple_roots.append(B[i])
        self._root_lattice = self._ambient_space.subspace_with_basis(self._simple_roots)

        self._simple_coroots = []
        for i in range(0,self._rank):
            self._simple_coroots.append(B[self._rank+i]/self._symmetrizing_matrix[i][i])
        self._coroot_lattice = self._ambient_space.subspace_with_basis(self._simple_coroots)

        self._zero = self._ambient_space.zero()


        #Initialize the Weyl group
        self._simple_reflections = []
        for i in range(0,self._rank):
            M=[]
            for r in range(0,2*self._rank):
                if r == self._rank+i:
                    M.append(list(identity_matrix(QQ,self._rank).row(i))+list(self._cartan_matrix.row(i)))
                else:
                    M.append(list(self._zero))
            self._simple_reflections.append(identity_matrix(QQ,2*self._rank)-matrix(QQ,M))
        self._Weyl_group = MatrixGroup(self._simple_reflections)
        
        self._ambient_char_ring = LaurentPolynomialRing(ZZ, 'e', self._rank)
        
        self._description = "The root system associated to the symmetrizable Cartan matrix %s with symmetrizing matrix %s"%(self._cartan_matrix.str(),self._symmetrizing_matrix.str())


    @property
    def rho(self):
        return sum(self.fundamental_weights())


    def is_finite(self):
        ct = self._cartan_matrix.cartan_type()
        if type(ct[0]) == str and len(ct) == 2:
            return true
        return false 
        
    
    def character_monomial(self, weight):
        return prod([self._ambient_char_ring.gen(i)**self.weightify(weight)[i] for i in xrange(self._rank)])


    def Weyl_character_formula(self, highest_weight):
        if not self.Weyl_group().is_finite():
            raise NotImplementedError("This root system is not finite and the Weyl character formula does not apply.")
        numer = self._ambient_char_ring(0)
        denom = self._ambient_char_ring(0)
        for w in self._Weyl_group:
            num_exp = w*(highest_weight+self.rho)
            den_exp = w*self.rho
            numer += self._Weyl_group.matrix_space()(w).determinant()*self.character_monomial(num_exp)
            denom += self._Weyl_group.matrix_space()(w).determinant()*self.character_monomial(den_exp)
        return numer/denom


    def weight_multiplicity(self, highest_weight, weight):
        character = self.Weyl_character_formula(highest_weight)
        numer = character.numerator()
        denom = character.denominator()
        denom_exp = sum([denom._mpoly_dict_recursive().keys()[0][i]*self.fundamental_weight(i) for i in xrange(self._rank)])
        exp = weight + denom_exp 
        return self._ambient_char_ring(numer).coefficient(self.character_monomial(exp))/self._ambient_char_ring(denom).coefficient(self.character_monomial(denom_exp))


    def braid_action(self, i, seq):
        """
        Input: An integer |i| between 1 and self.rank-1, a sequence of exceptional dimension vectors
        Output: The braid group action on the exceptional sequence, sigma_i has ith strand moving over (i-1)st strand, label of ith strand is fixed
        """
        temp = copy(seq)
        if i > 0:
            new_root = self.reflection_across(seq[i])*seq[i-1]
        if i < 0:
            new_root = self.reflection_across(seq[-i-1])*seq[-i]
        neg_switch = false
        for j in range(0,2*self._rank):
            if new_root[j] < 0:
                neg_switch = true
        if neg_switch:
            new_root *= -1
        if i > 0:
            temp[i-1] = temp[i]
            temp[i] = new_root
        if i < 0:
            temp[-i] = temp[-i-1]
            temp[-i-1] = new_root
        #print temp
        return temp

                    
    def commutation_matrix_from_list(self, bfi):
        """
        Input: A sequence bfi of m simple roots in range(0,self._rank)
        Output: A skew-symmetric matrix which can be used as the commutation matrix
                input for QuasiCommutativeLaurentPolynomialRing 
        """
        C = []
        for i in range(0,self.__ngens):
            row = []
            for j in range(0,self.__ngens):
                sum = 0
                for k in range(0,self.__ngens):
                    sum += self._symmetrizing_matrix[i][k]*self._cartan_matrix[k][j]
                row.append(sum)
            C.append(row)
        M = []
        len = bfi.__len__()
        for i in range(0,len):
            row = []
            for j in range(0,len):
                if i < j:
                    row.append(C[bfi[i]][bfi[j]])
                if i == j:
                    row.append(0)
                if j < i:
                    row.append(-C[bfi[i]][bfi[j]])
            M.append(row)
        return matrix(QQ,M)


    def cuspidal_decomposition(self, list, order):
        """
        Input: A list of simple roots and a choice of ordering on the simple roots
        Returns the decomposition of list into cuspidal words according to the increasing ordering 'order'
        """
        cuspidal_list = []
        cuspidal = []
        for i in list:
            if cuspidal == []:
                cuspidal.append(i)
            else:
                last = cuspidal.pop()
                cuspidal.append(last)
                if order.index(i) > order.index(last):
                    cuspidal.append(i)
                else:
                    cuspidal_list.append(copy(cuspidal))
                    cuspidal = [i]
        if cuspidal != []:
            cuspidal_list.append(copy(cuspidal))
        return cuspidal_list


    def decompose_root(self, root):
        """
        Input: A positive root
        Output: All possible sequences realizing this root
        """
        sequences = []
        init_height = self.height(root)
        if init_height <= 0:
            sequences   .append([])
            return sequences
        large_components = []
        max_component = 0
        for i in range(self._rank,2*self._rank):
            if root[i] > max_component:
                max_component = root[i]
                large_components = [i]
            elif root[i] == max_component:
                large_components.append(i)
        print "root=", root
        print "large_components=", large_components
        for i in large_components:
            new_root = self._simple_reflections[i-self._rank]*root
            new_height = self.height(new_root)
            if new_height < init_height:
                for seq in self.decompose_root(new_root):
                    sequences.append([i-self._rank]+seq)
        return sequences

        
    def Euler_Ringel_pairing(self, root1, root2):
        """
        Input: Two elements root1 and root2 in the root lattice
        Output: The Euler_Ringel pairing of root1 and root2 (assumes an acyclic quiver where an arrow i to j implies i < j)
        """
        output = 0
        for i in range(0,self._rank):
            for j in range(i,self._rank):
                if i == j:
                    output += root1[i]*root2[j]*self._symmetrizing_matrix[i][j]
                else:
                    output += root1[i]*root2[j]*self._symmetric_cartan_matrix[i][j]
        return output

    
    def fundamental_weight(self, i):
        return self._fundamental_weights[i]

    
    def fundamental_weights(self):
        return self._fundamental_weights

    
    def simple_coroot(self, i):
        return self._simple_coroots[i]

    
    def simple_coroots(self):
        return self._simple_coroots

    
    def simple_reflection(self, i):
        return self._simple_reflections[i]

    
    def simple_reflections(self):
        return self._simple_reflections

    
    def simple_root(self, i):
        return self._simple_roots[i]

    
    def simple_roots(self):
        return self._simple_roots

    
    def Weyl_group(self):
        return self._Weyl_group


    def height(self, root):
        """
        Input: A root, i.e. root[i]=0 for i in range(0,self._rank)
        ToDo: Type checking
        Output: The sum of all components
        """
        h = 0
        for i in range(self._rank,2*self._rank):
            h += root[i]
        return h


    def is_decreasing_cuspidal(self, list, order):
        """
        Input: A list of simple roots and a choice of ordering on the simple roots
        Output: True if list can be decomposed into a weakly decreasing concatenation of cuspidal words
        """
        cuspidal_list = self.cuspidal_decomposition(list,order)
        for i in range(0,cuspidal_list.__len__()-1):
            elt1 = cuspidal_list[i]
            elt2 = cuspidal_list[i+1]
            #print (elt1,elt2)
            min_len = elt1.__len__()
            if elt2.__len__() < min_len:
                min_len = elt2.__len__()
            equality_switch = true
            for j in range(0,min_len):
                if order.index(elt1[j]) < order.index(elt2[j]):
                    return false
                if order.index(elt1[j]) > order.index(elt2[j]):
                    equality_switch = false
                if equality_switch and min_len < elt2.__len__():
                    return false
        return true


    def is_dominant(self, weight):
        """
        Input: A weight, i.e. weight[i]=0 for i in range(self._rank,2*self._rank)
               possibly after identification modulo the kernel of the natural pairing
        """
        equiv_weight = weightify(weight)
        for i in range(0,self._rank):
            if equiv_weight[i] < 0:
                return False
        return True   


    def is_positive(self, root):
        """
        Input: A root, i.e. root[i]=0 for i in range(0,self._rank)
        ToDo: Type checking
        Output: True if all components are positive, False otherwise
        """
        for i in range(self._rank,2*self._rank):
            if root[i] < 0:
                return False
        return True


    def latex_coroot(self, coroot):
        """
        Input: A coroot, i.e. coroot[i]=0 for i in range(0,self._rank)
        ToDo: Type checking
        """
        output=""
        for i in range(self._rank,2*self._rank):
            if coroot[i]!=0:
                if output != "":
                    if coroot[i] > 0:
                        output += "+"
                if coroot[i]!=1:
                    if coroot[i] != -1:
                        output += str(coroot[i])
                    else:
                        output += "-"
                output += "\\alpha^\\vee_{" + str(i+1) + "}"
        return output


    def latex_root(self, root):
        """
        Input: A root, i.e. root[i]=0 for i in range(0,self._rank)
        ToDo: Type checking
        """
        output=""
        for i in range(self._rank,2*self._rank):
            if root[i]!=0:
                if output != "":
                    if root[i] > 0:
                        output += "+"
                if root[i]!=1:
                    if root[i] != -1:
                        output += str(root[i])
                    else:
                        output += "-"
                output += "\\alpha_{" + str(i+1) + "}"
        return output


    def latex_weight(self, weight):
        """
        Input: A weight, i.e. weight[i]=0 for i in range(self._rank,2*self._rank)
        ToDo: Type checking
        """
        output=""
        for i in range(0,self.rank):
            if weight[i]!=0:
                if output != "":
                    if weight[i] > 0:
                        output += "+"
                if weight[i]!=1:
                    if weight[i] != -1:
                        output += str(weight[i])
                    else:
                        output += "-"
                output += "\\omega_{" + str(i+1) + "}"
        for i in range(self._rank,2*self._rank):
            if weight[i]!=0:
                if output != "":
                    if weight[i] > 0:
                        output += "+"
                if weight[i]!=1:
                    if weight[i] != -1:
                        output += str(weight[i])
                    else:
                        output += "-"
                output += "\\alpha_{" + str(i+1) + "}"
        return output

        
    def pairing(self, root, weight):
        return 2*self.symmetric_pairing(root,weight)/self.symmetric_pairing(root,root)


    def phi_strings(self, bfi):
        """
        Input: A sequence bfi of m simple roots in range(0,self._rank)
        Output: A list of $\varphi_\bfi^{-1}(\varepsilon_\ell)$ for $1\le\ell\le m$ (see [Berenstein-Rupel] for details)
        """
        bfa = []
        m = bfi.__len__()
        for ell in range(0,m):
            weight = self.w(ell+1,bfi)*self._fundamental_weights[bfi[ell]]
            string = []
            for k in range(0,ell+1):
                string.append(-self.symmetric_pairing(self.w(k+1,bfi)*self._simple_coroots[bfi[k]],weight))
            for k in range(ell+1,m):
                string.append(0)
            bfa.append(string)
        return bfa 


    def reflection_across(self, root):
        """
        Input: An element of the root lattice
        Output: The element of self._Weyl_group which corresponds to the reflection across the hyperplane orthogonal to the root
        """
        M = []
        for i in range(0,self._rank):
            M.append(self.pairing(root,self._fundamental_weights[i])*root)
        for i in range(0,self._rank):
            M.append(self.pairing(root,self._simple_roots[i])*root)
        M = Matrix(QQ,M)
        return identity_matrix(QQ,2*self._rank)-M.transpose()


    def string(self, bfi, weight):
        """
        Input: A sequence bfi of simple roots in range(0,self._rank)
        """ 
        bfa = []
        m = bfi.__len__()
        for ell in range(0,m):
            bfa.append(self.symmetric_pairing(self.w(ell+1,bfi)*self._simple_coroots[bfi[ell]],weight))
        return bfa

        
    def symmetric_pairing(self, root, weight):
        """
        Input: A root, i.e. root[i]=0 for i in range(0,self._rank), and a weight
        ToDo: Type checking
        """
        sum = 0
        for i in range(0,self._rank):
            sum += root[self._rank+i]*self._symmetrizing_matrix[i][i]*weight[i]
            for j in range(0,self._rank):
                sum += root[self._rank+i]*self._symmetric_cartan_matrix[i][j]*weight[self._rank+j]
        return sum


    def w(self, ell, bfi):
        """
        Input: A sequence bfi of m simple roots in range(0,self._rank) and an integer ell <= m
        Output: The Weyl group element $w_\ell=s_{i_1}\cdots s_{i_\ell}$
        """
        element = identity_matrix(QQ,2*self._rank)
        for i in range(0,ell):
            element = self._simple_reflections[bfi[ell-i-1]]*element
        return element


    def weightify(self, weight):
        """
        Input: Any element of the ambient vector space
        Output: The equivalent element of the weight lattice modulo the kernel of the natural pairing
        """
        equiv_weight = self._zero
        for i in range(0,self._rank):
            equiv_weight += weight[i]*self._fundamental_weights[i]
            for j in range(0,self._rank):
                equiv_weight += weight[self._rank+i]*self._cartan_matrix[j][i]*self._fundamental_weights[j]
        return equiv_weight

    

    #TODO: Write a method for determining if a given matrix is an element of the Weyl group
    #      in the process I will probably find a representation in terms of generators,
    #      this representation should be returned
    #
    #  In both cases it should probably be in terms of some sort of descent algorithm
    #TODO: Write a length function for the Weyl group
