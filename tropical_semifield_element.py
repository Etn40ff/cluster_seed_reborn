from sage.monoids.free_abelian_monoid_element import FreeAbelianMonoidElement

class TropicalSemifieldElement(FreeAbelianMonoidElement):
    def __init__(self, parent, val = None):
        FreeAbelianMonoidElement.__init__(self,parent,val)
    
    def __add__(self, other):
        a = self.list()
        b = other.list()
        return prod([ self.parent().gen(i)**min(a[i],b[i]) for i in xrange(self.parent().ngens()) ])

    def __invert__(self):
        return self**(-1)

    def __pow__(self, n):
        if not isinstance(n, (int, long, Integer)):
            raise TypeError("Argument n (= %s) must be an integer."%n)
        else:
            z = self.parent()(1)
            z._FreeAbelianMonoidElement__element_vector = [i*n for i in self.list()]
            return z

