from sage.monoids.free_abelian_monoid import FreeAbelianMonoid_class

class TropicalSemifield(FreeAbelianMonoid_class):
    Element = TropicalSemifieldElement

    def __init__(self, name, n):
        FreeAbelianMonoid_class.__init__(self,name,n)
        #base = FreeAbelianMonoid(name,n)
        #Parent.__init__(self, base=base, category=[Semirings(),Groups()])
   

    def __call__(self, x):
        if isinstance(x, TropicalSemifieldElement) and x.parent() == self:
            return x
        return TropicalSemifieldElement(self, x)


