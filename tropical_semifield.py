from sage.groups.indexed_free_group import IndexedFreeAbelianGroup
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.parent import Parent

class TropicalSemifield(SageObject):
    
    def __init__(self, arg1 = None, arg2 = None, names = None, name = None):
        print arg1
        print arg2
        arg1 = list(arg1)

        if isinstance(arg1, (int, long, Integer)):
            arg1, arg2 = arg2, arg1
    
        if not names is None:
            arg1 = names
        elif not name is None:
            arg1 = name

        if arg1 is None:
            raise TypeError("You must specify the names of the variables.")

        if isinstance(arg1, (list, tuple)):
            arg1 = [str(x) for x in arg1]
        elif isinstance(arg1,str):
            if ',' in arg1:
                arg1 = arg1.split(',')
        else:
            raise TypeError("You must specify the names of the variables.")
        
        if isinstance(arg2, (int, long, Integer)):
            n = int(arg2)
            if isinstance(arg1,str):
                names = [arg1+str(i) for i in xrange(n)]
            else:
                if n != len(arg1):
                    raise IndexError("The number of names must equal the number of generators.")
                names = arg1
        elif arg2 == None:
            if not isinstance(arg1,(list,tuple)):
                arg1 = [arg1]
            n = len(arg1)    
            names = arg1
        else:
            raise TypeError("Weird input for arg2.") 

        IndexedFreeAbelianGroup.__init__(self, names, category=[Semirings(),Groups()])

    #def _element_constructor_(self, val):
    

