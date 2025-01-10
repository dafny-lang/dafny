import sys
import _dafny

# Module: Nested.Library

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "Nested.Library_Compile._default"

    @_dafny.classproperty
    def TWO(instance):
        return 2

    @_dafny.classproperty
    def THREE(instance):
        return default__.TWO + 1