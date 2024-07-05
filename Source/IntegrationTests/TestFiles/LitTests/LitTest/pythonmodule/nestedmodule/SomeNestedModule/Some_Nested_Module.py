import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import SomeNestedModule.module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: Some_Nested_Module

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def HelloWorld():
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hello World"))).VerbatimString(False))

