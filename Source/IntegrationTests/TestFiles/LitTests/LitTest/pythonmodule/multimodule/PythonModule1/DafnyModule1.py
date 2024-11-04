import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import PythonModule1.module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: PythonModule1.DafnyModule1

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def HelloWorld():
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Hello World"))).VerbatimString(False))

