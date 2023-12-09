import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Std_Wrappers
import Std_BoundedInts
import Std_Base64
import Std_Relations

# Module: Std_Math

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Min(a, b):
        if (a) < (b):
            return a
        elif True:
            return b

    @staticmethod
    def Min3(a, b, c):
        return default__.Min(a, default__.Min(b, c))

    @staticmethod
    def Max(a, b):
        if (a) < (b):
            return b
        elif True:
            return a

    @staticmethod
    def Max3(a, b, c):
        return default__.Max(a, default__.Max(b, c))

    @staticmethod
    def Abs(a):
        if (a) < (0):
            return (0) - (a)
        elif True:
            return a

