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
import Std_Math
import Std_Collections_Seq
import Std_Collections_Array

# Module: Std_Collections_Imap

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Get(m, x):
        if (x) in (m):
            return Std_Wrappers.Option_Some((m)[x])
        elif True:
            return Std_Wrappers.Option_None()

