import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Std_Wrappers
import Std_Concurrent
import Std_FileIOInternalExterns
import Std_BoundedInts
import Std_Base64
import Std_Relations
import Std_Math
import Std_Collections_Seq
import Std_Collections_Array
import Std_Collections_Imap
import Std_Functions
import Std_Collections_Iset
import Std_Collections_Map
import Std_Collections_Set
import Std_Collections
import Std_DynamicArray
import Std_FileIO
import Std_Arithmetic_GeneralInternals
import Std_Arithmetic_MulInternalsNonlinear
import Std_Arithmetic_MulInternals
import Std_Arithmetic_Mul
import Std_Arithmetic_ModInternalsNonlinear
import Std_Arithmetic_DivInternalsNonlinear
import Std_Arithmetic_ModInternals
import Std_Arithmetic_DivInternals
import Std_Arithmetic_DivMod
import Std_Arithmetic_Power

# Module: Std_Arithmetic_Logarithm

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Log(base, pow):
        d_129___accumulator_ = 0
        while True:
            with _dafny.label():
                if (pow) < (base):
                    return (0) + (d_129___accumulator_)
                elif True:
                    d_129___accumulator_ = (d_129___accumulator_) + (1)
                    in44_ = base
                    in45_ = _dafny.euclidian_division(pow, base)
                    base = in44_
                    pow = in45_
                    raise _dafny.TailCall()
                break

