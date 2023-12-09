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

# Module: Std_Arithmetic_Power

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Pow(b, e):
        d_118___accumulator_ = 1
        while True:
            with _dafny.label():
                if (e) == (0):
                    return (1) * (d_118___accumulator_)
                elif True:
                    d_118___accumulator_ = (d_118___accumulator_) * (b)
                    in38_ = b
                    in39_ = (e) - (1)
                    b = in38_
                    e = in39_
                    raise _dafny.TailCall()
                break

