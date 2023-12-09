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

# Module: Std_Arithmetic_DivInternals

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def DivPos(x, d):
        d_117___accumulator_ = 0
        while True:
            with _dafny.label():
                if (x) < (0):
                    d_117___accumulator_ = (d_117___accumulator_) + (-1)
                    in34_ = (x) + (d)
                    in35_ = d
                    x = in34_
                    d = in35_
                    raise _dafny.TailCall()
                elif (x) < (d):
                    return (0) + (d_117___accumulator_)
                elif True:
                    d_117___accumulator_ = (d_117___accumulator_) + (1)
                    in36_ = (x) - (d)
                    in37_ = d
                    x = in36_
                    d = in37_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def DivRecursive(x, d):
        if (d) > (0):
            return default__.DivPos(x, d)
        elif True:
            return (-1) * (default__.DivPos(x, (-1) * (d)))

