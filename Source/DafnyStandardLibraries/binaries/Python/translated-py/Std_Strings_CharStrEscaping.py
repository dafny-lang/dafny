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
import Std_Arithmetic_Power
import Std_Arithmetic_Logarithm
import Std_Arithmetic_Power2
import Std_Arithmetic
import Std_Strings_HexConversion
import Std_Strings_DecimalConversion

# Module: Std_Strings_CharStrEscaping

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Escape(str, mustEscape, escape):
        d_152___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (str) == (_dafny.SeqWithoutIsStrInference([])):
                    return (d_152___accumulator_) + (str)
                elif ((str)[0]) in (mustEscape):
                    d_152___accumulator_ = (d_152___accumulator_) + (_dafny.SeqWithoutIsStrInference([escape, (str)[0]]))
                    in52_ = _dafny.SeqWithoutIsStrInference((str)[1::])
                    in53_ = mustEscape
                    in54_ = escape
                    str = in52_
                    mustEscape = in53_
                    escape = in54_
                    raise _dafny.TailCall()
                elif True:
                    d_152___accumulator_ = (d_152___accumulator_) + (_dafny.SeqWithoutIsStrInference([(str)[0]]))
                    in55_ = _dafny.SeqWithoutIsStrInference((str)[1::])
                    in56_ = mustEscape
                    in57_ = escape
                    str = in55_
                    mustEscape = in56_
                    escape = in57_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Unescape(str, escape):
        if (str) == (_dafny.SeqWithoutIsStrInference([])):
            return Std_Wrappers.Option_Some(str)
        elif ((str)[0]) == (escape):
            if (len(str)) > (1):
                d_153_valueOrError0_ = default__.Unescape(_dafny.SeqWithoutIsStrInference((str)[2::]), escape)
                if (d_153_valueOrError0_).IsFailure():
                    return (d_153_valueOrError0_).PropagateFailure()
                elif True:
                    d_154_tl_ = (d_153_valueOrError0_).Extract()
                    return Std_Wrappers.Option_Some((_dafny.SeqWithoutIsStrInference([(str)[1]])) + (d_154_tl_))
            elif True:
                return Std_Wrappers.Option_None()
        elif True:
            d_155_valueOrError1_ = default__.Unescape(_dafny.SeqWithoutIsStrInference((str)[1::]), escape)
            if (d_155_valueOrError1_).IsFailure():
                return (d_155_valueOrError1_).PropagateFailure()
            elif True:
                d_156_tl_ = (d_155_valueOrError1_).Extract()
                return Std_Wrappers.Option_Some((_dafny.SeqWithoutIsStrInference([(str)[0]])) + (d_156_tl_))

