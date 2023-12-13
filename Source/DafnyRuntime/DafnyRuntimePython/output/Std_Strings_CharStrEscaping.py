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
        d_162___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (str) == (_dafny.SeqWithoutIsStrInference([])):
                    return (d_162___accumulator_) + (str)
                elif ((str)[0]) in (mustEscape):
                    d_162___accumulator_ = (d_162___accumulator_) + (_dafny.SeqWithoutIsStrInference([escape, (str)[0]]))
                    in56_ = _dafny.SeqWithoutIsStrInference((str)[1::])
                    in57_ = mustEscape
                    in58_ = escape
                    str = in56_
                    mustEscape = in57_
                    escape = in58_
                    raise _dafny.TailCall()
                elif True:
                    d_162___accumulator_ = (d_162___accumulator_) + (_dafny.SeqWithoutIsStrInference([(str)[0]]))
                    in59_ = _dafny.SeqWithoutIsStrInference((str)[1::])
                    in60_ = mustEscape
                    in61_ = escape
                    str = in59_
                    mustEscape = in60_
                    escape = in61_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Unescape(str, escape):
        if (str) == (_dafny.SeqWithoutIsStrInference([])):
            return Std_Wrappers.Option_Some(str)
        elif ((str)[0]) == (escape):
            if (len(str)) > (1):
                d_163_valueOrError0_ = default__.Unescape(_dafny.SeqWithoutIsStrInference((str)[2::]), escape)
                if (d_163_valueOrError0_).IsFailure():
                    return (d_163_valueOrError0_).PropagateFailure()
                elif True:
                    d_164_tl_ = (d_163_valueOrError0_).Extract()
                    return Std_Wrappers.Option_Some((_dafny.SeqWithoutIsStrInference([(str)[1]])) + (d_164_tl_))
            elif True:
                return Std_Wrappers.Option_None()
        elif True:
            d_165_valueOrError1_ = default__.Unescape(_dafny.SeqWithoutIsStrInference((str)[1::]), escape)
            if (d_165_valueOrError1_).IsFailure():
                return (d_165_valueOrError1_).PropagateFailure()
            elif True:
                d_166_tl_ = (d_165_valueOrError1_).Extract()
                return Std_Wrappers.Option_Some((_dafny.SeqWithoutIsStrInference([(str)[0]])) + (d_166_tl_))

