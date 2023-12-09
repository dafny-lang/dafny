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
import Std_Strings_CharStrEscaping

# Module: Std_Strings

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def OfNat(n):
        return Std_Strings_DecimalConversion.default__.OfNat(n)

    @staticmethod
    def OfInt(n):
        return Std_Strings_DecimalConversion.default__.OfInt(n, _dafny.CodePoint('-'))

    @staticmethod
    def ToNat(str):
        return Std_Strings_DecimalConversion.default__.ToNat(str)

    @staticmethod
    def ToInt(str):
        return Std_Strings_DecimalConversion.default__.ToInt(str, _dafny.CodePoint('-'))

    @staticmethod
    def EscapeQuotes(str):
        return Std_Strings_CharStrEscaping.default__.Escape(str, _dafny.Set({_dafny.CodePoint('\"'), _dafny.CodePoint('\'')}), _dafny.CodePoint('\\'))

    @staticmethod
    def UnescapeQuotes(str):
        return Std_Strings_CharStrEscaping.default__.Unescape(str, _dafny.CodePoint('\\'))

    @staticmethod
    def OfBool(b):
        if b:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true"))
        elif True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false"))

    @staticmethod
    def OfChar(c):
        return _dafny.SeqWithoutIsStrInference([c])

    @staticmethod
    def Join(sep, strs):
        d_157___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(strs)) == (0):
                    return (d_157___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif (len(strs)) == (1):
                    return (d_157___accumulator_) + ((strs)[0])
                elif True:
                    d_157___accumulator_ = (d_157___accumulator_) + (((strs)[0]) + (sep))
                    in58_ = sep
                    in59_ = _dafny.SeqWithoutIsStrInference((strs)[1::])
                    sep = in58_
                    strs = in59_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Concat(strs):
        d_158___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(strs)) == (0):
                    return (d_158___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_158___accumulator_ = (d_158___accumulator_) + ((strs)[0])
                    in60_ = _dafny.SeqWithoutIsStrInference((strs)[1::])
                    strs = in60_
                    raise _dafny.TailCall()
                break

