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
import Std_Strings
import Std_Unicode_Base
import Std_Unicode_Utf8EncodingForm
import Std_Unicode_Utf16EncodingForm
import Std_Unicode_UnicodeStringsWithUnicodeChar
import Std_Unicode_Utf8EncodingScheme
import Std_Unicode
import Std_PythonConcurrent
import Std_PythonFileIOInternalExterns
import Std_JSON_Values
import Std_JSON_Errors
import Std_JSON_Spec

# Module: Std_JSON_Utils_Views_Core

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Adjacent(lv, rv):
        return (((lv).end) == ((rv).beg)) and (((lv).s) == ((rv).s))

    @staticmethod
    def Merge(lv, rv):
        d_335_dt__update__tmp_h0_ = lv
        d_336_dt__update_hend_h0_ = (rv).end
        return View___View((d_335_dt__update__tmp_h0_).s, (d_335_dt__update__tmp_h0_).beg, d_336_dt__update_hend_h0_)


class View:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return View___View(_dafny.SeqWithoutIsStrInference([]), 0, 0)

class View__:
    @classmethod
    def default(cls, ):
        return lambda: View___View(_dafny.Seq({}), int(0), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_View(self) -> bool:
        return isinstance(self, View___View)
    def Length(self):
        return ((self).end) - ((self).beg)

    def Bytes(self):
        return _dafny.SeqWithoutIsStrInference(((self).s)[(self).beg:(self).end:])

    @staticmethod
    def OfBytes(bs):
        return View___View(bs, 0, len(bs))

    @staticmethod
    def OfString(s):
        return _dafny.SeqWithoutIsStrInference([ord((s)[d_337_i_]) for d_337_i_ in range(len(s))])

    def Byte_q(self, c):
        hresult_: bool = False
        hresult_ = (((self).Length()) == (1)) and (((self).At(0)) == (c))
        return hresult_
        return hresult_

    def Char_q(self, c):
        return (self).Byte_q(ord(c))

    def At(self, idx):
        return ((self).s)[((self).beg) + (idx)]

    def Peek(self):
        if (self).Empty_q:
            return -1
        elif True:
            return (self).At(0)

    def CopyTo(self, dest, start):
        hi0_ = (self).Length()
        for d_338_idx_ in range(0, hi0_):
            index6_ = (start) + (d_338_idx_)
            (dest)[index6_] = ((self).s)[((self).beg) + (d_338_idx_)]

    @_dafny.classproperty
    def Empty(instance):
        return View___View(_dafny.SeqWithoutIsStrInference([]), 0, 0)
    @property
    def Empty_q(self):
        return ((self).beg) == ((self).end)

class View___View(View__, NamedTuple('View', [('s', Any), ('beg', Any), ('end', Any)])):
    def __dafnystr__(self) -> str:
        return f'Core.View_.View({_dafny.string_of(self.s)}, {_dafny.string_of(self.beg)}, {_dafny.string_of(self.end)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, View___View) and self.s == __o.s and self.beg == __o.beg and self.end == __o.end
    def __hash__(self) -> int:
        return super().__hash__()

