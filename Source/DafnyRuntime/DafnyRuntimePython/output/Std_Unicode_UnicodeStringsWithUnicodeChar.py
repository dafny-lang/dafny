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
import Std_Strings_CharStrEscaping
import Std_Strings
import Std_Unicode_Base
import Std_Unicode_Utf8EncodingForm
import Std_Unicode_Utf16EncodingForm

# Module: Std_Unicode_UnicodeStringsWithUnicodeChar

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def CharAsUnicodeScalarValue(c):
        return ord(c)

    @staticmethod
    def CharFromUnicodeScalarValue(sv):
        return _dafny.CodePoint(chr(sv))

    @staticmethod
    def ToUTF8Checked(s):
        d_266_asCodeUnits_ = Std_Collections_Seq.default__.Map(default__.CharAsUnicodeScalarValue, s)
        d_267_asUtf8CodeUnits_ = Std_Unicode_Utf8EncodingForm.default__.EncodeScalarSequence(d_266_asCodeUnits_)
        def lambda13_(d_269_cu_):
            return d_269_cu_

        d_268_asBytes_ = Std_Collections_Seq.default__.Map(lambda13_, d_267_asUtf8CodeUnits_)
        return Std_Wrappers.Option_Some(d_268_asBytes_)

    @staticmethod
    def FromUTF8Checked(bs):
        def lambda14_(d_271_c_):
            return d_271_c_

        d_270_asCodeUnits_ = Std_Collections_Seq.default__.Map(lambda14_, bs)
        d_272_valueOrError0_ = Std_Unicode_Utf8EncodingForm.default__.DecodeCodeUnitSequenceChecked(d_270_asCodeUnits_)
        if (d_272_valueOrError0_).IsFailure():
            return (d_272_valueOrError0_).PropagateFailure()
        elif True:
            d_273_utf32_ = (d_272_valueOrError0_).Extract()
            d_274_asChars_ = Std_Collections_Seq.default__.Map(default__.CharFromUnicodeScalarValue, d_273_utf32_)
            return Std_Wrappers.Option_Some(d_274_asChars_)

    @staticmethod
    def ToUTF16Checked(s):
        d_275_asCodeUnits_ = Std_Collections_Seq.default__.Map(default__.CharAsUnicodeScalarValue, s)
        d_276_asUtf16CodeUnits_ = Std_Unicode_Utf16EncodingForm.default__.EncodeScalarSequence(d_275_asCodeUnits_)
        def lambda15_(d_278_cu_):
            return d_278_cu_

        d_277_asBytes_ = Std_Collections_Seq.default__.Map(lambda15_, d_276_asUtf16CodeUnits_)
        return Std_Wrappers.Option_Some(d_277_asBytes_)

    @staticmethod
    def FromUTF16Checked(bs):
        def lambda16_(d_280_c_):
            return d_280_c_

        d_279_asCodeUnits_ = Std_Collections_Seq.default__.Map(lambda16_, bs)
        d_281_valueOrError0_ = Std_Unicode_Utf16EncodingForm.default__.DecodeCodeUnitSequenceChecked(d_279_asCodeUnits_)
        if (d_281_valueOrError0_).IsFailure():
            return (d_281_valueOrError0_).PropagateFailure()
        elif True:
            d_282_utf32_ = (d_281_valueOrError0_).Extract()
            d_283_asChars_ = Std_Collections_Seq.default__.Map(default__.CharFromUnicodeScalarValue, d_282_utf32_)
            return Std_Wrappers.Option_Some(d_283_asChars_)

    @staticmethod
    def ASCIIToUTF8(s):
        def lambda17_(d_284_c_):
            return ord(d_284_c_)

        return Std_Collections_Seq.default__.Map(lambda17_, s)

    @staticmethod
    def ASCIIToUTF16(s):
        def lambda18_(d_285_c_):
            return ord(d_285_c_)

        return Std_Collections_Seq.default__.Map(lambda18_, s)

