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
        d_258_asCodeUnits_ = Std_Collections_Seq.default__.Map(default__.CharAsUnicodeScalarValue, s)
        d_259_asUtf8CodeUnits_ = Std_Unicode_Utf8EncodingForm.default__.EncodeScalarSequence(d_258_asCodeUnits_)
        def lambda11_(d_261_cu_):
            return d_261_cu_

        d_260_asBytes_ = Std_Collections_Seq.default__.Map(lambda11_, d_259_asUtf8CodeUnits_)
        return Std_Wrappers.Option_Some(d_260_asBytes_)

    @staticmethod
    def FromUTF8Checked(bs):
        def lambda12_(d_263_c_):
            return d_263_c_

        d_262_asCodeUnits_ = Std_Collections_Seq.default__.Map(lambda12_, bs)
        d_264_valueOrError0_ = Std_Unicode_Utf8EncodingForm.default__.DecodeCodeUnitSequenceChecked(d_262_asCodeUnits_)
        if (d_264_valueOrError0_).IsFailure():
            return (d_264_valueOrError0_).PropagateFailure()
        elif True:
            d_265_utf32_ = (d_264_valueOrError0_).Extract()
            d_266_asChars_ = Std_Collections_Seq.default__.Map(default__.CharFromUnicodeScalarValue, d_265_utf32_)
            return Std_Wrappers.Option_Some(d_266_asChars_)

    @staticmethod
    def ToUTF16Checked(s):
        d_267_asCodeUnits_ = Std_Collections_Seq.default__.Map(default__.CharAsUnicodeScalarValue, s)
        d_268_asUtf16CodeUnits_ = Std_Unicode_Utf16EncodingForm.default__.EncodeScalarSequence(d_267_asCodeUnits_)
        def lambda13_(d_270_cu_):
            return d_270_cu_

        d_269_asBytes_ = Std_Collections_Seq.default__.Map(lambda13_, d_268_asUtf16CodeUnits_)
        return Std_Wrappers.Option_Some(d_269_asBytes_)

    @staticmethod
    def FromUTF16Checked(bs):
        def lambda14_(d_272_c_):
            return d_272_c_

        d_271_asCodeUnits_ = Std_Collections_Seq.default__.Map(lambda14_, bs)
        d_273_valueOrError0_ = Std_Unicode_Utf16EncodingForm.default__.DecodeCodeUnitSequenceChecked(d_271_asCodeUnits_)
        if (d_273_valueOrError0_).IsFailure():
            return (d_273_valueOrError0_).PropagateFailure()
        elif True:
            d_274_utf32_ = (d_273_valueOrError0_).Extract()
            d_275_asChars_ = Std_Collections_Seq.default__.Map(default__.CharFromUnicodeScalarValue, d_274_utf32_)
            return Std_Wrappers.Option_Some(d_275_asChars_)

    @staticmethod
    def ASCIIToUTF8(s):
        def lambda15_(d_276_c_):
            return ord(d_276_c_)

        return Std_Collections_Seq.default__.Map(lambda15_, s)

    @staticmethod
    def ASCIIToUTF16(s):
        def lambda16_(d_277_c_):
            return ord(d_277_c_)

        return Std_Collections_Seq.default__.Map(lambda16_, s)

