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
import Std_JSON_Utils_Views_Core
import Std_JSON_Utils_Views_Writers
import Std_JSON_Utils_Views
import Std_JSON_Utils_Lexers_Core
import Std_JSON_Utils_Lexers_Strings
import Std_JSON_Utils_Lexers
import Std_JSON_Utils_Cursors
import Std_JSON_Utils_Parsers
import Std_JSON_Utils
import Std_JSON_Grammar
import Std_JSON_ByteStrConversion
import Std_JSON_Serializer
import Std_JSON_Deserializer_Uint16StrConversion
import Std_JSON_Deserializer
import Std_JSON_ConcreteSyntax_Spec
import Std_JSON_ConcreteSyntax_SpecProperties
import Std_JSON_ConcreteSyntax
import Std_JSON_ZeroCopy_Serializer
import Std_JSON_ZeroCopy_Deserializer_Core
import Std_JSON_ZeroCopy_Deserializer_Strings
import Std_JSON_ZeroCopy_Deserializer_Numbers
import Std_JSON_ZeroCopy_Deserializer_ObjectParams
import Std_JSON_ZeroCopy_Deserializer_Objects
import Std_JSON_ZeroCopy_Deserializer_ArrayParams
import Std_JSON_ZeroCopy_Deserializer_Arrays
import Std_JSON_ZeroCopy_Deserializer_Constants
import Std_JSON_ZeroCopy_Deserializer_Values

# Module: Std_JSON_ZeroCopy_Deserializer_API

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def LiftCursorError(err):
        source24_ = err
        if source24_.is_EOF:
            return Std_JSON_Errors.DeserializationError_ReachedEOF()
        elif source24_.is_ExpectingByte:
            d_750___mcc_h0_ = source24_.expected
            d_751___mcc_h1_ = source24_.b
            d_752_b_ = d_751___mcc_h1_
            d_753_expected_ = d_750___mcc_h0_
            return Std_JSON_Errors.DeserializationError_ExpectingByte(d_753_expected_, d_752_b_)
        elif source24_.is_ExpectingAnyByte:
            d_754___mcc_h2_ = source24_.expected__sq
            d_755___mcc_h3_ = source24_.b
            d_756_b_ = d_755___mcc_h3_
            d_757_expected__sq_ = d_754___mcc_h2_
            return Std_JSON_Errors.DeserializationError_ExpectingAnyByte(d_757_expected__sq_, d_756_b_)
        elif True:
            d_758___mcc_h4_ = source24_.err
            d_759_err_ = d_758___mcc_h4_
            return d_759_err_

    @staticmethod
    def JSON(cs):
        return (Std_JSON_ZeroCopy_Deserializer_Core.default__.Structural(cs, Std_JSON_ZeroCopy_Deserializer_Values.default__.Value)).MapFailure(default__.LiftCursorError)

    @staticmethod
    def Text(v):
        d_760_valueOrError0_ = default__.JSON(Std_JSON_Utils_Cursors.Cursor__.OfView(v))
        if (d_760_valueOrError0_).IsFailure():
            return (d_760_valueOrError0_).PropagateFailure()
        elif True:
            let_tmp_rhs39_ = (d_760_valueOrError0_).Extract()
            d_761_text_ = let_tmp_rhs39_.t
            d_762_cs_ = let_tmp_rhs39_.cs
            d_763_valueOrError1_ = Std_Wrappers.default__.Need((d_762_cs_).EOF_q, Std_JSON_Errors.DeserializationError_ExpectingEOF())
            if (d_763_valueOrError1_).IsFailure():
                return (d_763_valueOrError1_).PropagateFailure()
            elif True:
                return Std_Wrappers.Result_Success(d_761_text_)

    @staticmethod
    def OfBytes(bs):
        d_764_valueOrError0_ = Std_Wrappers.default__.Need((len(bs)) < (Std_BoundedInts.default__.TWO__TO__THE__32), Std_JSON_Errors.DeserializationError_IntOverflow())
        if (d_764_valueOrError0_).IsFailure():
            return (d_764_valueOrError0_).PropagateFailure()
        elif True:
            return default__.Text(Std_JSON_Utils_Views_Core.View__.OfBytes(bs))

