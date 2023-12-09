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

# Module: Std_JSON_Spec

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def EscapeUnicode(c):
        d_298_sStr_ = Std_Strings_HexConversion.default__.OfNat(c)
        d_299_s_ = Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(d_298_sStr_)
        return (d_299_s_) + (_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint(' ')) for d_300___v8_ in range((4) - (len(d_299_s_)))]))

    @staticmethod
    def Escape(str, start):
        d_301___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                pat_let_tv0_ = str
                pat_let_tv1_ = start
                if (start) >= (len(str)):
                    return (d_301___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    def iife7_(_pat_let1_0):
                        def iife8_(d_302_c_):
                            return ((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\u")))) + (default__.EscapeUnicode(d_302_c_)) if (d_302_c_) < (31) else _dafny.SeqWithoutIsStrInference([(pat_let_tv0_)[pat_let_tv1_]]))
                        return iife8_(_pat_let1_0)
                    d_301___accumulator_ = (d_301___accumulator_) + ((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\\""))) if ((str)[start]) == (34) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\\\"))) if ((str)[start]) == (92) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\b"))) if ((str)[start]) == (8) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\f"))) if ((str)[start]) == (12) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\n"))) if ((str)[start]) == (10) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\r"))) if ((str)[start]) == (13) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF16(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\\t"))) if ((str)[start]) == (9) else iife7_((str)[start])))))))))
                    in61_ = str
                    in62_ = (start) + (1)
                    str = in61_
                    start = in62_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def EscapeToUTF8(str, start):
        d_303_valueOrError0_ = (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ToUTF16Checked(str)).ToResult(Std_JSON_Errors.SerializationError_InvalidUnicode())
        if (d_303_valueOrError0_).IsFailure():
            return (d_303_valueOrError0_).PropagateFailure()
        elif True:
            d_304_utf16_ = (d_303_valueOrError0_).Extract()
            d_305_escaped_ = default__.Escape(d_304_utf16_, 0)
            d_306_valueOrError1_ = (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.FromUTF16Checked(d_305_escaped_)).ToResult(Std_JSON_Errors.SerializationError_InvalidUnicode())
            if (d_306_valueOrError1_).IsFailure():
                return (d_306_valueOrError1_).PropagateFailure()
            elif True:
                d_307_utf32_ = (d_306_valueOrError1_).Extract()
                return (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ToUTF8Checked(d_307_utf32_)).ToResult(Std_JSON_Errors.SerializationError_InvalidUnicode())

    @staticmethod
    def String(str):
        d_308_valueOrError0_ = default__.EscapeToUTF8(str, 0)
        if (d_308_valueOrError0_).IsFailure():
            return (d_308_valueOrError0_).PropagateFailure()
        elif True:
            d_309_inBytes_ = (d_308_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))) + (d_309_inBytes_)) + (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\"")))))

    @staticmethod
    def IntToBytes(n):
        d_310_s_ = Std_Strings.default__.OfInt(n)
        return Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(d_310_s_)

    @staticmethod
    def Number(dec):
        return Std_Wrappers.Result_Success((default__.IntToBytes((dec).n)) + ((_dafny.SeqWithoutIsStrInference([]) if ((dec).e10) == (0) else (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "e")))) + (default__.IntToBytes((dec).e10)))))

    @staticmethod
    def KeyValue(kv):
        d_311_valueOrError0_ = default__.String((kv)[0])
        if (d_311_valueOrError0_).IsFailure():
            return (d_311_valueOrError0_).PropagateFailure()
        elif True:
            d_312_key_ = (d_311_valueOrError0_).Extract()
            d_313_valueOrError1_ = default__.JSON((kv)[1])
            if (d_313_valueOrError1_).IsFailure():
                return (d_313_valueOrError1_).PropagateFailure()
            elif True:
                d_314_value_ = (d_313_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success(((d_312_key_) + (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ":"))))) + (d_314_value_))

    @staticmethod
    def Join(sep, items):
        if (len(items)) == (0):
            return Std_Wrappers.Result_Success(_dafny.SeqWithoutIsStrInference([]))
        elif True:
            d_315_valueOrError0_ = (items)[0]
            if (d_315_valueOrError0_).IsFailure():
                return (d_315_valueOrError0_).PropagateFailure()
            elif True:
                d_316_first_ = (d_315_valueOrError0_).Extract()
                if (len(items)) == (1):
                    return Std_Wrappers.Result_Success(d_316_first_)
                elif True:
                    d_317_valueOrError1_ = default__.Join(sep, _dafny.SeqWithoutIsStrInference((items)[1::]))
                    if (d_317_valueOrError1_).IsFailure():
                        return (d_317_valueOrError1_).PropagateFailure()
                    elif True:
                        d_318_rest_ = (d_317_valueOrError1_).Extract()
                        return Std_Wrappers.Result_Success(((d_316_first_) + (sep)) + (d_318_rest_))

    @staticmethod
    def Object(obj):
        d_319_valueOrError0_ = default__.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))), _dafny.SeqWithoutIsStrInference([default__.KeyValue((obj)[d_320_i_]) for d_320_i_ in range(len(obj))]))
        if (d_319_valueOrError0_).IsFailure():
            return (d_319_valueOrError0_).PropagateFailure()
        elif True:
            d_321_middle_ = (d_319_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "{")))) + (d_321_middle_)) + (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "}")))))

    @staticmethod
    def Array(arr):
        d_322_valueOrError0_ = default__.Join(Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ","))), _dafny.SeqWithoutIsStrInference([default__.JSON((arr)[d_323_i_]) for d_323_i_ in range(len(arr))]))
        if (d_322_valueOrError0_).IsFailure():
            return (d_322_valueOrError0_).PropagateFailure()
        elif True:
            d_324_middle_ = (d_322_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "[")))) + (d_324_middle_)) + (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "]")))))

    @staticmethod
    def JSON(js):
        source12_ = js
        if source12_.is_Null:
            return Std_Wrappers.Result_Success(Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "null"))))
        elif source12_.is_Bool:
            d_325___mcc_h0_ = source12_.b
            d_326_b_ = d_325___mcc_h0_
            return Std_Wrappers.Result_Success((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "true"))) if d_326_b_ else Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ASCIIToUTF8(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "false")))))
        elif source12_.is_String:
            d_327___mcc_h1_ = source12_.str
            d_328_str_ = d_327___mcc_h1_
            return default__.String(d_328_str_)
        elif source12_.is_Number:
            d_329___mcc_h2_ = source12_.num
            d_330_dec_ = d_329___mcc_h2_
            return default__.Number(d_330_dec_)
        elif source12_.is_Object:
            d_331___mcc_h3_ = source12_.obj
            d_332_obj_ = d_331___mcc_h3_
            return default__.Object(d_332_obj_)
        elif True:
            d_333___mcc_h4_ = source12_.arr
            d_334_arr_ = d_333___mcc_h4_
            return default__.Array(d_334_arr_)

