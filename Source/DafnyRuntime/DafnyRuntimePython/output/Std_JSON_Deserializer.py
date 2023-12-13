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
import Std_Unicode_UnicodeStringsWithUnicodeChar
import Std_Unicode_Utf8EncodingScheme
import Std_Unicode
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

# Module: Std_JSON_Deserializer

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Bool(js):
        return ((js).At(0)) == (ord(_dafny.CodePoint('t')))

    @staticmethod
    def UnsupportedEscape16(code):
        return Std_JSON_Errors.DeserializationError_UnsupportedEscape((Std_Unicode_UnicodeStringsWithUnicodeChar.default__.FromUTF16Checked(code)).GetOr(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Couldn't decode UTF-16"))))

    @staticmethod
    def ToNat16(str):
        d_471_hd_ = Std_JSON_Deserializer_Uint16StrConversion.default__.ToNat(str)
        return d_471_hd_

    @staticmethod
    def Unescape(str, start, prefix):
        while True:
            with _dafny.label():
                if (start) >= (len(str)):
                    return Std_Wrappers.Result_Success(prefix)
                elif ((str)[start]) == (ord(_dafny.CodePoint('\\'))):
                    if (len(str)) == ((start) + (1)):
                        return Std_Wrappers.Result_Failure(Std_JSON_Errors.DeserializationError_EscapeAtEOS())
                    elif True:
                        d_472_c_ = (str)[(start) + (1)]
                        if (d_472_c_) == (ord(_dafny.CodePoint('u'))):
                            if (len(str)) <= ((start) + (6)):
                                return Std_Wrappers.Result_Failure(Std_JSON_Errors.DeserializationError_EscapeAtEOS())
                            elif True:
                                d_473_code_ = _dafny.SeqWithoutIsStrInference((str)[(start) + (2):(start) + (6):])
                                def lambda30_(exists_var_0_):
                                    d_474_c_: int = exists_var_0_
                                    return ((d_474_c_) in (d_473_code_)) and ((d_474_c_) not in (default__.HEX__TABLE__16))

                                if _dafny.quantifier((d_473_code_).UniqueElements, False, lambda30_):
                                    return Std_Wrappers.Result_Failure(default__.UnsupportedEscape16(d_473_code_))
                                elif True:
                                    d_475_hd_ = default__.ToNat16(d_473_code_)
                                    in86_ = str
                                    in87_ = (start) + (6)
                                    in88_ = (prefix) + (_dafny.SeqWithoutIsStrInference([d_475_hd_]))
                                    str = in86_
                                    start = in87_
                                    prefix = in88_
                                    raise _dafny.TailCall()
                        elif True:
                            d_476_unescaped_ = (34 if (d_472_c_) == (34) else (92 if (d_472_c_) == (92) else (8 if (d_472_c_) == (98) else (12 if (d_472_c_) == (102) else (10 if (d_472_c_) == (110) else (13 if (d_472_c_) == (114) else (9 if (d_472_c_) == (116) else 0)))))))
                            if (d_476_unescaped_) == (0):
                                return Std_Wrappers.Result_Failure(default__.UnsupportedEscape16(_dafny.SeqWithoutIsStrInference((str)[start:(start) + (2):])))
                            elif True:
                                in89_ = str
                                in90_ = (start) + (2)
                                in91_ = (prefix) + (_dafny.SeqWithoutIsStrInference([d_476_unescaped_]))
                                str = in89_
                                start = in90_
                                prefix = in91_
                                raise _dafny.TailCall()
                elif True:
                    in92_ = str
                    in93_ = (start) + (1)
                    in94_ = (prefix) + (_dafny.SeqWithoutIsStrInference([(str)[start]]))
                    str = in92_
                    start = in93_
                    prefix = in94_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def String(js):
        d_477_valueOrError0_ = (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.FromUTF8Checked(((js).contents).Bytes())).ToResult(Std_JSON_Errors.DeserializationError_InvalidUnicode())
        if (d_477_valueOrError0_).IsFailure():
            return (d_477_valueOrError0_).PropagateFailure()
        elif True:
            d_478_asUtf32_ = (d_477_valueOrError0_).Extract()
            d_479_valueOrError1_ = (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.ToUTF16Checked(d_478_asUtf32_)).ToResult(Std_JSON_Errors.DeserializationError_InvalidUnicode())
            if (d_479_valueOrError1_).IsFailure():
                return (d_479_valueOrError1_).PropagateFailure()
            elif True:
                d_480_asUint16_ = (d_479_valueOrError1_).Extract()
                d_481_valueOrError2_ = default__.Unescape(d_480_asUint16_, 0, _dafny.SeqWithoutIsStrInference([]))
                if (d_481_valueOrError2_).IsFailure():
                    return (d_481_valueOrError2_).PropagateFailure()
                elif True:
                    d_482_unescaped_ = (d_481_valueOrError2_).Extract()
                    return (Std_Unicode_UnicodeStringsWithUnicodeChar.default__.FromUTF16Checked(d_482_unescaped_)).ToResult(Std_JSON_Errors.DeserializationError_InvalidUnicode())

    @staticmethod
    def ToInt(sign, n):
        d_483_n_ = Std_JSON_ByteStrConversion.default__.ToNat((n).Bytes())
        return Std_Wrappers.Result_Success(((0) - (d_483_n_) if (sign).Char_q(_dafny.CodePoint('-')) else d_483_n_))

    @staticmethod
    def Number(js):
        let_tmp_rhs17_ = js
        d_484_minus_ = let_tmp_rhs17_.minus
        d_485_num_ = let_tmp_rhs17_.num
        d_486_frac_ = let_tmp_rhs17_.frac
        d_487_exp_ = let_tmp_rhs17_.exp
        d_488_valueOrError0_ = default__.ToInt(d_484_minus_, d_485_num_)
        if (d_488_valueOrError0_).IsFailure():
            return (d_488_valueOrError0_).PropagateFailure()
        elif True:
            d_489_n_ = (d_488_valueOrError0_).Extract()
            def lambda31_(source17_):
                if source17_.is_Empty:
                    return Std_Wrappers.Result_Success(0)
                elif True:
                    d_491___mcc_h0_ = source17_.t
                    source18_ = d_491___mcc_h0_
                    d_492___mcc_h1_ = source18_.e
                    d_493___mcc_h2_ = source18_.sign
                    d_494___mcc_h3_ = source18_.num
                    d_495_num_ = d_494___mcc_h3_
                    d_496_sign_ = d_493___mcc_h2_
                    return default__.ToInt(d_496_sign_, d_495_num_)

            d_490_valueOrError1_ = lambda31_(d_487_exp_)
            if (d_490_valueOrError1_).IsFailure():
                return (d_490_valueOrError1_).PropagateFailure()
            elif True:
                d_497_e10_ = (d_490_valueOrError1_).Extract()
                source19_ = d_486_frac_
                if source19_.is_Empty:
                    return Std_Wrappers.Result_Success(Std_JSON_Values.Decimal_Decimal(d_489_n_, d_497_e10_))
                elif True:
                    d_498___mcc_h4_ = source19_.t
                    source20_ = d_498___mcc_h4_
                    d_499___mcc_h5_ = source20_.period
                    d_500___mcc_h6_ = source20_.num
                    d_501_num_ = d_500___mcc_h6_
                    d_502_pow10_ = (d_501_num_).Length()
                    d_503_valueOrError2_ = default__.ToInt(d_484_minus_, d_501_num_)
                    if (d_503_valueOrError2_).IsFailure():
                        return (d_503_valueOrError2_).PropagateFailure()
                    elif True:
                        d_504_frac_ = (d_503_valueOrError2_).Extract()
                        return Std_Wrappers.Result_Success(Std_JSON_Values.Decimal_Decimal(((d_489_n_) * (Std_Arithmetic_Power.default__.Pow(10, d_502_pow10_))) + (d_504_frac_), (d_497_e10_) - (d_502_pow10_)))

    @staticmethod
    def KeyValue(js):
        d_505_valueOrError0_ = default__.String((js).k)
        if (d_505_valueOrError0_).IsFailure():
            return (d_505_valueOrError0_).PropagateFailure()
        elif True:
            d_506_k_ = (d_505_valueOrError0_).Extract()
            d_507_valueOrError1_ = default__.Value((js).v)
            if (d_507_valueOrError1_).IsFailure():
                return (d_507_valueOrError1_).PropagateFailure()
            elif True:
                d_508_v_ = (d_507_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success((d_506_k_, d_508_v_))

    @staticmethod
    def Object(js):
        def lambda32_(d_509_js_):
            def lambda33_(d_510_d_):
                return default__.KeyValue((d_510_d_).t)

            return lambda33_

        return Std_Collections_Seq.default__.MapWithResult(lambda32_(js), (js).data)

    @staticmethod
    def Array(js):
        def lambda34_(d_511_js_):
            def lambda35_(d_512_d_):
                return default__.Value((d_512_d_).t)

            return lambda35_

        return Std_Collections_Seq.default__.MapWithResult(lambda34_(js), (js).data)

    @staticmethod
    def Value(js):
        source21_ = js
        if source21_.is_Null:
            d_513___mcc_h0_ = source21_.n
            return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_Null())
        elif source21_.is_Bool:
            d_514___mcc_h1_ = source21_.b
            d_515_b_ = d_514___mcc_h1_
            return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_Bool(default__.Bool(d_515_b_)))
        elif source21_.is_String:
            d_516___mcc_h2_ = source21_.str
            d_517_str_ = d_516___mcc_h2_
            d_518_valueOrError0_ = default__.String(d_517_str_)
            if (d_518_valueOrError0_).IsFailure():
                return (d_518_valueOrError0_).PropagateFailure()
            elif True:
                d_519_s_ = (d_518_valueOrError0_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_String(d_519_s_))
        elif source21_.is_Number:
            d_520___mcc_h3_ = source21_.num
            d_521_dec_ = d_520___mcc_h3_
            d_522_valueOrError1_ = default__.Number(d_521_dec_)
            if (d_522_valueOrError1_).IsFailure():
                return (d_522_valueOrError1_).PropagateFailure()
            elif True:
                d_523_n_ = (d_522_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_Number(d_523_n_))
        elif source21_.is_Object:
            d_524___mcc_h4_ = source21_.obj
            d_525_obj_ = d_524___mcc_h4_
            d_526_valueOrError2_ = default__.Object(d_525_obj_)
            if (d_526_valueOrError2_).IsFailure():
                return (d_526_valueOrError2_).PropagateFailure()
            elif True:
                d_527_o_ = (d_526_valueOrError2_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_Object(d_527_o_))
        elif True:
            d_528___mcc_h5_ = source21_.arr
            d_529_arr_ = d_528___mcc_h5_
            d_530_valueOrError3_ = default__.Array(d_529_arr_)
            if (d_530_valueOrError3_).IsFailure():
                return (d_530_valueOrError3_).PropagateFailure()
            elif True:
                d_531_a_ = (d_530_valueOrError3_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Values.JSON_Array(d_531_a_))

    @staticmethod
    def JSON(js):
        return default__.Value((js).t)

    @_dafny.classproperty
    def HEX__TABLE__16(instance):
        return Std_JSON_Deserializer_Uint16StrConversion.default__.charToDigit
    @_dafny.classproperty
    def DIGITS(instance):
        return Std_JSON_ByteStrConversion.default__.charToDigit
    @_dafny.classproperty
    def MINUS(instance):
        return ord(_dafny.CodePoint('-'))
