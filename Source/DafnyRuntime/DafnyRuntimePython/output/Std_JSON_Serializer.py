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

# Module: Std_JSON_Serializer

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Bool(b):
        return Std_JSON_Utils_Views_Core.View__.OfBytes((Std_JSON_Grammar.default__.TRUE if b else Std_JSON_Grammar.default__.FALSE))

    @staticmethod
    def CheckLength(s, err):
        return Std_Wrappers.Outcome.Need((len(s)) < (Std_BoundedInts.default__.TWO__TO__THE__32), err)

    @staticmethod
    def String(str):
        d_407_valueOrError0_ = Std_JSON_Spec.default__.EscapeToUTF8(str, 0)
        if (d_407_valueOrError0_).IsFailure():
            return (d_407_valueOrError0_).PropagateFailure()
        elif True:
            d_408_bs_ = (d_407_valueOrError0_).Extract()
            d_409_o_ = default__.CheckLength(d_408_bs_, Std_JSON_Errors.SerializationError_StringTooLong(str))
            if (d_409_o_).is_Pass:
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.jstring_JString(Std_JSON_Grammar.default__.DOUBLEQUOTE, Std_JSON_Utils_Views_Core.View__.OfBytes(d_408_bs_), Std_JSON_Grammar.default__.DOUBLEQUOTE))
            elif True:
                return Std_Wrappers.Result_Failure((d_409_o_).error)

    @staticmethod
    def Sign(n):
        return Std_JSON_Utils_Views_Core.View__.OfBytes((_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('-'))]) if (n) < (0) else _dafny.SeqWithoutIsStrInference([])))

    @staticmethod
    def Int_k(n):
        return Std_JSON_ByteStrConversion.default__.OfInt(n, default__.MINUS)

    @staticmethod
    def Int(n):
        d_410_bs_ = default__.Int_k(n)
        d_411_o_ = default__.CheckLength(d_410_bs_, Std_JSON_Errors.SerializationError_IntTooLarge(n))
        if (d_411_o_).is_Pass:
            return Std_Wrappers.Result_Success(Std_JSON_Utils_Views_Core.View__.OfBytes(d_410_bs_))
        elif True:
            return Std_Wrappers.Result_Failure((d_411_o_).error)

    @staticmethod
    def Number(dec):
        pat_let_tv2_ = dec
        pat_let_tv3_ = dec
        d_412_minus_ = default__.Sign((dec).n)
        d_413_valueOrError0_ = default__.Int(Std_Math.default__.Abs((dec).n))
        if (d_413_valueOrError0_).IsFailure():
            return (d_413_valueOrError0_).PropagateFailure()
        elif True:
            d_414_num_ = (d_413_valueOrError0_).Extract()
            d_415_frac_ = Std_JSON_Grammar.Maybe_Empty()
            def iife9_(_pat_let2_0):
                def iife10_(d_417_e_):
                    def iife11_(_pat_let3_0):
                        def iife12_(d_418_sign_):
                            def iife13_(_pat_let4_0):
                                def iife14_(d_419_valueOrError2_):
                                    def iife15_(_pat_let5_0):
                                        def iife16_(d_420_num_):
                                            return Std_Wrappers.Result_Success(Std_JSON_Grammar.Maybe_NonEmpty(Std_JSON_Grammar.jexp_JExp(d_417_e_, d_418_sign_, d_420_num_)))
                                        return iife16_(_pat_let5_0)
                                    return ((d_419_valueOrError2_).PropagateFailure() if (d_419_valueOrError2_).IsFailure() else iife15_((d_419_valueOrError2_).Extract()))
                                return iife14_(_pat_let4_0)
                            return iife13_(default__.Int(Std_Math.default__.Abs((pat_let_tv3_).e10)))
                        return iife12_(_pat_let3_0)
                    return iife11_(default__.Sign((pat_let_tv2_).e10))
                return iife10_(_pat_let2_0)
            d_416_valueOrError1_ = (Std_Wrappers.Result_Success(Std_JSON_Grammar.Maybe_Empty()) if ((dec).e10) == (0) else iife9_(Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('e'))]))))
            if (d_416_valueOrError1_).IsFailure():
                return (d_416_valueOrError1_).PropagateFailure()
            elif True:
                d_421_exp_ = (d_416_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.jnumber_JNumber(d_412_minus_, d_414_num_, Std_JSON_Grammar.Maybe_Empty(), d_421_exp_))

    @staticmethod
    def MkStructural(v):
        return Std_JSON_Grammar.Structural_Structural(Std_JSON_Grammar.default__.EMPTY, v, Std_JSON_Grammar.default__.EMPTY)

    @staticmethod
    def KeyValue(kv):
        d_422_valueOrError0_ = default__.String((kv)[0])
        if (d_422_valueOrError0_).IsFailure():
            return (d_422_valueOrError0_).PropagateFailure()
        elif True:
            d_423_k_ = (d_422_valueOrError0_).Extract()
            d_424_valueOrError1_ = default__.Value((kv)[1])
            if (d_424_valueOrError1_).IsFailure():
                return (d_424_valueOrError1_).PropagateFailure()
            elif True:
                d_425_v_ = (d_424_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.jKeyValue_KeyValue(d_423_k_, default__.COLON, d_425_v_))

    @staticmethod
    def MkSuffixedSequence(ds, suffix, start):
        d_426___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (start) >= (len(ds)):
                    return (d_426___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif (start) == ((len(ds)) - (1)):
                    return (d_426___accumulator_) + (_dafny.SeqWithoutIsStrInference([Std_JSON_Grammar.Suffixed_Suffixed((ds)[start], Std_JSON_Grammar.Maybe_Empty())]))
                elif True:
                    d_426___accumulator_ = (d_426___accumulator_) + (_dafny.SeqWithoutIsStrInference([Std_JSON_Grammar.Suffixed_Suffixed((ds)[start], Std_JSON_Grammar.Maybe_NonEmpty(suffix))]))
                    in78_ = ds
                    in79_ = suffix
                    in80_ = (start) + (1)
                    ds = in78_
                    suffix = in79_
                    start = in80_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Object(obj):
        def lambda25_(d_428_obj_):
            def lambda26_(d_429_v_):
                return default__.KeyValue(d_429_v_)

            return lambda26_

        d_427_valueOrError0_ = Std_Collections_Seq.default__.MapWithResult(lambda25_(obj), obj)
        if (d_427_valueOrError0_).IsFailure():
            return (d_427_valueOrError0_).PropagateFailure()
        elif True:
            d_430_items_ = (d_427_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(Std_JSON_Grammar.Bracketed_Bracketed(default__.MkStructural(Std_JSON_Grammar.default__.LBRACE), default__.MkSuffixedSequence(d_430_items_, default__.COMMA, 0), default__.MkStructural(Std_JSON_Grammar.default__.RBRACE)))

    @staticmethod
    def Array(arr):
        def lambda27_(d_432_arr_):
            def lambda28_(d_433_v_):
                return default__.Value(d_433_v_)

            return lambda28_

        d_431_valueOrError0_ = Std_Collections_Seq.default__.MapWithResult(lambda27_(arr), arr)
        if (d_431_valueOrError0_).IsFailure():
            return (d_431_valueOrError0_).PropagateFailure()
        elif True:
            d_434_items_ = (d_431_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(Std_JSON_Grammar.Bracketed_Bracketed(default__.MkStructural(Std_JSON_Grammar.default__.LBRACKET), default__.MkSuffixedSequence(d_434_items_, default__.COMMA, 0), default__.MkStructural(Std_JSON_Grammar.default__.RBRACKET)))

    @staticmethod
    def Value(js):
        source16_ = js
        if source16_.is_Null:
            return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_Null(Std_JSON_Utils_Views_Core.View__.OfBytes(Std_JSON_Grammar.default__.NULL)))
        elif source16_.is_Bool:
            d_435___mcc_h0_ = source16_.b
            d_436_b_ = d_435___mcc_h0_
            return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_Bool(default__.Bool(d_436_b_)))
        elif source16_.is_String:
            d_437___mcc_h1_ = source16_.str
            d_438_str_ = d_437___mcc_h1_
            d_439_valueOrError0_ = default__.String(d_438_str_)
            if (d_439_valueOrError0_).IsFailure():
                return (d_439_valueOrError0_).PropagateFailure()
            elif True:
                d_440_s_ = (d_439_valueOrError0_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_String(d_440_s_))
        elif source16_.is_Number:
            d_441___mcc_h2_ = source16_.num
            d_442_dec_ = d_441___mcc_h2_
            d_443_valueOrError1_ = default__.Number(d_442_dec_)
            if (d_443_valueOrError1_).IsFailure():
                return (d_443_valueOrError1_).PropagateFailure()
            elif True:
                d_444_n_ = (d_443_valueOrError1_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_Number(d_444_n_))
        elif source16_.is_Object:
            d_445___mcc_h3_ = source16_.obj
            d_446_obj_ = d_445___mcc_h3_
            d_447_valueOrError2_ = default__.Object(d_446_obj_)
            if (d_447_valueOrError2_).IsFailure():
                return (d_447_valueOrError2_).PropagateFailure()
            elif True:
                d_448_o_ = (d_447_valueOrError2_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_Object(d_448_o_))
        elif True:
            d_449___mcc_h4_ = source16_.arr
            d_450_arr_ = d_449___mcc_h4_
            d_451_valueOrError3_ = default__.Array(d_450_arr_)
            if (d_451_valueOrError3_).IsFailure():
                return (d_451_valueOrError3_).PropagateFailure()
            elif True:
                d_452_a_ = (d_451_valueOrError3_).Extract()
                return Std_Wrappers.Result_Success(Std_JSON_Grammar.Value_Array(d_452_a_))

    @staticmethod
    def JSON(js):
        d_453_valueOrError0_ = default__.Value(js)
        if (d_453_valueOrError0_).IsFailure():
            return (d_453_valueOrError0_).PropagateFailure()
        elif True:
            d_454_val_ = (d_453_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success(default__.MkStructural(d_454_val_))

    @_dafny.classproperty
    def DIGITS(instance):
        return Std_JSON_ByteStrConversion.default__.chars
    @_dafny.classproperty
    def MINUS(instance):
        return ord(_dafny.CodePoint('-'))
    @_dafny.classproperty
    def COLON(instance):
        return default__.MkStructural(Std_JSON_Grammar.default__.COLON)
    @_dafny.classproperty
    def COMMA(instance):
        return default__.MkStructural(Std_JSON_Grammar.default__.COMMA)

class bytes32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class string32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})
