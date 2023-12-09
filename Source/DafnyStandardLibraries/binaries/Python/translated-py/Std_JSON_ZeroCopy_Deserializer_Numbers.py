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

# Module: Std_JSON_ZeroCopy_Deserializer_Numbers

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Digits(cs):
        return ((cs).SkipWhile(Std_JSON_Grammar.default__.Digit_q)).Split()

    @staticmethod
    def NonEmptyDigits(cs):
        d_620_sp_ = default__.Digits(cs)
        if ((d_620_sp_).t).Empty_q:
            return Std_Wrappers.Result_Failure(Std_JSON_Utils_Cursors.CursorError_OtherError(Std_JSON_Errors.DeserializationError_EmptyNumber()))
        elif True:
            return Std_Wrappers.Result_Success(d_620_sp_)

    @staticmethod
    def NonZeroInt(cs):
        return default__.NonEmptyDigits(cs)

    @staticmethod
    def OptionalMinus(cs):
        def lambda43_(d_621_c_):
            return (d_621_c_) == (ord(_dafny.CodePoint('-')))

        return ((cs).SkipIf(lambda43_)).Split()

    @staticmethod
    def OptionalSign(cs):
        def lambda44_(d_622_c_):
            return ((d_622_c_) == (ord(_dafny.CodePoint('-')))) or ((d_622_c_) == (ord(_dafny.CodePoint('+'))))

        return ((cs).SkipIf(lambda44_)).Split()

    @staticmethod
    def TrimmedInt(cs):
        def lambda45_(d_624_c_):
            return (d_624_c_) == (ord(_dafny.CodePoint('0')))

        d_623_sp_ = ((cs).SkipIf(lambda45_)).Split()
        if ((d_623_sp_).t).Empty_q:
            return default__.NonZeroInt((d_623_sp_).cs)
        elif True:
            return Std_Wrappers.Result_Success(d_623_sp_)

    @staticmethod
    def Exp(cs):
        def lambda46_(d_625_c_):
            return ((d_625_c_) == (ord(_dafny.CodePoint('e')))) or ((d_625_c_) == (ord(_dafny.CodePoint('E'))))

        let_tmp_rhs27_ = ((cs).SkipIf(lambda46_)).Split()
        d_626_e_ = let_tmp_rhs27_.t
        d_627_cs_ = let_tmp_rhs27_.cs
        if (d_626_e_).Empty_q:
            return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Maybe_Empty(), d_627_cs_))
        elif True:
            let_tmp_rhs28_ = default__.OptionalSign(d_627_cs_)
            d_628_sign_ = let_tmp_rhs28_.t
            d_629_cs_ = let_tmp_rhs28_.cs
            d_630_valueOrError0_ = default__.NonEmptyDigits(d_629_cs_)
            if (d_630_valueOrError0_).IsFailure():
                return (d_630_valueOrError0_).PropagateFailure()
            elif True:
                let_tmp_rhs29_ = (d_630_valueOrError0_).Extract()
                d_631_num_ = let_tmp_rhs29_.t
                d_632_cs_ = let_tmp_rhs29_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Maybe_NonEmpty(Std_JSON_Grammar.jexp_JExp(d_626_e_, d_628_sign_, d_631_num_)), d_632_cs_))

    @staticmethod
    def Frac(cs):
        def lambda47_(d_633_c_):
            return (d_633_c_) == (ord(_dafny.CodePoint('.')))

        let_tmp_rhs30_ = ((cs).SkipIf(lambda47_)).Split()
        d_634_period_ = let_tmp_rhs30_.t
        d_635_cs_ = let_tmp_rhs30_.cs
        if (d_634_period_).Empty_q:
            return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Maybe_Empty(), d_635_cs_))
        elif True:
            d_636_valueOrError0_ = default__.NonEmptyDigits(d_635_cs_)
            if (d_636_valueOrError0_).IsFailure():
                return (d_636_valueOrError0_).PropagateFailure()
            elif True:
                let_tmp_rhs31_ = (d_636_valueOrError0_).Extract()
                d_637_num_ = let_tmp_rhs31_.t
                d_638_cs_ = let_tmp_rhs31_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Maybe_NonEmpty(Std_JSON_Grammar.jfrac_JFrac(d_634_period_, d_637_num_)), d_638_cs_))

    @staticmethod
    def NumberFromParts(minus, num, frac, exp):
        d_639_sp_ = Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.jnumber_JNumber((minus).t, (num).t, (frac).t, (exp).t), (exp).cs)
        return d_639_sp_

    @staticmethod
    def Number(cs):
        d_640_minus_ = default__.OptionalMinus(cs)
        d_641_valueOrError0_ = default__.TrimmedInt((d_640_minus_).cs)
        if (d_641_valueOrError0_).IsFailure():
            return (d_641_valueOrError0_).PropagateFailure()
        elif True:
            d_642_num_ = (d_641_valueOrError0_).Extract()
            d_643_valueOrError1_ = default__.Frac((d_642_num_).cs)
            if (d_643_valueOrError1_).IsFailure():
                return (d_643_valueOrError1_).PropagateFailure()
            elif True:
                d_644_frac_ = (d_643_valueOrError1_).Extract()
                d_645_valueOrError2_ = default__.Exp((d_644_frac_).cs)
                if (d_645_valueOrError2_).IsFailure():
                    return (d_645_valueOrError2_).PropagateFailure()
                elif True:
                    d_646_exp_ = (d_645_valueOrError2_).Extract()
                    return Std_Wrappers.Result_Success(default__.NumberFromParts(d_640_minus_, d_642_num_, d_644_frac_, d_646_exp_))

