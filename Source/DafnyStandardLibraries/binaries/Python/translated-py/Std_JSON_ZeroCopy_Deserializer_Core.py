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

# Module: Std_JSON_ZeroCopy_Deserializer_Core

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Get(cs, err):
        d_587_valueOrError0_ = (cs).Get(err)
        if (d_587_valueOrError0_).IsFailure():
            return (d_587_valueOrError0_).PropagateFailure()
        elif True:
            d_588_cs_ = (d_587_valueOrError0_).Extract()
            return Std_Wrappers.Result_Success((d_588_cs_).Split())

    @staticmethod
    def WS(cs):
        sp: Std_JSON_Utils_Cursors.Split = Std_JSON_Utils_Cursors.Split.default(Std_JSON_Grammar.jblanks.default)()
        d_589_point_k_: int
        d_589_point_k_ = (cs).point
        d_590_end_: int
        d_590_end_ = (cs).end
        while ((d_589_point_k_) < (d_590_end_)) and (Std_JSON_Grammar.default__.Blank_q(((cs).s)[d_589_point_k_])):
            d_589_point_k_ = (d_589_point_k_) + (1)
        sp = (Std_JSON_Utils_Cursors.Cursor___Cursor((cs).s, (cs).beg, d_589_point_k_, (cs).end)).Split()
        return sp
        return sp

    @staticmethod
    def Structural(cs, parser):
        let_tmp_rhs18_ = default__.WS(cs)
        d_591_before_ = let_tmp_rhs18_.t
        d_592_cs_ = let_tmp_rhs18_.cs
        d_593_valueOrError0_ = (parser)(d_592_cs_)
        if (d_593_valueOrError0_).IsFailure():
            return (d_593_valueOrError0_).PropagateFailure()
        elif True:
            let_tmp_rhs19_ = (d_593_valueOrError0_).Extract()
            d_594_val_ = let_tmp_rhs19_.t
            d_595_cs_ = let_tmp_rhs19_.cs
            let_tmp_rhs20_ = default__.WS(d_595_cs_)
            d_596_after_ = let_tmp_rhs20_.t
            d_597_cs_ = let_tmp_rhs20_.cs
            return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Structural_Structural(d_591_before_, d_594_val_, d_596_after_), d_597_cs_))

    @staticmethod
    def TryStructural(cs):
        let_tmp_rhs21_ = default__.WS(cs)
        d_598_before_ = let_tmp_rhs21_.t
        d_599_cs_ = let_tmp_rhs21_.cs
        let_tmp_rhs22_ = ((d_599_cs_).SkipByte()).Split()
        d_600_val_ = let_tmp_rhs22_.t
        d_601_cs_ = let_tmp_rhs22_.cs
        let_tmp_rhs23_ = default__.WS(d_601_cs_)
        d_602_after_ = let_tmp_rhs23_.t
        d_603_cs_ = let_tmp_rhs23_.cs
        return Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Structural_Structural(d_598_before_, d_600_val_, d_602_after_), d_603_cs_)

    @_dafny.classproperty
    def SpecView(instance):
        def lambda42_(d_604_v_):
            return Std_JSON_ConcreteSyntax_Spec.default__.View(d_604_v_)

        return lambda42_

class jopt:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([]))

class ValueParser:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Parsers.SubParser.default()
