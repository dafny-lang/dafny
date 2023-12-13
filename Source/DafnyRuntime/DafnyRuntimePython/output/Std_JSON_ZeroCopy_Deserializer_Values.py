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

# Module: Std_JSON_ZeroCopy_Deserializer_Values

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Value(cs):
        d_724_c_ = (cs).Peek()
        if (d_724_c_) == (ord(_dafny.CodePoint('{'))):
            d_725_valueOrError0_ = Std_JSON_ZeroCopy_Deserializer_Objects.default__.Object(cs, default__.ValueParser(cs))
            if (d_725_valueOrError0_).IsFailure():
                return (d_725_valueOrError0_).PropagateFailure()
            elif True:
                let_tmp_rhs32_ = (d_725_valueOrError0_).Extract()
                d_726_obj_ = let_tmp_rhs32_.t
                d_727_cs_k_ = let_tmp_rhs32_.cs
                d_728_v_ = Std_JSON_Grammar.Value_Object(d_726_obj_)
                d_729_sp_ = Std_JSON_Utils_Cursors.Split_SP(d_728_v_, d_727_cs_k_)
                return Std_Wrappers.Result_Success(d_729_sp_)
        elif (d_724_c_) == (ord(_dafny.CodePoint('['))):
            d_730_valueOrError1_ = Std_JSON_ZeroCopy_Deserializer_Arrays.default__.Array(cs, default__.ValueParser(cs))
            if (d_730_valueOrError1_).IsFailure():
                return (d_730_valueOrError1_).PropagateFailure()
            elif True:
                let_tmp_rhs33_ = (d_730_valueOrError1_).Extract()
                d_731_arr_ = let_tmp_rhs33_.t
                d_732_cs_k_ = let_tmp_rhs33_.cs
                d_733_v_ = Std_JSON_Grammar.Value_Array(d_731_arr_)
                d_734_sp_ = Std_JSON_Utils_Cursors.Split_SP(d_733_v_, d_732_cs_k_)
                return Std_Wrappers.Result_Success(d_734_sp_)
        elif (d_724_c_) == (ord(_dafny.CodePoint('\"'))):
            d_735_valueOrError2_ = Std_JSON_ZeroCopy_Deserializer_Strings.default__.String(cs)
            if (d_735_valueOrError2_).IsFailure():
                return (d_735_valueOrError2_).PropagateFailure()
            elif True:
                let_tmp_rhs34_ = (d_735_valueOrError2_).Extract()
                d_736_str_ = let_tmp_rhs34_.t
                d_737_cs_k_ = let_tmp_rhs34_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Value_String(d_736_str_), d_737_cs_k_))
        elif (d_724_c_) == (ord(_dafny.CodePoint('t'))):
            d_738_valueOrError3_ = Std_JSON_ZeroCopy_Deserializer_Constants.default__.Constant(cs, Std_JSON_Grammar.default__.TRUE)
            if (d_738_valueOrError3_).IsFailure():
                return (d_738_valueOrError3_).PropagateFailure()
            elif True:
                let_tmp_rhs35_ = (d_738_valueOrError3_).Extract()
                d_739_cst_ = let_tmp_rhs35_.t
                d_740_cs_k_ = let_tmp_rhs35_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Value_Bool(d_739_cst_), d_740_cs_k_))
        elif (d_724_c_) == (ord(_dafny.CodePoint('f'))):
            d_741_valueOrError4_ = Std_JSON_ZeroCopy_Deserializer_Constants.default__.Constant(cs, Std_JSON_Grammar.default__.FALSE)
            if (d_741_valueOrError4_).IsFailure():
                return (d_741_valueOrError4_).PropagateFailure()
            elif True:
                let_tmp_rhs36_ = (d_741_valueOrError4_).Extract()
                d_742_cst_ = let_tmp_rhs36_.t
                d_743_cs_k_ = let_tmp_rhs36_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Value_Bool(d_742_cst_), d_743_cs_k_))
        elif (d_724_c_) == (ord(_dafny.CodePoint('n'))):
            d_744_valueOrError5_ = Std_JSON_ZeroCopy_Deserializer_Constants.default__.Constant(cs, Std_JSON_Grammar.default__.NULL)
            if (d_744_valueOrError5_).IsFailure():
                return (d_744_valueOrError5_).PropagateFailure()
            elif True:
                let_tmp_rhs37_ = (d_744_valueOrError5_).Extract()
                d_745_cst_ = let_tmp_rhs37_.t
                d_746_cs_k_ = let_tmp_rhs37_.cs
                return Std_Wrappers.Result_Success(Std_JSON_Utils_Cursors.Split_SP(Std_JSON_Grammar.Value_Null(d_745_cst_), d_746_cs_k_))
        elif True:
            d_747_valueOrError6_ = Std_JSON_ZeroCopy_Deserializer_Numbers.default__.Number(cs)
            if (d_747_valueOrError6_).IsFailure():
                return (d_747_valueOrError6_).PropagateFailure()
            elif True:
                let_tmp_rhs38_ = (d_747_valueOrError6_).Extract()
                d_748_num_ = let_tmp_rhs38_.t
                d_749_cs_k_ = let_tmp_rhs38_.cs
                d_750_v_ = Std_JSON_Grammar.Value_Number(d_748_num_)
                d_751_sp_ = Std_JSON_Utils_Cursors.Split_SP(d_750_v_, d_749_cs_k_)
                return Std_Wrappers.Result_Success(d_751_sp_)

    @staticmethod
    def ValueParser(cs):
        def lambda48_(d_753_cs_):
            def lambda49_(d_754_ps_k_):
                return ((d_754_ps_k_).Length()) < ((d_753_cs_).Length())

            return lambda49_

        d_752_pre_ = lambda48_(cs)
        def lambda50_(d_756_pre_):
            def lambda51_(d_757_ps_k_):
                return default__.Value(d_757_ps_k_)

            return lambda51_

        d_755_fn_ = lambda50_(d_752_pre_)
        return d_755_fn_

