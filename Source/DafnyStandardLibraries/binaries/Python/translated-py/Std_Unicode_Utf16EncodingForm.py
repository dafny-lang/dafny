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

# Module: Std_Unicode_Utf16EncodingForm

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsMinimalWellFormedCodeUnitSubsequence(s):
        if (len(s)) == (1):
            return default__.IsWellFormedSingleCodeUnitSequence(s)
        elif (len(s)) == (2):
            d_227_b_ = default__.IsWellFormedDoubleCodeUnitSequence(s)
            return d_227_b_
        elif True:
            return False

    @staticmethod
    def IsWellFormedSingleCodeUnitSequence(s):
        d_228_firstWord_ = (s)[0]
        return (((0) <= (d_228_firstWord_)) and ((d_228_firstWord_) <= (55295))) or (((57344) <= (d_228_firstWord_)) and ((d_228_firstWord_) <= (65535)))

    @staticmethod
    def IsWellFormedDoubleCodeUnitSequence(s):
        d_229_firstWord_ = (s)[0]
        d_230_secondWord_ = (s)[1]
        return (((55296) <= (d_229_firstWord_)) and ((d_229_firstWord_) <= (56319))) and (((56320) <= (d_230_secondWord_)) and ((d_230_secondWord_) <= (57343)))

    @staticmethod
    def SplitPrefixMinimalWellFormedCodeUnitSubsequence(s):
        if ((len(s)) >= (1)) and (default__.IsWellFormedSingleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:1:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:1:]))
        elif ((len(s)) >= (2)) and (default__.IsWellFormedDoubleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:2:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:2:]))
        elif True:
            return Std_Wrappers.Option_None()

    @staticmethod
    def EncodeScalarValue(v):
        if (((0) <= (v)) and ((v) <= (55295))) or (((57344) <= (v)) and ((v) <= (65535))):
            return default__.EncodeScalarValueSingleWord(v)
        elif True:
            return default__.EncodeScalarValueDoubleWord(v)

    @staticmethod
    def EncodeScalarValueSingleWord(v):
        d_231_firstWord_ = v
        return _dafny.SeqWithoutIsStrInference([d_231_firstWord_])

    @staticmethod
    def EncodeScalarValueDoubleWord(v):
        d_232_x2_ = (v) & (1023)
        d_233_x1_ = ((v) & (64512)) >> (10)
        d_234_u_ = ((v) & (2031616)) >> (16)
        d_235_w_ = ((d_234_u_) - (1)) & ((1 << 5) - 1)
        d_236_firstWord_ = ((55296) | (((d_235_w_) << (6)) & ((1 << 16) - 1))) | (d_233_x1_)
        d_237_secondWord_ = (56320) | (d_232_x2_)
        return _dafny.SeqWithoutIsStrInference([d_236_firstWord_, d_237_secondWord_])

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequence(m):
        if (len(m)) == (1):
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
        elif True:
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m):
        d_238_firstWord_ = (m)[0]
        d_239_x_ = d_238_firstWord_
        return d_239_x_

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m):
        d_240_firstWord_ = (m)[0]
        d_241_secondWord_ = (m)[1]
        d_242_x2_ = (d_241_secondWord_) & (1023)
        d_243_x1_ = (d_240_firstWord_) & (63)
        d_244_w_ = ((d_240_firstWord_) & (960)) >> (6)
        d_245_u_ = ((d_244_w_) + (1)) & ((1 << 24) - 1)
        d_246_v_ = ((((d_245_u_) << (16)) & ((1 << 24) - 1)) | (((d_243_x1_) << (10)) & ((1 << 24) - 1))) | (d_242_x2_)
        return d_246_v_

    @staticmethod
    def PartitionCodeUnitSequenceChecked(s):
        maybeParts: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        if (s) == (_dafny.SeqWithoutIsStrInference([])):
            maybeParts = Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference([]))
            return maybeParts
        d_247_result_: _dafny.Seq
        d_247_result_ = _dafny.SeqWithoutIsStrInference([])
        d_248_rest_: _dafny.Seq
        d_248_rest_ = s
        while (len(d_248_rest_)) > (0):
            d_249_prefix_: _dafny.Seq
            d_250_valueOrError0_: Std_Wrappers.Option = Std_Wrappers.Option.default()()
            d_250_valueOrError0_ = default__.SplitPrefixMinimalWellFormedCodeUnitSubsequence(d_248_rest_)
            if (d_250_valueOrError0_).IsFailure():
                maybeParts = (d_250_valueOrError0_).PropagateFailure()
                return maybeParts
            d_249_prefix_ = (d_250_valueOrError0_).Extract()
            d_247_result_ = (d_247_result_) + (_dafny.SeqWithoutIsStrInference([d_249_prefix_]))
            d_248_rest_ = _dafny.SeqWithoutIsStrInference((d_248_rest_)[len(d_249_prefix_)::])
        maybeParts = Std_Wrappers.Option_Some(d_247_result_)
        return maybeParts
        return maybeParts

    @staticmethod
    def PartitionCodeUnitSequence(s):
        return (default__.PartitionCodeUnitSequenceChecked(s)).Extract()

    @staticmethod
    def IsWellFormedCodeUnitSequence(s):
        return (default__.PartitionCodeUnitSequenceChecked(s)).is_Some

    @staticmethod
    def EncodeScalarSequence(vs):
        s: _dafny.Seq = WellFormedCodeUnitSeq.default()
        s = _dafny.SeqWithoutIsStrInference([])
        lo1_ = 0
        for d_251_i_ in range(len(vs)-1, lo1_-1, -1):
            d_252_next_: _dafny.Seq
            d_252_next_ = default__.EncodeScalarValue((vs)[d_251_i_])
            s = (d_252_next_) + (s)
        return s

    @staticmethod
    def DecodeCodeUnitSequence(s):
        d_253_parts_ = default__.PartitionCodeUnitSequence(s)
        d_254_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_253_parts_)
        return d_254_vs_

    @staticmethod
    def DecodeCodeUnitSequenceChecked(s):
        maybeVs: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        d_255_maybeParts_: Std_Wrappers.Option
        d_255_maybeParts_ = default__.PartitionCodeUnitSequenceChecked(s)
        if (d_255_maybeParts_).is_None:
            maybeVs = Std_Wrappers.Option_None()
            return maybeVs
        d_256_parts_: _dafny.Seq
        d_256_parts_ = (d_255_maybeParts_).value
        d_257_vs_: _dafny.Seq
        d_257_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_256_parts_)
        maybeVs = Std_Wrappers.Option_Some(d_257_vs_)
        return maybeVs
        return maybeVs


class WellFormedCodeUnitSeq:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.SeqWithoutIsStrInference([])

class MinimalWellFormedCodeUnitSeq:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})
