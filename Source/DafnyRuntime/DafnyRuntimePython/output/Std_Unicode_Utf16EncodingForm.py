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

# Module: Std_Unicode_Utf16EncodingForm

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsMinimalWellFormedCodeUnitSubsequence(s):
        if (len(s)) == (1):
            return default__.IsWellFormedSingleCodeUnitSequence(s)
        elif (len(s)) == (2):
            d_235_b_ = default__.IsWellFormedDoubleCodeUnitSequence(s)
            return d_235_b_
        elif True:
            return False

    @staticmethod
    def IsWellFormedSingleCodeUnitSequence(s):
        d_236_firstWord_ = (s)[0]
        return (((0) <= (d_236_firstWord_)) and ((d_236_firstWord_) <= (55295))) or (((57344) <= (d_236_firstWord_)) and ((d_236_firstWord_) <= (65535)))

    @staticmethod
    def IsWellFormedDoubleCodeUnitSequence(s):
        d_237_firstWord_ = (s)[0]
        d_238_secondWord_ = (s)[1]
        return (((55296) <= (d_237_firstWord_)) and ((d_237_firstWord_) <= (56319))) and (((56320) <= (d_238_secondWord_)) and ((d_238_secondWord_) <= (57343)))

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
        d_239_firstWord_ = v
        return _dafny.SeqWithoutIsStrInference([d_239_firstWord_])

    @staticmethod
    def EncodeScalarValueDoubleWord(v):
        d_240_x2_ = (v) & (1023)
        d_241_x1_ = ((v) & (64512)) >> (10)
        d_242_u_ = ((v) & (2031616)) >> (16)
        d_243_w_ = ((d_242_u_) - (1)) & ((1 << 5) - 1)
        d_244_firstWord_ = ((55296) | (((d_243_w_) << (6)) & ((1 << 16) - 1))) | (d_241_x1_)
        d_245_secondWord_ = (56320) | (d_240_x2_)
        return _dafny.SeqWithoutIsStrInference([d_244_firstWord_, d_245_secondWord_])

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequence(m):
        if (len(m)) == (1):
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
        elif True:
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m):
        d_246_firstWord_ = (m)[0]
        d_247_x_ = d_246_firstWord_
        return d_247_x_

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m):
        d_248_firstWord_ = (m)[0]
        d_249_secondWord_ = (m)[1]
        d_250_x2_ = (d_249_secondWord_) & (1023)
        d_251_x1_ = (d_248_firstWord_) & (63)
        d_252_w_ = ((d_248_firstWord_) & (960)) >> (6)
        d_253_u_ = ((d_252_w_) + (1)) & ((1 << 24) - 1)
        d_254_v_ = ((((d_253_u_) << (16)) & ((1 << 24) - 1)) | (((d_251_x1_) << (10)) & ((1 << 24) - 1))) | (d_250_x2_)
        return d_254_v_

    @staticmethod
    def PartitionCodeUnitSequenceChecked(s):
        maybeParts: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        if (s) == (_dafny.SeqWithoutIsStrInference([])):
            maybeParts = Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference([]))
            return maybeParts
        d_255_result_: _dafny.Seq
        d_255_result_ = _dafny.SeqWithoutIsStrInference([])
        d_256_rest_: _dafny.Seq
        d_256_rest_ = s
        while (len(d_256_rest_)) > (0):
            d_257_prefix_: _dafny.Seq
            d_258_valueOrError0_: Std_Wrappers.Option = Std_Wrappers.Option.default()()
            d_258_valueOrError0_ = default__.SplitPrefixMinimalWellFormedCodeUnitSubsequence(d_256_rest_)
            if (d_258_valueOrError0_).IsFailure():
                maybeParts = (d_258_valueOrError0_).PropagateFailure()
                return maybeParts
            d_257_prefix_ = (d_258_valueOrError0_).Extract()
            d_255_result_ = (d_255_result_) + (_dafny.SeqWithoutIsStrInference([d_257_prefix_]))
            d_256_rest_ = _dafny.SeqWithoutIsStrInference((d_256_rest_)[len(d_257_prefix_)::])
        maybeParts = Std_Wrappers.Option_Some(d_255_result_)
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
        for d_259_i_ in range(len(vs)-1, lo1_-1, -1):
            d_260_next_: _dafny.Seq
            d_260_next_ = default__.EncodeScalarValue((vs)[d_259_i_])
            s = (d_260_next_) + (s)
        return s

    @staticmethod
    def DecodeCodeUnitSequence(s):
        d_261_parts_ = default__.PartitionCodeUnitSequence(s)
        d_262_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_261_parts_)
        return d_262_vs_

    @staticmethod
    def DecodeCodeUnitSequenceChecked(s):
        maybeVs: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        d_263_maybeParts_: Std_Wrappers.Option
        d_263_maybeParts_ = default__.PartitionCodeUnitSequenceChecked(s)
        if (d_263_maybeParts_).is_None:
            maybeVs = Std_Wrappers.Option_None()
            return maybeVs
        d_264_parts_: _dafny.Seq
        d_264_parts_ = (d_263_maybeParts_).value
        d_265_vs_: _dafny.Seq
        d_265_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_264_parts_)
        maybeVs = Std_Wrappers.Option_Some(d_265_vs_)
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
