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

# Module: Std_Base64

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsBase64Char(c):
        return (((((c) == (_dafny.CodePoint('+'))) or ((c) == (_dafny.CodePoint('/')))) or (((_dafny.CodePoint('0')) <= (c)) and ((c) <= (_dafny.CodePoint('9'))))) or (((_dafny.CodePoint('A')) <= (c)) and ((c) <= (_dafny.CodePoint('Z'))))) or (((_dafny.CodePoint('a')) <= (c)) and ((c) <= (_dafny.CodePoint('z'))))

    @staticmethod
    def IsUnpaddedBase64String(s):
        def lambda0_(forall_var_0_):
            d_28_k_: str = forall_var_0_
            return not ((d_28_k_) in (s)) or (default__.IsBase64Char(d_28_k_))

        return ((_dafny.euclidian_modulus(len(s), 4)) == (0)) and (_dafny.quantifier((s).UniqueElements, True, lambda0_))

    @staticmethod
    def IndexToChar(i):
        if (i) == (63):
            return _dafny.CodePoint('/')
        elif (i) == (62):
            return _dafny.CodePoint('+')
        elif ((52) <= (i)) and ((i) <= (61)):
            return _dafny.CodePoint(chr(((i) - (4)) & ((1 << 6) - 1)))
        elif ((26) <= (i)) and ((i) <= (51)):
            return (_dafny.CodePoint(chr(i))) + (_dafny.CodePoint(chr(71)))
        elif True:
            return (_dafny.CodePoint(chr(i))) + (_dafny.CodePoint(chr(65)))

    @staticmethod
    def CharToIndex(c):
        if (c) == (_dafny.CodePoint('/')):
            return 63
        elif (c) == (_dafny.CodePoint('+')):
            return 62
        elif ((_dafny.CodePoint('0')) <= (c)) and ((c) <= (_dafny.CodePoint('9'))):
            return ord((c) + (_dafny.CodePoint(chr(4))))
        elif ((_dafny.CodePoint('a')) <= (c)) and ((c) <= (_dafny.CodePoint('z'))):
            return ord((c) - (_dafny.CodePoint(chr(71))))
        elif True:
            return ord((c) - (_dafny.CodePoint(chr(65))))

    @staticmethod
    def BV24ToSeq(x):
        d_29_b0_ = ((x) >> (16)) & (255)
        d_30_b1_ = ((x) >> (8)) & (255)
        d_31_b2_ = (x) & (255)
        return _dafny.SeqWithoutIsStrInference([d_29_b0_, d_30_b1_, d_31_b2_])

    @staticmethod
    def SeqToBV24(x):
        return (((((x)[0]) << (16)) & ((1 << 24) - 1)) | ((((x)[1]) << (8)) & ((1 << 24) - 1))) | ((x)[2])

    @staticmethod
    def BV24ToIndexSeq(x):
        d_32_b0_ = ((x) >> (18)) & (63)
        d_33_b1_ = ((x) >> (12)) & (63)
        d_34_b2_ = ((x) >> (6)) & (63)
        d_35_b3_ = (x) & (63)
        return _dafny.SeqWithoutIsStrInference([d_32_b0_, d_33_b1_, d_34_b2_, d_35_b3_])

    @staticmethod
    def IndexSeqToBV24(x):
        return ((((((x)[0]) << (18)) & ((1 << 24) - 1)) | ((((x)[1]) << (12)) & ((1 << 24) - 1))) | ((((x)[2]) << (6)) & ((1 << 24) - 1))) | ((x)[3])

    @staticmethod
    def DecodeBlock(s):
        return default__.BV24ToSeq(default__.IndexSeqToBV24(s))

    @staticmethod
    def EncodeBlock(s):
        return default__.BV24ToIndexSeq(default__.SeqToBV24(s))

    @staticmethod
    def DecodeRecursively(s):
        b: _dafny.Seq = _dafny.Seq({})
        d_36_resultLength_: int
        d_36_resultLength_ = (_dafny.euclidian_division(len(s), 4)) * (3)
        d_37_result_: _dafny.Array
        def lambda1_(d_38_i_):
            return 0

        init0_ = lambda1_
        nw0_ = _dafny.Array(None, d_36_resultLength_)
        for i0_0_ in range(nw0_.length(0)):
            nw0_[i0_0_] = init0_(i0_0_)
        d_37_result_ = nw0_
        d_39_i_: int
        d_39_i_ = len(s)
        d_40_j_: int
        d_40_j_ = d_36_resultLength_
        while (d_39_i_) > (0):
            d_39_i_ = (d_39_i_) - (4)
            d_40_j_ = (d_40_j_) - (3)
            d_41_block_: _dafny.Seq
            d_41_block_ = default__.DecodeBlock(_dafny.SeqWithoutIsStrInference((s)[d_39_i_:(d_39_i_) + (4):]))
            (d_37_result_)[(d_40_j_)] = (d_41_block_)[0]
            index0_ = (d_40_j_) + (1)
            (d_37_result_)[index0_] = (d_41_block_)[1]
            index1_ = (d_40_j_) + (2)
            (d_37_result_)[index1_] = (d_41_block_)[2]
        b = _dafny.SeqWithoutIsStrInference((d_37_result_)[::])
        return b

    @staticmethod
    def EncodeRecursively(b):
        s: _dafny.Seq = _dafny.Seq({})
        d_42_resultLength_: int
        d_42_resultLength_ = (_dafny.euclidian_division(len(b), 3)) * (4)
        d_43_result_: _dafny.Array
        def lambda2_(d_44_i_):
            return 0

        init1_ = lambda2_
        nw1_ = _dafny.Array(None, d_42_resultLength_)
        for i0_1_ in range(nw1_.length(0)):
            nw1_[i0_1_] = init1_(i0_1_)
        d_43_result_ = nw1_
        d_45_i_: int
        d_45_i_ = len(b)
        d_46_j_: int
        d_46_j_ = d_42_resultLength_
        while (d_45_i_) > (0):
            d_45_i_ = (d_45_i_) - (3)
            d_46_j_ = (d_46_j_) - (4)
            d_47_block_: _dafny.Seq
            d_47_block_ = default__.EncodeBlock(_dafny.SeqWithoutIsStrInference((b)[d_45_i_:(d_45_i_) + (3):]))
            (d_43_result_)[(d_46_j_)] = (d_47_block_)[0]
            index2_ = (d_46_j_) + (1)
            (d_43_result_)[index2_] = (d_47_block_)[1]
            index3_ = (d_46_j_) + (2)
            (d_43_result_)[index3_] = (d_47_block_)[2]
            index4_ = (d_46_j_) + (3)
            (d_43_result_)[index4_] = (d_47_block_)[3]
        s = _dafny.SeqWithoutIsStrInference((d_43_result_)[::])
        return s

    @staticmethod
    def FromCharsToIndices(s):
        return _dafny.SeqWithoutIsStrInference([default__.CharToIndex((s)[d_48_i_]) for d_48_i_ in range(len(s))])

    @staticmethod
    def FromIndicesToChars(b):
        return _dafny.SeqWithoutIsStrInference([default__.IndexToChar((b)[d_49_i_]) for d_49_i_ in range(len(b))])

    @staticmethod
    def DecodeUnpadded(s):
        return default__.DecodeRecursively(default__.FromCharsToIndices(s))

    @staticmethod
    def EncodeUnpadded(b):
        return default__.FromIndicesToChars(default__.EncodeRecursively(b))

    @staticmethod
    def Is1Padding(s):
        return ((((((len(s)) == (4)) and (default__.IsBase64Char((s)[0]))) and (default__.IsBase64Char((s)[1]))) and (default__.IsBase64Char((s)[2]))) and (((default__.CharToIndex((s)[2])) & (3)) == (0))) and (((s)[3]) == (_dafny.CodePoint('=')))

    @staticmethod
    def Decode1Padding(s):
        d_50_d_ = default__.DecodeBlock(_dafny.SeqWithoutIsStrInference([default__.CharToIndex((s)[0]), default__.CharToIndex((s)[1]), default__.CharToIndex((s)[2]), 0]))
        return _dafny.SeqWithoutIsStrInference([(d_50_d_)[0], (d_50_d_)[1]])

    @staticmethod
    def Encode1Padding(b):
        d_51_e_ = default__.EncodeBlock(_dafny.SeqWithoutIsStrInference([(b)[0], (b)[1], 0]))
        return _dafny.SeqWithoutIsStrInference([default__.IndexToChar((d_51_e_)[0]), default__.IndexToChar((d_51_e_)[1]), default__.IndexToChar((d_51_e_)[2]), _dafny.CodePoint('=')])

    @staticmethod
    def Is2Padding(s):
        return ((((((len(s)) == (4)) and (default__.IsBase64Char((s)[0]))) and (default__.IsBase64Char((s)[1]))) and ((_dafny.euclidian_modulus(default__.CharToIndex((s)[1]), 16)) == (0))) and (((s)[2]) == (_dafny.CodePoint('=')))) and (((s)[3]) == (_dafny.CodePoint('=')))

    @staticmethod
    def Decode2Padding(s):
        d_52_d_ = default__.DecodeBlock(_dafny.SeqWithoutIsStrInference([default__.CharToIndex((s)[0]), default__.CharToIndex((s)[1]), 0, 0]))
        return _dafny.SeqWithoutIsStrInference([(d_52_d_)[0]])

    @staticmethod
    def Encode2Padding(b):
        d_53_e_ = default__.EncodeBlock(_dafny.SeqWithoutIsStrInference([(b)[0], 0, 0]))
        return _dafny.SeqWithoutIsStrInference([default__.IndexToChar((d_53_e_)[0]), default__.IndexToChar((d_53_e_)[1]), _dafny.CodePoint('='), _dafny.CodePoint('=')])

    @staticmethod
    def IsBase64String(s):
        d_54_finalBlockStart_ = (len(s)) - (4)
        return ((_dafny.euclidian_modulus(len(s), 4)) == (0)) and ((default__.IsUnpaddedBase64String(s)) or ((default__.IsUnpaddedBase64String(_dafny.SeqWithoutIsStrInference((s)[:d_54_finalBlockStart_:]))) and ((default__.Is1Padding(_dafny.SeqWithoutIsStrInference((s)[d_54_finalBlockStart_::]))) or (default__.Is2Padding(_dafny.SeqWithoutIsStrInference((s)[d_54_finalBlockStart_::]))))))

    @staticmethod
    def DecodeValid(s):
        if (s) == (_dafny.SeqWithoutIsStrInference([])):
            return _dafny.SeqWithoutIsStrInference([])
        elif True:
            d_55_finalBlockStart_ = (len(s)) - (4)
            d_56_prefix_ = _dafny.SeqWithoutIsStrInference((s)[:d_55_finalBlockStart_:])
            d_57_suffix_ = _dafny.SeqWithoutIsStrInference((s)[d_55_finalBlockStart_::])
            if default__.Is1Padding(d_57_suffix_):
                return (default__.DecodeUnpadded(d_56_prefix_)) + (default__.Decode1Padding(d_57_suffix_))
            elif default__.Is2Padding(d_57_suffix_):
                return (default__.DecodeUnpadded(d_56_prefix_)) + (default__.Decode2Padding(d_57_suffix_))
            elif True:
                return default__.DecodeUnpadded(s)

    @staticmethod
    def DecodeBV(s):
        if default__.IsBase64String(s):
            return Std_Wrappers.Result_Success(default__.DecodeValid(s))
        elif True:
            return Std_Wrappers.Result_Failure(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The encoding is malformed")))

    @staticmethod
    def EncodeBV(b):
        if (_dafny.euclidian_modulus(len(b), 3)) == (0):
            return default__.EncodeUnpadded(b)
        elif (_dafny.euclidian_modulus(len(b), 3)) == (1):
            d_58_s1_ = default__.EncodeUnpadded(_dafny.SeqWithoutIsStrInference((b)[:(len(b)) - (1):]))
            d_59_s2_ = default__.Encode2Padding(_dafny.SeqWithoutIsStrInference((b)[(len(b)) - (1)::]))
            return (d_58_s1_) + (d_59_s2_)
        elif True:
            d_60_s1_ = default__.EncodeUnpadded(_dafny.SeqWithoutIsStrInference((b)[:(len(b)) - (2):]))
            d_61_s2_ = default__.Encode1Padding(_dafny.SeqWithoutIsStrInference((b)[(len(b)) - (2)::]))
            return (d_60_s1_) + (d_61_s2_)

    @staticmethod
    def UInt8sToBVs(u):
        return _dafny.SeqWithoutIsStrInference([(u)[d_62_i_] for d_62_i_ in range(len(u))])

    @staticmethod
    def BVsToUInt8s(b):
        return _dafny.SeqWithoutIsStrInference([(b)[d_63_i_] for d_63_i_ in range(len(b))])

    @staticmethod
    def Encode(u):
        return default__.EncodeBV(default__.UInt8sToBVs(u))

    @staticmethod
    def Decode(s):
        if default__.IsBase64String(s):
            d_64_b_ = default__.DecodeValid(s)
            return Std_Wrappers.Result_Success(default__.BVsToUInt8s(d_64_b_))
        elif True:
            return Std_Wrappers.Result_Failure(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "The encoding is malformed")))

