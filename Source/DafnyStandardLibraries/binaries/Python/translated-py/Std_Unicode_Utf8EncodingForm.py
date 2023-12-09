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

# Module: Std_Unicode_Utf8EncodingForm

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsMinimalWellFormedCodeUnitSubsequence(s):
        if (len(s)) == (1):
            d_160_b_ = default__.IsWellFormedSingleCodeUnitSequence(s)
            return d_160_b_
        elif (len(s)) == (2):
            d_161_b_ = default__.IsWellFormedDoubleCodeUnitSequence(s)
            return d_161_b_
        elif (len(s)) == (3):
            d_162_b_ = default__.IsWellFormedTripleCodeUnitSequence(s)
            return d_162_b_
        elif (len(s)) == (4):
            d_163_b_ = default__.IsWellFormedQuadrupleCodeUnitSequence(s)
            return d_163_b_
        elif True:
            return False

    @staticmethod
    def IsWellFormedSingleCodeUnitSequence(s):
        d_164_firstByte_ = (s)[0]
        return (True) and (((0) <= (d_164_firstByte_)) and ((d_164_firstByte_) <= (127)))

    @staticmethod
    def IsWellFormedDoubleCodeUnitSequence(s):
        d_165_firstByte_ = (s)[0]
        d_166_secondByte_ = (s)[1]
        return (((194) <= (d_165_firstByte_)) and ((d_165_firstByte_) <= (223))) and (((128) <= (d_166_secondByte_)) and ((d_166_secondByte_) <= (191)))

    @staticmethod
    def IsWellFormedTripleCodeUnitSequence(s):
        d_167_firstByte_ = (s)[0]
        d_168_secondByte_ = (s)[1]
        d_169_thirdByte_ = (s)[2]
        return ((((((d_167_firstByte_) == (224)) and (((160) <= (d_168_secondByte_)) and ((d_168_secondByte_) <= (191)))) or ((((225) <= (d_167_firstByte_)) and ((d_167_firstByte_) <= (236))) and (((128) <= (d_168_secondByte_)) and ((d_168_secondByte_) <= (191))))) or (((d_167_firstByte_) == (237)) and (((128) <= (d_168_secondByte_)) and ((d_168_secondByte_) <= (159))))) or ((((238) <= (d_167_firstByte_)) and ((d_167_firstByte_) <= (239))) and (((128) <= (d_168_secondByte_)) and ((d_168_secondByte_) <= (191))))) and (((128) <= (d_169_thirdByte_)) and ((d_169_thirdByte_) <= (191)))

    @staticmethod
    def IsWellFormedQuadrupleCodeUnitSequence(s):
        d_170_firstByte_ = (s)[0]
        d_171_secondByte_ = (s)[1]
        d_172_thirdByte_ = (s)[2]
        d_173_fourthByte_ = (s)[3]
        return ((((((d_170_firstByte_) == (240)) and (((144) <= (d_171_secondByte_)) and ((d_171_secondByte_) <= (191)))) or ((((241) <= (d_170_firstByte_)) and ((d_170_firstByte_) <= (243))) and (((128) <= (d_171_secondByte_)) and ((d_171_secondByte_) <= (191))))) or (((d_170_firstByte_) == (244)) and (((128) <= (d_171_secondByte_)) and ((d_171_secondByte_) <= (143))))) and (((128) <= (d_172_thirdByte_)) and ((d_172_thirdByte_) <= (191)))) and (((128) <= (d_173_fourthByte_)) and ((d_173_fourthByte_) <= (191)))

    @staticmethod
    def SplitPrefixMinimalWellFormedCodeUnitSubsequence(s):
        if ((len(s)) >= (1)) and (default__.IsWellFormedSingleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:1:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:1:]))
        elif ((len(s)) >= (2)) and (default__.IsWellFormedDoubleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:2:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:2:]))
        elif ((len(s)) >= (3)) and (default__.IsWellFormedTripleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:3:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:3:]))
        elif ((len(s)) >= (4)) and (default__.IsWellFormedQuadrupleCodeUnitSequence(_dafny.SeqWithoutIsStrInference((s)[:4:]))):
            return Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference((s)[:4:]))
        elif True:
            return Std_Wrappers.Option_None()

    @staticmethod
    def EncodeScalarValue(v):
        if (v) <= (127):
            return default__.EncodeScalarValueSingleByte(v)
        elif (v) <= (2047):
            return default__.EncodeScalarValueDoubleByte(v)
        elif (v) <= (65535):
            return default__.EncodeScalarValueTripleByte(v)
        elif True:
            return default__.EncodeScalarValueQuadrupleByte(v)

    @staticmethod
    def EncodeScalarValueSingleByte(v):
        d_174_x_ = (v) & (127)
        d_175_firstByte_ = d_174_x_
        return _dafny.SeqWithoutIsStrInference([d_175_firstByte_])

    @staticmethod
    def EncodeScalarValueDoubleByte(v):
        d_176_x_ = (v) & (63)
        d_177_y_ = ((v) & (1984)) >> (6)
        d_178_firstByte_ = (192) | (d_177_y_)
        d_179_secondByte_ = (128) | (d_176_x_)
        return _dafny.SeqWithoutIsStrInference([d_178_firstByte_, d_179_secondByte_])

    @staticmethod
    def EncodeScalarValueTripleByte(v):
        d_180_x_ = (v) & (63)
        d_181_y_ = ((v) & (4032)) >> (6)
        d_182_z_ = ((v) & (61440)) >> (12)
        d_183_firstByte_ = (224) | (d_182_z_)
        d_184_secondByte_ = (128) | (d_181_y_)
        d_185_thirdByte_ = (128) | (d_180_x_)
        return _dafny.SeqWithoutIsStrInference([d_183_firstByte_, d_184_secondByte_, d_185_thirdByte_])

    @staticmethod
    def EncodeScalarValueQuadrupleByte(v):
        d_186_x_ = (v) & (63)
        d_187_y_ = ((v) & (4032)) >> (6)
        d_188_z_ = ((v) & (61440)) >> (12)
        d_189_u2_ = ((v) & (196608)) >> (16)
        d_190_u1_ = ((v) & (1835008)) >> (18)
        d_191_firstByte_ = (240) | (d_190_u1_)
        d_192_secondByte_ = ((128) | (((d_189_u2_) << (4)) & ((1 << 8) - 1))) | (d_188_z_)
        d_193_thirdByte_ = (128) | (d_187_y_)
        d_194_fourthByte_ = (128) | (d_186_x_)
        return _dafny.SeqWithoutIsStrInference([d_191_firstByte_, d_192_secondByte_, d_193_thirdByte_, d_194_fourthByte_])

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequence(m):
        if (len(m)) == (1):
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
        elif (len(m)) == (2):
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
        elif (len(m)) == (3):
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
        elif True:
            return default__.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m):
        d_195_firstByte_ = (m)[0]
        d_196_x_ = d_195_firstByte_
        return d_196_x_

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m):
        d_197_firstByte_ = (m)[0]
        d_198_secondByte_ = (m)[1]
        d_199_y_ = (d_197_firstByte_) & (31)
        d_200_x_ = (d_198_secondByte_) & (63)
        return (((d_199_y_) << (6)) & ((1 << 24) - 1)) | (d_200_x_)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m):
        d_201_firstByte_ = (m)[0]
        d_202_secondByte_ = (m)[1]
        d_203_thirdByte_ = (m)[2]
        d_204_z_ = (d_201_firstByte_) & (15)
        d_205_y_ = (d_202_secondByte_) & (63)
        d_206_x_ = (d_203_thirdByte_) & (63)
        return ((((d_204_z_) << (12)) & ((1 << 24) - 1)) | (((d_205_y_) << (6)) & ((1 << 24) - 1))) | (d_206_x_)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m):
        d_207_firstByte_ = (m)[0]
        d_208_secondByte_ = (m)[1]
        d_209_thirdByte_ = (m)[2]
        d_210_fourthByte_ = (m)[3]
        d_211_u1_ = (d_207_firstByte_) & (7)
        d_212_u2_ = ((d_208_secondByte_) & (48)) >> (4)
        d_213_z_ = (d_208_secondByte_) & (15)
        d_214_y_ = (d_209_thirdByte_) & (63)
        d_215_x_ = (d_210_fourthByte_) & (63)
        return ((((((d_211_u1_) << (18)) & ((1 << 24) - 1)) | (((d_212_u2_) << (16)) & ((1 << 24) - 1))) | (((d_213_z_) << (12)) & ((1 << 24) - 1))) | (((d_214_y_) << (6)) & ((1 << 24) - 1))) | (d_215_x_)

    @staticmethod
    def PartitionCodeUnitSequenceChecked(s):
        maybeParts: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        if (s) == (_dafny.SeqWithoutIsStrInference([])):
            maybeParts = Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference([]))
            return maybeParts
        d_216_result_: _dafny.Seq
        d_216_result_ = _dafny.SeqWithoutIsStrInference([])
        d_217_rest_: _dafny.Seq
        d_217_rest_ = s
        while (len(d_217_rest_)) > (0):
            d_218_prefix_: _dafny.Seq
            d_219_valueOrError0_: Std_Wrappers.Option = Std_Wrappers.Option.default()()
            d_219_valueOrError0_ = default__.SplitPrefixMinimalWellFormedCodeUnitSubsequence(d_217_rest_)
            if (d_219_valueOrError0_).IsFailure():
                maybeParts = (d_219_valueOrError0_).PropagateFailure()
                return maybeParts
            d_218_prefix_ = (d_219_valueOrError0_).Extract()
            d_216_result_ = (d_216_result_) + (_dafny.SeqWithoutIsStrInference([d_218_prefix_]))
            d_217_rest_ = _dafny.SeqWithoutIsStrInference((d_217_rest_)[len(d_218_prefix_)::])
        maybeParts = Std_Wrappers.Option_Some(d_216_result_)
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
        lo0_ = 0
        for d_220_i_ in range(len(vs)-1, lo0_-1, -1):
            d_221_next_: _dafny.Seq
            d_221_next_ = default__.EncodeScalarValue((vs)[d_220_i_])
            s = (d_221_next_) + (s)
        return s

    @staticmethod
    def DecodeCodeUnitSequence(s):
        d_222_parts_ = default__.PartitionCodeUnitSequence(s)
        d_223_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_222_parts_)
        return d_223_vs_

    @staticmethod
    def DecodeCodeUnitSequenceChecked(s):
        maybeVs: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        d_224_maybeParts_: Std_Wrappers.Option
        d_224_maybeParts_ = default__.PartitionCodeUnitSequenceChecked(s)
        if (d_224_maybeParts_).is_None:
            maybeVs = Std_Wrappers.Option_None()
            return maybeVs
        d_225_parts_: _dafny.Seq
        d_225_parts_ = (d_224_maybeParts_).value
        d_226_vs_: _dafny.Seq
        d_226_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_225_parts_)
        maybeVs = Std_Wrappers.Option_Some(d_226_vs_)
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
