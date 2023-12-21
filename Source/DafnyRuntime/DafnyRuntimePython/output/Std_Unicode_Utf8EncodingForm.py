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

# Module: Std_Unicode_Utf8EncodingForm

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsMinimalWellFormedCodeUnitSubsequence(s):
        if (len(s)) == (1):
            d_168_b_ = default__.IsWellFormedSingleCodeUnitSequence(s)
            return d_168_b_
        elif (len(s)) == (2):
            d_169_b_ = default__.IsWellFormedDoubleCodeUnitSequence(s)
            return d_169_b_
        elif (len(s)) == (3):
            d_170_b_ = default__.IsWellFormedTripleCodeUnitSequence(s)
            return d_170_b_
        elif (len(s)) == (4):
            d_171_b_ = default__.IsWellFormedQuadrupleCodeUnitSequence(s)
            return d_171_b_
        elif True:
            return False

    @staticmethod
    def IsWellFormedSingleCodeUnitSequence(s):
        d_172_firstByte_ = (s)[0]
        return (True) and (((0) <= (d_172_firstByte_)) and ((d_172_firstByte_) <= (127)))

    @staticmethod
    def IsWellFormedDoubleCodeUnitSequence(s):
        d_173_firstByte_ = (s)[0]
        d_174_secondByte_ = (s)[1]
        return (((194) <= (d_173_firstByte_)) and ((d_173_firstByte_) <= (223))) and (((128) <= (d_174_secondByte_)) and ((d_174_secondByte_) <= (191)))

    @staticmethod
    def IsWellFormedTripleCodeUnitSequence(s):
        d_175_firstByte_ = (s)[0]
        d_176_secondByte_ = (s)[1]
        d_177_thirdByte_ = (s)[2]
        return ((((((d_175_firstByte_) == (224)) and (((160) <= (d_176_secondByte_)) and ((d_176_secondByte_) <= (191)))) or ((((225) <= (d_175_firstByte_)) and ((d_175_firstByte_) <= (236))) and (((128) <= (d_176_secondByte_)) and ((d_176_secondByte_) <= (191))))) or (((d_175_firstByte_) == (237)) and (((128) <= (d_176_secondByte_)) and ((d_176_secondByte_) <= (159))))) or ((((238) <= (d_175_firstByte_)) and ((d_175_firstByte_) <= (239))) and (((128) <= (d_176_secondByte_)) and ((d_176_secondByte_) <= (191))))) and (((128) <= (d_177_thirdByte_)) and ((d_177_thirdByte_) <= (191)))

    @staticmethod
    def IsWellFormedQuadrupleCodeUnitSequence(s):
        d_178_firstByte_ = (s)[0]
        d_179_secondByte_ = (s)[1]
        d_180_thirdByte_ = (s)[2]
        d_181_fourthByte_ = (s)[3]
        return ((((((d_178_firstByte_) == (240)) and (((144) <= (d_179_secondByte_)) and ((d_179_secondByte_) <= (191)))) or ((((241) <= (d_178_firstByte_)) and ((d_178_firstByte_) <= (243))) and (((128) <= (d_179_secondByte_)) and ((d_179_secondByte_) <= (191))))) or (((d_178_firstByte_) == (244)) and (((128) <= (d_179_secondByte_)) and ((d_179_secondByte_) <= (143))))) and (((128) <= (d_180_thirdByte_)) and ((d_180_thirdByte_) <= (191)))) and (((128) <= (d_181_fourthByte_)) and ((d_181_fourthByte_) <= (191)))

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
        d_182_x_ = (v) & (127)
        d_183_firstByte_ = d_182_x_
        return _dafny.SeqWithoutIsStrInference([d_183_firstByte_])

    @staticmethod
    def EncodeScalarValueDoubleByte(v):
        d_184_x_ = (v) & (63)
        d_185_y_ = ((v) & (1984)) >> (6)
        d_186_firstByte_ = (192) | (d_185_y_)
        d_187_secondByte_ = (128) | (d_184_x_)
        return _dafny.SeqWithoutIsStrInference([d_186_firstByte_, d_187_secondByte_])

    @staticmethod
    def EncodeScalarValueTripleByte(v):
        d_188_x_ = (v) & (63)
        d_189_y_ = ((v) & (4032)) >> (6)
        d_190_z_ = ((v) & (61440)) >> (12)
        d_191_firstByte_ = (224) | (d_190_z_)
        d_192_secondByte_ = (128) | (d_189_y_)
        d_193_thirdByte_ = (128) | (d_188_x_)
        return _dafny.SeqWithoutIsStrInference([d_191_firstByte_, d_192_secondByte_, d_193_thirdByte_])

    @staticmethod
    def EncodeScalarValueQuadrupleByte(v):
        d_194_x_ = (v) & (63)
        d_195_y_ = ((v) & (4032)) >> (6)
        d_196_z_ = ((v) & (61440)) >> (12)
        d_197_u2_ = ((v) & (196608)) >> (16)
        d_198_u1_ = ((v) & (1835008)) >> (18)
        d_199_firstByte_ = (240) | (d_198_u1_)
        d_200_secondByte_ = ((128) | (((d_197_u2_) << (4)) & ((1 << 8) - 1))) | (d_196_z_)
        d_201_thirdByte_ = (128) | (d_195_y_)
        d_202_fourthByte_ = (128) | (d_194_x_)
        return _dafny.SeqWithoutIsStrInference([d_199_firstByte_, d_200_secondByte_, d_201_thirdByte_, d_202_fourthByte_])

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
        d_203_firstByte_ = (m)[0]
        d_204_x_ = d_203_firstByte_
        return d_204_x_

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m):
        d_205_firstByte_ = (m)[0]
        d_206_secondByte_ = (m)[1]
        d_207_y_ = (d_205_firstByte_) & (31)
        d_208_x_ = (d_206_secondByte_) & (63)
        return (((d_207_y_) << (6)) & ((1 << 24) - 1)) | (d_208_x_)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m):
        d_209_firstByte_ = (m)[0]
        d_210_secondByte_ = (m)[1]
        d_211_thirdByte_ = (m)[2]
        d_212_z_ = (d_209_firstByte_) & (15)
        d_213_y_ = (d_210_secondByte_) & (63)
        d_214_x_ = (d_211_thirdByte_) & (63)
        return ((((d_212_z_) << (12)) & ((1 << 24) - 1)) | (((d_213_y_) << (6)) & ((1 << 24) - 1))) | (d_214_x_)

    @staticmethod
    def DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m):
        d_215_firstByte_ = (m)[0]
        d_216_secondByte_ = (m)[1]
        d_217_thirdByte_ = (m)[2]
        d_218_fourthByte_ = (m)[3]
        d_219_u1_ = (d_215_firstByte_) & (7)
        d_220_u2_ = ((d_216_secondByte_) & (48)) >> (4)
        d_221_z_ = (d_216_secondByte_) & (15)
        d_222_y_ = (d_217_thirdByte_) & (63)
        d_223_x_ = (d_218_fourthByte_) & (63)
        return ((((((d_219_u1_) << (18)) & ((1 << 24) - 1)) | (((d_220_u2_) << (16)) & ((1 << 24) - 1))) | (((d_221_z_) << (12)) & ((1 << 24) - 1))) | (((d_222_y_) << (6)) & ((1 << 24) - 1))) | (d_223_x_)

    @staticmethod
    def PartitionCodeUnitSequenceChecked(s):
        maybeParts: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        if (s) == (_dafny.SeqWithoutIsStrInference([])):
            maybeParts = Std_Wrappers.Option_Some(_dafny.SeqWithoutIsStrInference([]))
            return maybeParts
        d_224_result_: _dafny.Seq
        d_224_result_ = _dafny.SeqWithoutIsStrInference([])
        d_225_rest_: _dafny.Seq
        d_225_rest_ = s
        while (len(d_225_rest_)) > (0):
            d_226_prefix_: _dafny.Seq
            d_227_valueOrError0_: Std_Wrappers.Option = Std_Wrappers.Option.default()()
            d_227_valueOrError0_ = default__.SplitPrefixMinimalWellFormedCodeUnitSubsequence(d_225_rest_)
            if (d_227_valueOrError0_).IsFailure():
                maybeParts = (d_227_valueOrError0_).PropagateFailure()
                return maybeParts
            d_226_prefix_ = (d_227_valueOrError0_).Extract()
            d_224_result_ = (d_224_result_) + (_dafny.SeqWithoutIsStrInference([d_226_prefix_]))
            d_225_rest_ = _dafny.SeqWithoutIsStrInference((d_225_rest_)[len(d_226_prefix_)::])
        maybeParts = Std_Wrappers.Option_Some(d_224_result_)
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
        for d_228_i_ in range(len(vs)-1, lo0_-1, -1):
            d_229_next_: _dafny.Seq
            d_229_next_ = default__.EncodeScalarValue((vs)[d_228_i_])
            s = (d_229_next_) + (s)
        return s

    @staticmethod
    def DecodeCodeUnitSequence(s):
        d_230_parts_ = default__.PartitionCodeUnitSequence(s)
        d_231_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_230_parts_)
        return d_231_vs_

    @staticmethod
    def DecodeCodeUnitSequenceChecked(s):
        maybeVs: Std_Wrappers.Option = Std_Wrappers.Option.default()()
        d_232_maybeParts_: Std_Wrappers.Option
        d_232_maybeParts_ = default__.PartitionCodeUnitSequenceChecked(s)
        if (d_232_maybeParts_).is_None:
            maybeVs = Std_Wrappers.Option_None()
            return maybeVs
        d_233_parts_: _dafny.Seq
        d_233_parts_ = (d_232_maybeParts_).value
        d_234_vs_: _dafny.Seq
        d_234_vs_ = Std_Collections_Seq.default__.Map(default__.DecodeMinimalWellFormedCodeUnitSubsequence, d_233_parts_)
        maybeVs = Std_Wrappers.Option_Some(d_234_vs_)
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
