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

# Module: Std_JSON_Errors


class DeserializationError:
    @classmethod
    def default(cls, ):
        return lambda: DeserializationError_UnterminatedSequence()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UnterminatedSequence(self) -> bool:
        return isinstance(self, DeserializationError_UnterminatedSequence)
    @property
    def is_UnsupportedEscape(self) -> bool:
        return isinstance(self, DeserializationError_UnsupportedEscape)
    @property
    def is_EscapeAtEOS(self) -> bool:
        return isinstance(self, DeserializationError_EscapeAtEOS)
    @property
    def is_EmptyNumber(self) -> bool:
        return isinstance(self, DeserializationError_EmptyNumber)
    @property
    def is_ExpectingEOF(self) -> bool:
        return isinstance(self, DeserializationError_ExpectingEOF)
    @property
    def is_IntOverflow(self) -> bool:
        return isinstance(self, DeserializationError_IntOverflow)
    @property
    def is_ReachedEOF(self) -> bool:
        return isinstance(self, DeserializationError_ReachedEOF)
    @property
    def is_ExpectingByte(self) -> bool:
        return isinstance(self, DeserializationError_ExpectingByte)
    @property
    def is_ExpectingAnyByte(self) -> bool:
        return isinstance(self, DeserializationError_ExpectingAnyByte)
    @property
    def is_InvalidUnicode(self) -> bool:
        return isinstance(self, DeserializationError_InvalidUnicode)
    def ToString(self):
        source10_ = self
        if source10_.is_UnterminatedSequence:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unterminated sequence"))
        elif source10_.is_UnsupportedEscape:
            d_280___mcc_h0_ = source10_.str
            d_281_str_ = d_280___mcc_h0_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsupported escape sequence: "))) + (d_281_str_)
        elif source10_.is_EscapeAtEOS:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Escape character at end of string"))
        elif source10_.is_EmptyNumber:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Number must contain at least one digit"))
        elif source10_.is_ExpectingEOF:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Expecting EOF"))
        elif source10_.is_IntOverflow:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Input length does not fit in a 32-bit counter"))
        elif source10_.is_ReachedEOF:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Reached EOF"))
        elif source10_.is_ExpectingByte:
            d_282___mcc_h1_ = source10_.expected
            d_283___mcc_h2_ = source10_.b
            d_284_b_ = d_283___mcc_h2_
            d_285_b0_ = d_282___mcc_h1_
            d_286_c_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint(chr(d_284_b_))]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) if (d_284_b_) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EOF")))
            return (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Expecting '"))) + (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint(chr(d_285_b0_))]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "', read ")))) + (d_286_c_)
        elif source10_.is_ExpectingAnyByte:
            d_287___mcc_h3_ = source10_.expected__sq
            d_288___mcc_h4_ = source10_.b
            d_289_b_ = d_288___mcc_h4_
            d_290_bs0_ = d_287___mcc_h3_
            d_291_c_ = (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) + (_dafny.SeqWithoutIsStrInference([_dafny.CodePoint(chr(d_289_b_))]))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "'"))) if (d_289_b_) > (0) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "EOF")))
            d_292_c0s_ = _dafny.SeqWithoutIsStrInference([_dafny.CodePoint(chr((d_290_bs0_)[d_293_idx_])) for d_293_idx_ in range(len(d_290_bs0_))])
            return (((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Expecting one of '"))) + (d_292_c0s_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "', read ")))) + (d_291_c_)
        elif True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid Unicode sequence"))


class DeserializationError_UnterminatedSequence(DeserializationError, NamedTuple('UnterminatedSequence', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.UnterminatedSequence'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_UnterminatedSequence)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_UnsupportedEscape(DeserializationError, NamedTuple('UnsupportedEscape', [('str', Any)])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.UnsupportedEscape({self.str.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_UnsupportedEscape) and self.str == __o.str
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_EscapeAtEOS(DeserializationError, NamedTuple('EscapeAtEOS', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.EscapeAtEOS'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_EscapeAtEOS)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_EmptyNumber(DeserializationError, NamedTuple('EmptyNumber', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.EmptyNumber'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_EmptyNumber)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_ExpectingEOF(DeserializationError, NamedTuple('ExpectingEOF', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.ExpectingEOF'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_ExpectingEOF)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_IntOverflow(DeserializationError, NamedTuple('IntOverflow', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.IntOverflow'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_IntOverflow)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_ReachedEOF(DeserializationError, NamedTuple('ReachedEOF', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.ReachedEOF'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_ReachedEOF)
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_ExpectingByte(DeserializationError, NamedTuple('ExpectingByte', [('expected', Any), ('b', Any)])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.ExpectingByte({_dafny.string_of(self.expected)}, {_dafny.string_of(self.b)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_ExpectingByte) and self.expected == __o.expected and self.b == __o.b
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_ExpectingAnyByte(DeserializationError, NamedTuple('ExpectingAnyByte', [('expected__sq', Any), ('b', Any)])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.ExpectingAnyByte({_dafny.string_of(self.expected__sq)}, {_dafny.string_of(self.b)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_ExpectingAnyByte) and self.expected__sq == __o.expected__sq and self.b == __o.b
    def __hash__(self) -> int:
        return super().__hash__()

class DeserializationError_InvalidUnicode(DeserializationError, NamedTuple('InvalidUnicode', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.DeserializationError.InvalidUnicode'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DeserializationError_InvalidUnicode)
    def __hash__(self) -> int:
        return super().__hash__()


class SerializationError:
    @classmethod
    def default(cls, ):
        return lambda: SerializationError_OutOfMemory()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_OutOfMemory(self) -> bool:
        return isinstance(self, SerializationError_OutOfMemory)
    @property
    def is_IntTooLarge(self) -> bool:
        return isinstance(self, SerializationError_IntTooLarge)
    @property
    def is_StringTooLong(self) -> bool:
        return isinstance(self, SerializationError_StringTooLong)
    @property
    def is_InvalidUnicode(self) -> bool:
        return isinstance(self, SerializationError_InvalidUnicode)
    def ToString(self):
        source11_ = self
        if source11_.is_OutOfMemory:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Out of memory"))
        elif source11_.is_IntTooLarge:
            d_294___mcc_h0_ = source11_.i
            d_295_i_ = d_294___mcc_h0_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Integer too large: "))) + (Std_Strings.default__.OfInt(d_295_i_))
        elif source11_.is_StringTooLong:
            d_296___mcc_h1_ = source11_.s
            d_297_s_ = d_296___mcc_h1_
            return (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String too long: "))) + (d_297_s_)
        elif True:
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Invalid Unicode sequence"))


class SerializationError_OutOfMemory(SerializationError, NamedTuple('OutOfMemory', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.SerializationError.OutOfMemory'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SerializationError_OutOfMemory)
    def __hash__(self) -> int:
        return super().__hash__()

class SerializationError_IntTooLarge(SerializationError, NamedTuple('IntTooLarge', [('i', Any)])):
    def __dafnystr__(self) -> str:
        return f'Errors.SerializationError.IntTooLarge({_dafny.string_of(self.i)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SerializationError_IntTooLarge) and self.i == __o.i
    def __hash__(self) -> int:
        return super().__hash__()

class SerializationError_StringTooLong(SerializationError, NamedTuple('StringTooLong', [('s', Any)])):
    def __dafnystr__(self) -> str:
        return f'Errors.SerializationError.StringTooLong({self.s.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SerializationError_StringTooLong) and self.s == __o.s
    def __hash__(self) -> int:
        return super().__hash__()

class SerializationError_InvalidUnicode(SerializationError, NamedTuple('InvalidUnicode', [])):
    def __dafnystr__(self) -> str:
        return f'Errors.SerializationError.InvalidUnicode'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SerializationError_InvalidUnicode)
    def __hash__(self) -> int:
        return super().__hash__()

