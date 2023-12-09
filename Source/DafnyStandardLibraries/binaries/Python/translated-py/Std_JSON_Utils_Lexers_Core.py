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

# Module: Std_JSON_Utils_Lexers_Core


class LexerResult:
    @classmethod
    def default(cls, ):
        return lambda: LexerResult_Accept()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Accept(self) -> bool:
        return isinstance(self, LexerResult_Accept)
    @property
    def is_Reject(self) -> bool:
        return isinstance(self, LexerResult_Reject)
    @property
    def is_Partial(self) -> bool:
        return isinstance(self, LexerResult_Partial)

class LexerResult_Accept(LexerResult, NamedTuple('Accept', [])):
    def __dafnystr__(self) -> str:
        return f'Core.LexerResult.Accept'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LexerResult_Accept)
    def __hash__(self) -> int:
        return super().__hash__()

class LexerResult_Reject(LexerResult, NamedTuple('Reject', [('err', Any)])):
    def __dafnystr__(self) -> str:
        return f'Core.LexerResult.Reject({_dafny.string_of(self.err)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LexerResult_Reject) and self.err == __o.err
    def __hash__(self) -> int:
        return super().__hash__()

class LexerResult_Partial(LexerResult, NamedTuple('Partial', [('st', Any)])):
    def __dafnystr__(self) -> str:
        return f'Core.LexerResult.Partial({_dafny.string_of(self.st)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LexerResult_Partial) and self.st == __o.st
    def __hash__(self) -> int:
        return super().__hash__()

