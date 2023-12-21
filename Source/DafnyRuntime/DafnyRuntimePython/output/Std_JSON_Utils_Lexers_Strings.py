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

# Module: Std_JSON_Utils_Lexers_Strings

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def StringBody(escaped, byte):
        if (byte) == (ord(_dafny.CodePoint('\\'))):
            return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(not(escaped))
        elif ((byte) == (ord(_dafny.CodePoint('\"')))) and (not(escaped)):
            return Std_JSON_Utils_Lexers_Core.LexerResult_Accept()
        elif True:
            return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(False)

    @staticmethod
    def String(st, byte):
        source13_ = st
        if source13_.is_Start:
            if (byte) == (ord(_dafny.CodePoint('\"'))):
                return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(StringLexerState_Body(False))
            elif True:
                return Std_JSON_Utils_Lexers_Core.LexerResult_Reject(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "String must start with double quote")))
        elif source13_.is_Body:
            d_352___mcc_h0_ = source13_.escaped
            d_353_escaped_ = d_352___mcc_h0_
            if (byte) == (ord(_dafny.CodePoint('\\'))):
                return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(StringLexerState_Body(not(d_353_escaped_)))
            elif ((byte) == (ord(_dafny.CodePoint('\"')))) and (not(d_353_escaped_)):
                return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(StringLexerState_End())
            elif True:
                return Std_JSON_Utils_Lexers_Core.LexerResult_Partial(StringLexerState_Body(False))
        elif True:
            return Std_JSON_Utils_Lexers_Core.LexerResult_Accept()

    @_dafny.classproperty
    def StringBodyLexerStart(instance):
        return False
    @_dafny.classproperty
    def StringLexerStart(instance):
        return StringLexerState_Start()

class StringLexerState:
    @classmethod
    def default(cls, ):
        return lambda: StringLexerState_Start()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Start(self) -> bool:
        return isinstance(self, StringLexerState_Start)
    @property
    def is_Body(self) -> bool:
        return isinstance(self, StringLexerState_Body)
    @property
    def is_End(self) -> bool:
        return isinstance(self, StringLexerState_End)

class StringLexerState_Start(StringLexerState, NamedTuple('Start', [])):
    def __dafnystr__(self) -> str:
        return f'Strings.StringLexerState.Start'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StringLexerState_Start)
    def __hash__(self) -> int:
        return super().__hash__()

class StringLexerState_Body(StringLexerState, NamedTuple('Body', [('escaped', Any)])):
    def __dafnystr__(self) -> str:
        return f'Strings.StringLexerState.Body({_dafny.string_of(self.escaped)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StringLexerState_Body) and self.escaped == __o.escaped
    def __hash__(self) -> int:
        return super().__hash__()

class StringLexerState_End(StringLexerState, NamedTuple('End', [])):
    def __dafnystr__(self) -> str:
        return f'Strings.StringLexerState.End'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, StringLexerState_End)
    def __hash__(self) -> int:
        return super().__hash__()

