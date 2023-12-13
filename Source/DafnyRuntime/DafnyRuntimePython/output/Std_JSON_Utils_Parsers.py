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

# Module: Std_JSON_Utils_Parsers

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def ParserWitness():
        def lambda22_(d_389___v9_):
            return Std_Wrappers.Result_Failure(Std_JSON_Utils_Cursors.CursorError_EOF())

        return lambda22_

    @staticmethod
    def SubParserWitness():
        def lambda23_(d_390_cs_):
            return Std_Wrappers.Result_Failure(Std_JSON_Utils_Cursors.CursorError_EOF())

        return lambda23_


class Parser:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.ParserWitness()

class Parser__:
    @classmethod
    def default(cls, default_T):
        return lambda: (lambda x0: Std_Wrappers.Result.default(Std_JSON_Utils_Cursors.Split.default(default_T))())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Parser(self) -> bool:
        return isinstance(self, Parser___Parser)

class Parser___Parser(Parser__, NamedTuple('Parser', [('fn', Any)])):
    def __dafnystr__(self) -> str:
        return f'Parsers.Parser_.Parser({_dafny.string_of(self.fn)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Parser___Parser) and self.fn == __o.fn
    def __hash__(self) -> int:
        return super().__hash__()


class SubParser__:
    @classmethod
    def default(cls, ):
        return lambda: None
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SubParser(self) -> bool:
        return isinstance(self, SubParser___SubParser)

class SubParser___SubParser(SubParser__, NamedTuple('SubParser', [('fn', Any)])):
    def __dafnystr__(self) -> str:
        return f'Parsers.SubParser_.SubParser({_dafny.string_of(self.fn)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SubParser___SubParser) and self.fn == __o.fn
    def __hash__(self) -> int:
        return super().__hash__()


class SubParser:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.SubParserWitness()
