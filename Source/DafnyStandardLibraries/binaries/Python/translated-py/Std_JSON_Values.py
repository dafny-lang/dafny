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

# Module: Std_JSON_Values

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Int(n):
        return Decimal_Decimal(n, 0)


class Decimal:
    @classmethod
    def default(cls, ):
        return lambda: Decimal_Decimal(int(0), int(0))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Decimal(self) -> bool:
        return isinstance(self, Decimal_Decimal)

class Decimal_Decimal(Decimal, NamedTuple('Decimal', [('n', Any), ('e10', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.Decimal.Decimal({_dafny.string_of(self.n)}, {_dafny.string_of(self.e10)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Decimal_Decimal) and self.n == __o.n and self.e10 == __o.e10
    def __hash__(self) -> int:
        return super().__hash__()


class JSON:
    @classmethod
    def default(cls, ):
        return lambda: JSON_Null()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Null(self) -> bool:
        return isinstance(self, JSON_Null)
    @property
    def is_Bool(self) -> bool:
        return isinstance(self, JSON_Bool)
    @property
    def is_String(self) -> bool:
        return isinstance(self, JSON_String)
    @property
    def is_Number(self) -> bool:
        return isinstance(self, JSON_Number)
    @property
    def is_Object(self) -> bool:
        return isinstance(self, JSON_Object)
    @property
    def is_Array(self) -> bool:
        return isinstance(self, JSON_Array)

class JSON_Null(JSON, NamedTuple('Null', [])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.Null'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_Null)
    def __hash__(self) -> int:
        return super().__hash__()

class JSON_Bool(JSON, NamedTuple('Bool', [('b', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.Bool({_dafny.string_of(self.b)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_Bool) and self.b == __o.b
    def __hash__(self) -> int:
        return super().__hash__()

class JSON_String(JSON, NamedTuple('String', [('str', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.String({self.str.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_String) and self.str == __o.str
    def __hash__(self) -> int:
        return super().__hash__()

class JSON_Number(JSON, NamedTuple('Number', [('num', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.Number({_dafny.string_of(self.num)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_Number) and self.num == __o.num
    def __hash__(self) -> int:
        return super().__hash__()

class JSON_Object(JSON, NamedTuple('Object', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.Object({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_Object) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()

class JSON_Array(JSON, NamedTuple('Array', [('arr', Any)])):
    def __dafnystr__(self) -> str:
        return f'Values.JSON.Array({_dafny.string_of(self.arr)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, JSON_Array) and self.arr == __o.arr
    def __hash__(self) -> int:
        return super().__hash__()

