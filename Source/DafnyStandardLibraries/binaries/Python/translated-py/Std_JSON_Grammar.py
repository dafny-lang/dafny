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
import Std_JSON_Utils_Lexers_Core
import Std_JSON_Utils_Lexers_Strings
import Std_JSON_Utils_Lexers
import Std_JSON_Utils_Cursors
import Std_JSON_Utils_Parsers
import Std_JSON_Utils

# Module: Std_JSON_Grammar

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Blank_q(b):
        return ((((b) == (32)) or ((b) == (9))) or ((b) == (10))) or ((b) == (13))

    @staticmethod
    def Digit_q(b):
        return ((ord(_dafny.CodePoint('0'))) <= (b)) and ((b) <= (ord(_dafny.CodePoint('9'))))

    @_dafny.classproperty
    def NULL(instance):
        return _dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('n')), ord(_dafny.CodePoint('u')), ord(_dafny.CodePoint('l')), ord(_dafny.CodePoint('l'))])
    @_dafny.classproperty
    def TRUE(instance):
        return _dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('t')), ord(_dafny.CodePoint('r')), ord(_dafny.CodePoint('u')), ord(_dafny.CodePoint('e'))])
    @_dafny.classproperty
    def FALSE(instance):
        return _dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('f')), ord(_dafny.CodePoint('a')), ord(_dafny.CodePoint('l')), ord(_dafny.CodePoint('s')), ord(_dafny.CodePoint('e'))])
    @_dafny.classproperty
    def DOUBLEQUOTE(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('\"'))]))
    @_dafny.classproperty
    def PERIOD(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('.'))]))
    @_dafny.classproperty
    def E(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('e'))]))
    @_dafny.classproperty
    def COLON(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint(':'))]))
    @_dafny.classproperty
    def COMMA(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint(','))]))
    @_dafny.classproperty
    def LBRACE(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('{'))]))
    @_dafny.classproperty
    def RBRACE(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('}'))]))
    @_dafny.classproperty
    def LBRACKET(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('['))]))
    @_dafny.classproperty
    def RBRACKET(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint(']'))]))
    @_dafny.classproperty
    def MINUS(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('-'))]))
    @_dafny.classproperty
    def EMPTY(instance):
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([]))

class jchar:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('b'))]))

class jquote:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.DOUBLEQUOTE

class jperiod:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.PERIOD

class je:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.E

class jcolon:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.COLON

class jcomma:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.COMMA

class jlbrace:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.LBRACE

class jrbrace:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.RBRACE

class jlbracket:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.LBRACKET

class jrbracket:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.RBRACKET

class jminus:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.MINUS

class jsign:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return default__.EMPTY

class jblanks:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([]))

class Structural:
    @classmethod
    def default(cls, default_T):
        return lambda: Structural_Structural(jblanks.default(), default_T(), jblanks.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Structural(self) -> bool:
        return isinstance(self, Structural_Structural)

class Structural_Structural(Structural, NamedTuple('Structural', [('before', Any), ('t', Any), ('after', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Structural.Structural({_dafny.string_of(self.before)}, {_dafny.string_of(self.t)}, {_dafny.string_of(self.after)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Structural_Structural) and self.before == __o.before and self.t == __o.t and self.after == __o.after
    def __hash__(self) -> int:
        return super().__hash__()


class Maybe:
    @classmethod
    def default(cls, ):
        return lambda: Maybe_Empty()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Empty(self) -> bool:
        return isinstance(self, Maybe_Empty)
    @property
    def is_NonEmpty(self) -> bool:
        return isinstance(self, Maybe_NonEmpty)

class Maybe_Empty(Maybe, NamedTuple('Empty', [])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Maybe.Empty'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Maybe_Empty)
    def __hash__(self) -> int:
        return super().__hash__()

class Maybe_NonEmpty(Maybe, NamedTuple('NonEmpty', [('t', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Maybe.NonEmpty({_dafny.string_of(self.t)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Maybe_NonEmpty) and self.t == __o.t
    def __hash__(self) -> int:
        return super().__hash__()


class Suffixed:
    @classmethod
    def default(cls, default_T):
        return lambda: Suffixed_Suffixed(default_T(), Maybe.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Suffixed(self) -> bool:
        return isinstance(self, Suffixed_Suffixed)

class Suffixed_Suffixed(Suffixed, NamedTuple('Suffixed', [('t', Any), ('suffix', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Suffixed.Suffixed({_dafny.string_of(self.t)}, {_dafny.string_of(self.suffix)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Suffixed_Suffixed) and self.t == __o.t and self.suffix == __o.suffix
    def __hash__(self) -> int:
        return super().__hash__()


class SuffixedSequence:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.Seq({})

class Bracketed:
    @classmethod
    def default(cls, default_L, default_R):
        return lambda: Bracketed_Bracketed(Structural.default(default_L)(), _dafny.Seq({}), Structural.default(default_R)())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Bracketed(self) -> bool:
        return isinstance(self, Bracketed_Bracketed)

class Bracketed_Bracketed(Bracketed, NamedTuple('Bracketed', [('l', Any), ('data', Any), ('r', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Bracketed.Bracketed({_dafny.string_of(self.l)}, {_dafny.string_of(self.data)}, {_dafny.string_of(self.r)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Bracketed_Bracketed) and self.l == __o.l and self.data == __o.data and self.r == __o.r
    def __hash__(self) -> int:
        return super().__hash__()


class jnull:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(default__.NULL)

class jbool:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(default__.TRUE)

class jdigits:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([]))

class jnum:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('0'))]))

class jint:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([ord(_dafny.CodePoint('0'))]))

class jstr:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return Std_JSON_Utils_Views_Core.View__.OfBytes(_dafny.SeqWithoutIsStrInference([]))

class jstring:
    @classmethod
    def default(cls, ):
        return lambda: jstring_JString(jquote.default(), jstr.default(), jquote.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JString(self) -> bool:
        return isinstance(self, jstring_JString)

class jstring_JString(jstring, NamedTuple('JString', [('lq', Any), ('contents', Any), ('rq', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.jstring.JString({_dafny.string_of(self.lq)}, {_dafny.string_of(self.contents)}, {_dafny.string_of(self.rq)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, jstring_JString) and self.lq == __o.lq and self.contents == __o.contents and self.rq == __o.rq
    def __hash__(self) -> int:
        return super().__hash__()


class jKeyValue:
    @classmethod
    def default(cls, ):
        return lambda: jKeyValue_KeyValue(jstring.default()(), Structural.default(jcolon.default)(), Value.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_KeyValue(self) -> bool:
        return isinstance(self, jKeyValue_KeyValue)

class jKeyValue_KeyValue(jKeyValue, NamedTuple('KeyValue', [('k', Any), ('colon', Any), ('v', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.jKeyValue.KeyValue({_dafny.string_of(self.k)}, {_dafny.string_of(self.colon)}, {_dafny.string_of(self.v)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, jKeyValue_KeyValue) and self.k == __o.k and self.colon == __o.colon and self.v == __o.v
    def __hash__(self) -> int:
        return super().__hash__()


class jfrac:
    @classmethod
    def default(cls, ):
        return lambda: jfrac_JFrac(jperiod.default(), jnum.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JFrac(self) -> bool:
        return isinstance(self, jfrac_JFrac)

class jfrac_JFrac(jfrac, NamedTuple('JFrac', [('period', Any), ('num', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.jfrac.JFrac({_dafny.string_of(self.period)}, {_dafny.string_of(self.num)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, jfrac_JFrac) and self.period == __o.period and self.num == __o.num
    def __hash__(self) -> int:
        return super().__hash__()


class jexp:
    @classmethod
    def default(cls, ):
        return lambda: jexp_JExp(je.default(), jsign.default(), jnum.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JExp(self) -> bool:
        return isinstance(self, jexp_JExp)

class jexp_JExp(jexp, NamedTuple('JExp', [('e', Any), ('sign', Any), ('num', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.jexp.JExp({_dafny.string_of(self.e)}, {_dafny.string_of(self.sign)}, {_dafny.string_of(self.num)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, jexp_JExp) and self.e == __o.e and self.sign == __o.sign and self.num == __o.num
    def __hash__(self) -> int:
        return super().__hash__()


class jnumber:
    @classmethod
    def default(cls, ):
        return lambda: jnumber_JNumber(jminus.default(), jnum.default(), Maybe.default()(), Maybe.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_JNumber(self) -> bool:
        return isinstance(self, jnumber_JNumber)

class jnumber_JNumber(jnumber, NamedTuple('JNumber', [('minus', Any), ('num', Any), ('frac', Any), ('exp', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.jnumber.JNumber({_dafny.string_of(self.minus)}, {_dafny.string_of(self.num)}, {_dafny.string_of(self.frac)}, {_dafny.string_of(self.exp)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, jnumber_JNumber) and self.minus == __o.minus and self.num == __o.num and self.frac == __o.frac and self.exp == __o.exp
    def __hash__(self) -> int:
        return super().__hash__()


class Value:
    @classmethod
    def default(cls, ):
        return lambda: Value_Null(jnull.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Null(self) -> bool:
        return isinstance(self, Value_Null)
    @property
    def is_Bool(self) -> bool:
        return isinstance(self, Value_Bool)
    @property
    def is_String(self) -> bool:
        return isinstance(self, Value_String)
    @property
    def is_Number(self) -> bool:
        return isinstance(self, Value_Number)
    @property
    def is_Object(self) -> bool:
        return isinstance(self, Value_Object)
    @property
    def is_Array(self) -> bool:
        return isinstance(self, Value_Array)

class Value_Null(Value, NamedTuple('Null', [('n', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.Null({_dafny.string_of(self.n)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_Null) and self.n == __o.n
    def __hash__(self) -> int:
        return super().__hash__()

class Value_Bool(Value, NamedTuple('Bool', [('b', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.Bool({_dafny.string_of(self.b)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_Bool) and self.b == __o.b
    def __hash__(self) -> int:
        return super().__hash__()

class Value_String(Value, NamedTuple('String', [('str', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.String({_dafny.string_of(self.str)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_String) and self.str == __o.str
    def __hash__(self) -> int:
        return super().__hash__()

class Value_Number(Value, NamedTuple('Number', [('num', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.Number({_dafny.string_of(self.num)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_Number) and self.num == __o.num
    def __hash__(self) -> int:
        return super().__hash__()

class Value_Object(Value, NamedTuple('Object', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.Object({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_Object) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()

class Value_Array(Value, NamedTuple('Array', [('arr', Any)])):
    def __dafnystr__(self) -> str:
        return f'Grammar.Value.Array({_dafny.string_of(self.arr)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Value_Array) and self.arr == __o.arr
    def __hash__(self) -> int:
        return super().__hash__()

