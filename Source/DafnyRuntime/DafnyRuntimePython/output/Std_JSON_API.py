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
import Std_JSON_Utils_Parsers
import Std_JSON_Utils
import Std_JSON_Grammar
import Std_JSON_ByteStrConversion
import Std_JSON_Serializer
import Std_JSON_Deserializer_Uint16StrConversion
import Std_JSON_Deserializer
import Std_JSON_ConcreteSyntax_Spec
import Std_JSON_ConcreteSyntax_SpecProperties
import Std_JSON_ConcreteSyntax
import Std_JSON_ZeroCopy_Serializer
import Std_JSON_ZeroCopy_Deserializer_Core
import Std_JSON_ZeroCopy_Deserializer_Strings
import Std_JSON_ZeroCopy_Deserializer_Numbers
import Std_JSON_ZeroCopy_Deserializer_ObjectParams
import Std_JSON_ZeroCopy_Deserializer_Objects
import Std_JSON_ZeroCopy_Deserializer_ArrayParams
import Std_JSON_ZeroCopy_Deserializer_Arrays
import Std_JSON_ZeroCopy_Deserializer_Constants
import Std_JSON_ZeroCopy_Deserializer_Values
import Std_JSON_ZeroCopy_Deserializer_API
import Std_JSON_ZeroCopy_Deserializer
import Std_JSON_ZeroCopy_API
import Std_JSON_ZeroCopy

# Module: Std_JSON_API

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Serialize(js):
        d_773_valueOrError0_ = Std_JSON_Serializer.default__.JSON(js)
        if (d_773_valueOrError0_).IsFailure():
            return (d_773_valueOrError0_).PropagateFailure()
        elif True:
            d_774_js_ = (d_773_valueOrError0_).Extract()
            return Std_JSON_ZeroCopy_API.default__.Serialize(d_774_js_)

    @staticmethod
    def SerializeAlloc(js):
        bs: Std_Wrappers.Result = Std_Wrappers.Result.default(_dafny.defaults.pointer)()
        d_775_js_: Std_JSON_Grammar.Structural
        d_776_valueOrError0_: Std_Wrappers.Result = Std_Wrappers.Result.default(Std_JSON_Grammar.Structural.default(Std_JSON_Grammar.Value.default()))()
        d_776_valueOrError0_ = Std_JSON_Serializer.default__.JSON(js)
        if (d_776_valueOrError0_).IsFailure():
            bs = (d_776_valueOrError0_).PropagateFailure()
            return bs
        d_775_js_ = (d_776_valueOrError0_).Extract()
        out11_: Std_Wrappers.Result
        out11_ = Std_JSON_ZeroCopy_API.default__.SerializeAlloc(d_775_js_)
        bs = out11_
        return bs

    @staticmethod
    def SerializeInto(js, bs):
        len: Std_Wrappers.Result = Std_Wrappers.Result.default(Std_BoundedInts.uint32.default)()
        d_777_js_: Std_JSON_Grammar.Structural
        d_778_valueOrError0_: Std_Wrappers.Result = Std_Wrappers.Result.default(Std_JSON_Grammar.Structural.default(Std_JSON_Grammar.Value.default()))()
        d_778_valueOrError0_ = Std_JSON_Serializer.default__.JSON(js)
        if (d_778_valueOrError0_).IsFailure():
            len = (d_778_valueOrError0_).PropagateFailure()
            return len
        d_777_js_ = (d_778_valueOrError0_).Extract()
        out12_: Std_Wrappers.Result
        out12_ = Std_JSON_ZeroCopy_API.default__.SerializeInto(d_777_js_, bs)
        len = out12_
        return len

    @staticmethod
    def Deserialize(bs):
        d_779_valueOrError0_ = Std_JSON_ZeroCopy_API.default__.Deserialize(bs)
        if (d_779_valueOrError0_).IsFailure():
            return (d_779_valueOrError0_).PropagateFailure()
        elif True:
            d_780_js_ = (d_779_valueOrError0_).Extract()
            return Std_JSON_Deserializer.default__.JSON(d_780_js_)

