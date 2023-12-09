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
import Std_JSON_Grammar
import Std_JSON_ByteStrConversion
import Std_JSON_Serializer
import Std_JSON_Deserializer_Uint16StrConversion
import Std_JSON_Deserializer

# Module: Std_JSON_ConcreteSyntax_Spec

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def View(v):
        return (v).Bytes()

    @staticmethod
    def Structural(self, fT):
        return ((default__.View((self).before)) + (fT((self).t))) + (default__.View((self).after))

    @staticmethod
    def StructuralView(self):
        return default__.Structural(self, default__.View)

    @staticmethod
    def Maybe(self, fT):
        if (self).is_Empty:
            return _dafny.SeqWithoutIsStrInference([])
        elif True:
            return fT((self).t)

    @staticmethod
    def ConcatBytes(ts, fT):
        d_524___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(ts)) == (0):
                    return (d_524___accumulator_) + (_dafny.SeqWithoutIsStrInference([]))
                elif True:
                    d_524___accumulator_ = (d_524___accumulator_) + (fT((ts)[0]))
                    in94_ = _dafny.SeqWithoutIsStrInference((ts)[1::])
                    in95_ = fT
                    ts = in94_
                    fT = in95_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Bracketed(self, fDatum):
        return ((default__.StructuralView((self).l)) + (default__.ConcatBytes((self).data, fDatum))) + (default__.StructuralView((self).r))

    @staticmethod
    def KeyValue(self):
        return ((default__.String((self).k)) + (default__.StructuralView((self).colon))) + (default__.Value((self).v))

    @staticmethod
    def Frac(self):
        return (default__.View((self).period)) + (default__.View((self).num))

    @staticmethod
    def Exp(self):
        return ((default__.View((self).e)) + (default__.View((self).sign))) + (default__.View((self).num))

    @staticmethod
    def Number(self):
        return (((default__.View((self).minus)) + (default__.View((self).num))) + (default__.Maybe((self).frac, default__.Frac))) + (default__.Maybe((self).exp, default__.Exp))

    @staticmethod
    def String(self):
        return ((default__.View((self).lq)) + (default__.View((self).contents))) + (default__.View((self).rq))

    @staticmethod
    def CommaSuffix(c):
        return default__.Maybe(c, default__.StructuralView)

    @staticmethod
    def Member(self):
        return (default__.KeyValue((self).t)) + (default__.CommaSuffix((self).suffix))

    @staticmethod
    def Item(self):
        return (default__.Value((self).t)) + (default__.CommaSuffix((self).suffix))

    @staticmethod
    def Object(obj):
        def lambda36_(d_525_obj_):
            def lambda37_(d_526_d_):
                return default__.Member(d_526_d_)

            return lambda37_

        return default__.Bracketed(obj, lambda36_(obj))

    @staticmethod
    def Array(arr):
        def lambda38_(d_527_arr_):
            def lambda39_(d_528_d_):
                return default__.Item(d_528_d_)

            return lambda39_

        return default__.Bracketed(arr, lambda38_(arr))

    @staticmethod
    def Value(self):
        source22_ = self
        if source22_.is_Null:
            d_529___mcc_h0_ = source22_.n
            d_530_n_ = d_529___mcc_h0_
            return default__.View(d_530_n_)
        elif source22_.is_Bool:
            d_531___mcc_h1_ = source22_.b
            d_532_b_ = d_531___mcc_h1_
            return default__.View(d_532_b_)
        elif source22_.is_String:
            d_533___mcc_h2_ = source22_.str
            d_534_str_ = d_533___mcc_h2_
            return default__.String(d_534_str_)
        elif source22_.is_Number:
            d_535___mcc_h3_ = source22_.num
            d_536_num_ = d_535___mcc_h3_
            return default__.Number(d_536_num_)
        elif source22_.is_Object:
            d_537___mcc_h4_ = source22_.obj
            d_538_obj_ = d_537___mcc_h4_
            return default__.Object(d_538_obj_)
        elif True:
            d_539___mcc_h5_ = source22_.arr
            d_540_arr_ = d_539___mcc_h5_
            return default__.Array(d_540_arr_)

    @staticmethod
    def JSON(js):
        return default__.Structural(js, default__.Value)

