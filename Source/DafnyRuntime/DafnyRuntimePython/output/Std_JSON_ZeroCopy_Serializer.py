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

# Module: Std_JSON_ZeroCopy_Serializer

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Serialize(js):
        rbs: Std_Wrappers.Result = Std_Wrappers.Result.default(_dafny.defaults.pointer)()
        d_549_writer_: Std_JSON_Utils_Views_Writers.Writer__
        d_549_writer_ = default__.Text(js)
        d_550_valueOrError0_: Std_Wrappers.OutcomeResult = Std_Wrappers.OutcomeResult.default()()
        d_550_valueOrError0_ = Std_Wrappers.default__.Need((d_549_writer_).Unsaturated_q, Std_JSON_Errors.SerializationError_OutOfMemory())
        if (d_550_valueOrError0_).IsFailure():
            rbs = (d_550_valueOrError0_).PropagateFailure()
            return rbs
        d_551_bs_: _dafny.Array
        out6_: _dafny.Array
        out6_ = (d_549_writer_).ToArray()
        d_551_bs_ = out6_
        rbs = Std_Wrappers.Result_Success(d_551_bs_)
        return rbs
        return rbs

    @staticmethod
    def SerializeTo(js, dest):
        len: Std_Wrappers.Result = Std_Wrappers.Result.default(Std_BoundedInts.uint32.default)()
        d_552_writer_: Std_JSON_Utils_Views_Writers.Writer__
        d_552_writer_ = default__.Text(js)
        d_553_valueOrError0_: Std_Wrappers.OutcomeResult = Std_Wrappers.OutcomeResult.default()()
        d_553_valueOrError0_ = Std_Wrappers.default__.Need((d_552_writer_).Unsaturated_q, Std_JSON_Errors.SerializationError_OutOfMemory())
        if (d_553_valueOrError0_).IsFailure():
            len = (d_553_valueOrError0_).PropagateFailure()
            return len
        d_554_valueOrError1_: Std_Wrappers.OutcomeResult = Std_Wrappers.OutcomeResult.default()()
        d_554_valueOrError1_ = Std_Wrappers.default__.Need(((d_552_writer_).length) <= ((dest).length(0)), Std_JSON_Errors.SerializationError_OutOfMemory())
        if (d_554_valueOrError1_).IsFailure():
            len = (d_554_valueOrError1_).PropagateFailure()
            return len
        (d_552_writer_).CopyTo(dest)
        len = Std_Wrappers.Result_Success((d_552_writer_).length)
        return len
        return len

    @staticmethod
    def Text(js):
        return default__.JSON(js, Std_JSON_Utils_Views_Writers.Writer__.Empty)

    @staticmethod
    def JSON(js, writer):
        def lambda40_(d_555_js_):
            def lambda41_(d_556_wr_):
                return default__.Value((d_555_js_).t, d_556_wr_)

            return lambda41_

        return (((writer).Append((js).before)).Then(lambda40_(js))).Append((js).after)

    @staticmethod
    def Value(v, writer):
        source23_ = v
        if source23_.is_Null:
            d_557___mcc_h0_ = source23_.n
            d_558_n_ = d_557___mcc_h0_
            d_559_wr_ = (writer).Append(d_558_n_)
            return d_559_wr_
        elif source23_.is_Bool:
            d_560___mcc_h1_ = source23_.b
            d_561_b_ = d_560___mcc_h1_
            d_562_wr_ = (writer).Append(d_561_b_)
            return d_562_wr_
        elif source23_.is_String:
            d_563___mcc_h2_ = source23_.str
            d_564_str_ = d_563___mcc_h2_
            d_565_wr_ = default__.String(d_564_str_, writer)
            return d_565_wr_
        elif source23_.is_Number:
            d_566___mcc_h3_ = source23_.num
            d_567_num_ = d_566___mcc_h3_
            d_568_wr_ = default__.Number(d_567_num_, writer)
            return d_568_wr_
        elif source23_.is_Object:
            d_569___mcc_h4_ = source23_.obj
            d_570_obj_ = d_569___mcc_h4_
            d_571_wr_ = default__.Object(d_570_obj_, writer)
            return d_571_wr_
        elif True:
            d_572___mcc_h5_ = source23_.arr
            d_573_arr_ = d_572___mcc_h5_
            d_574_wr_ = default__.Array(d_573_arr_, writer)
            return d_574_wr_

    @staticmethod
    def String(str, writer):
        return (((writer).Append((str).lq)).Append((str).contents)).Append((str).rq)

    @staticmethod
    def Number(num, writer):
        d_575_wr1_ = ((writer).Append((num).minus)).Append((num).num)
        d_576_wr2_ = (((d_575_wr1_).Append((((num).frac).t).period)).Append((((num).frac).t).num) if ((num).frac).is_NonEmpty else d_575_wr1_)
        d_577_wr3_ = ((((d_576_wr2_).Append((((num).exp).t).e)).Append((((num).exp).t).sign)).Append((((num).exp).t).num) if ((num).exp).is_NonEmpty else d_576_wr2_)
        d_578_wr_ = d_577_wr3_
        return d_578_wr_

    @staticmethod
    def StructuralView(st, writer):
        return (((writer).Append((st).before)).Append((st).t)).Append((st).after)

    @staticmethod
    def Object(obj, writer):
        d_579_wr_ = default__.StructuralView((obj).l, writer)
        d_580_wr_ = default__.Members(obj, d_579_wr_)
        d_581_wr_ = default__.StructuralView((obj).r, d_580_wr_)
        return d_581_wr_

    @staticmethod
    def Array(arr, writer):
        d_582_wr_ = default__.StructuralView((arr).l, writer)
        d_583_wr_ = default__.Items(arr, d_582_wr_)
        d_584_wr_ = default__.StructuralView((arr).r, d_583_wr_)
        return d_584_wr_

    @staticmethod
    def Members(obj, writer):
        wr: Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Writer.default()
        out7_: Std_JSON_Utils_Views_Writers.Writer__
        out7_ = default__.MembersImpl(obj, writer)
        wr = out7_
        return wr

    @staticmethod
    def Items(arr, writer):
        wr: Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Writer.default()
        out8_: Std_JSON_Utils_Views_Writers.Writer__
        out8_ = default__.ItemsImpl(arr, writer)
        wr = out8_
        return wr

    @staticmethod
    def MembersImpl(obj, writer):
        wr: Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Writer.default()
        wr = writer
        d_585_members_: _dafny.Seq
        d_585_members_ = (obj).data
        hi1_ = len(d_585_members_)
        for d_586_i_ in range(0, hi1_):
            wr = default__.Member((d_585_members_)[d_586_i_], wr)
        return wr

    @staticmethod
    def ItemsImpl(arr, writer):
        wr: Std_JSON_Utils_Views_Writers.Writer__ = Std_JSON_Utils_Views_Writers.Writer.default()
        wr = writer
        d_587_items_: _dafny.Seq
        d_587_items_ = (arr).data
        hi2_ = len(d_587_items_)
        for d_588_i_ in range(0, hi2_):
            wr = default__.Item((d_587_items_)[d_588_i_], wr)
        return wr

    @staticmethod
    def Member(m, writer):
        d_589_wr_ = default__.String(((m).t).k, writer)
        d_590_wr_ = default__.StructuralView(((m).t).colon, d_589_wr_)
        d_591_wr_ = default__.Value(((m).t).v, d_590_wr_)
        d_592_wr_ = (d_591_wr_ if ((m).suffix).is_Empty else default__.StructuralView(((m).suffix).t, d_591_wr_))
        return d_592_wr_

    @staticmethod
    def Item(m, writer):
        d_593_wr_ = default__.Value((m).t, writer)
        d_594_wr_ = (d_593_wr_ if ((m).suffix).is_Empty else default__.StructuralView(((m).suffix).t, d_593_wr_))
        return d_594_wr_

