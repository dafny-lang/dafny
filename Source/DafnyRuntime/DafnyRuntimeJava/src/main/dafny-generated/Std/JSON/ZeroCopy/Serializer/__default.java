// Class __default
// Dafny class __default compiled into Java
package Std.JSON.ZeroCopy.Serializer;

import Std.Wrappers.*;
import Std.BoundedInts.*;
import Std.Base64.*;
import Std.Math.*;
import Std.Collections.Seq.*;
import Std.Collections.Array.*;
import Std.Collections.Imap.*;
import Std.Collections.Map.*;
import Std.Collections.Set.*;
import Std.DynamicArray.*;
import Std.FileIO.*;
import Std.Arithmetic.MulInternals.*;
import Std.Arithmetic.ModInternals.*;
import Std.Arithmetic.DivInternals.*;
import Std.Arithmetic.DivMod.*;
import Std.Arithmetic.Power.*;
import Std.Arithmetic.Logarithm.*;
import Std.Arithmetic.Power2.*;
import Std.Strings.HexConversion.*;
import Std.Strings.DecimalConversion.*;
import Std.Strings.CharStrEscaping.*;
import Std.Strings.*;
import Std.Unicode.Base.*;
import Std.Unicode.Utf8EncodingForm.*;
import Std.Unicode.Utf16EncodingForm.*;
import Std.Unicode.UnicodeStringsWithUnicodeChar.*;
import Std.Unicode.Utf8EncodingScheme.*;
import Std.JavaFileIOInternalExterns.*;
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;
import Std.JSON.Utils.Cursors.*;
import Std.JSON.Utils.Parsers.*;
import Std.JSON.Grammar.*;
import Std.JSON.ByteStrConversion.*;
import Std.JSON.Serializer.*;
import Std.JSON.Deserializer.Uint16StrConversion.*;
import Std.JSON.Deserializer.*;
import Std.JSON.ConcreteSyntax.Spec.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> Serialize(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js)
  {
    Std.Wrappers.Result<byte[], Std.JSON.Errors.SerializationError> rbs = Std.Wrappers.Result.<byte[], Std.JSON.Errors.SerializationError>Default(dafny.TypeDescriptor.BYTE_ARRAY, Std.JSON.Errors.SerializationError._typeDescriptor(), new byte[0]);
    Std.JSON.Utils.Views.Writers.Writer__ _575_writer;
    _575_writer = __default.Text(js);
    Std.Wrappers.OutcomeResult<Std.JSON.Errors.SerializationError> _576_valueOrError0 = Std.Wrappers.OutcomeResult.<Std.JSON.Errors.SerializationError>Default(Std.JSON.Errors.SerializationError._typeDescriptor());
    _576_valueOrError0 = Std.Wrappers.__default.<Std.JSON.Errors.SerializationError>Need(Std.JSON.Errors.SerializationError._typeDescriptor(), (_575_writer).Unsaturated_q(), Std.JSON.Errors.SerializationError.create_OutOfMemory());
    if ((_576_valueOrError0).IsFailure(Std.JSON.Errors.SerializationError._typeDescriptor())) {
      rbs = (_576_valueOrError0).<byte[]>PropagateFailure(Std.JSON.Errors.SerializationError._typeDescriptor(), dafny.TypeDescriptor.BYTE_ARRAY);
      return rbs;
    }
    byte[] _577_bs;
    byte[] _out11;
    _out11 = (_575_writer).ToArray();
    _577_bs = _out11;
    rbs = Std.Wrappers.Result.<byte[], Std.JSON.Errors.SerializationError>create_Success(dafny.TypeDescriptor.BYTE_ARRAY, Std.JSON.Errors.SerializationError._typeDescriptor(), _577_bs);
    return rbs;
  }
  public static Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> SerializeTo(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js, byte[] dest)
  {
    Std.Wrappers.Result<java.lang.Integer, Std.JSON.Errors.SerializationError> len = Std.Wrappers.Result.<java.lang.Integer, Std.JSON.Errors.SerializationError>Default(Std.BoundedInts.uint32._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), 0);
    Std.JSON.Utils.Views.Writers.Writer__ _578_writer;
    _578_writer = __default.Text(js);
    Std.Wrappers.OutcomeResult<Std.JSON.Errors.SerializationError> _579_valueOrError0 = Std.Wrappers.OutcomeResult.<Std.JSON.Errors.SerializationError>Default(Std.JSON.Errors.SerializationError._typeDescriptor());
    _579_valueOrError0 = Std.Wrappers.__default.<Std.JSON.Errors.SerializationError>Need(Std.JSON.Errors.SerializationError._typeDescriptor(), (_578_writer).Unsaturated_q(), Std.JSON.Errors.SerializationError.create_OutOfMemory());
    if ((_579_valueOrError0).IsFailure(Std.JSON.Errors.SerializationError._typeDescriptor())) {
      len = (_579_valueOrError0).<java.lang.Integer>PropagateFailure(Std.JSON.Errors.SerializationError._typeDescriptor(), Std.BoundedInts.uint32._typeDescriptor());
      return len;
    }
    Std.Wrappers.OutcomeResult<Std.JSON.Errors.SerializationError> _580_valueOrError1 = Std.Wrappers.OutcomeResult.<Std.JSON.Errors.SerializationError>Default(Std.JSON.Errors.SerializationError._typeDescriptor());
    _580_valueOrError1 = Std.Wrappers.__default.<Std.JSON.Errors.SerializationError>Need(Std.JSON.Errors.SerializationError._typeDescriptor(), (dafny.Helpers.unsignedToBigInteger((_578_writer).dtor_length())).compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength((dest)))) <= 0, Std.JSON.Errors.SerializationError.create_OutOfMemory());
    if ((_580_valueOrError1).IsFailure(Std.JSON.Errors.SerializationError._typeDescriptor())) {
      len = (_580_valueOrError1).<java.lang.Integer>PropagateFailure(Std.JSON.Errors.SerializationError._typeDescriptor(), Std.BoundedInts.uint32._typeDescriptor());
      return len;
    }
    (_578_writer).CopyTo(dest);
    len = Std.Wrappers.Result.<java.lang.Integer, Std.JSON.Errors.SerializationError>create_Success(Std.BoundedInts.uint32._typeDescriptor(), Std.JSON.Errors.SerializationError._typeDescriptor(), (_578_writer).dtor_length());
    return len;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Text(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js) {
    return __default.JSON(js, Std.JSON.Utils.Views.Writers.Writer__.Empty());
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ JSON(Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value> js, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    return (((writer).Append((js).dtor_before())).Then(((java.util.function.Function<Std.JSON.Grammar.Structural<Std.JSON.Grammar.Value>, java.util.function.Function<Std.JSON.Utils.Views.Writers.Writer__, Std.JSON.Utils.Views.Writers.Writer__>>)(_581_js) -> ((java.util.function.Function<Std.JSON.Utils.Views.Writers.Writer__, Std.JSON.Utils.Views.Writers.Writer__>)(_582_wr_boxed0) -> {
      Std.JSON.Utils.Views.Writers.Writer__ _582_wr = ((Std.JSON.Utils.Views.Writers.Writer__)(java.lang.Object)(_582_wr_boxed0));
      return __default.Value((_581_js).dtor_t(), _582_wr);
    })).apply(js))).Append((js).dtor_after());
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Value(Std.JSON.Grammar.Value v, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Grammar.Value _source23 = v;
    if (_source23.is_Null()) {
      Std.JSON.Utils.Views.Core.View__ _583___mcc_h0 = ((Std.JSON.Grammar.Value_Null)_source23)._n;
      Std.JSON.Utils.Views.Core.View__ _584_n = _583___mcc_h0;
      Std.JSON.Utils.Views.Writers.Writer__ _585_wr = (writer).Append(_584_n);
      return _585_wr;
    } else if (_source23.is_Bool()) {
      Std.JSON.Utils.Views.Core.View__ _586___mcc_h1 = ((Std.JSON.Grammar.Value_Bool)_source23)._b;
      Std.JSON.Utils.Views.Core.View__ _587_b = _586___mcc_h1;
      Std.JSON.Utils.Views.Writers.Writer__ _588_wr = (writer).Append(_587_b);
      return _588_wr;
    } else if (_source23.is_String()) {
      Std.JSON.Grammar.jstring _589___mcc_h2 = ((Std.JSON.Grammar.Value_String)_source23)._str;
      Std.JSON.Grammar.jstring _590_str = _589___mcc_h2;
      Std.JSON.Utils.Views.Writers.Writer__ _591_wr = __default.String(_590_str, writer);
      return _591_wr;
    } else if (_source23.is_Number()) {
      Std.JSON.Grammar.jnumber _592___mcc_h3 = ((Std.JSON.Grammar.Value_Number)_source23)._num;
      Std.JSON.Grammar.jnumber _593_num = _592___mcc_h3;
      Std.JSON.Utils.Views.Writers.Writer__ _594_wr = __default.Number(_593_num, writer);
      return _594_wr;
    } else if (_source23.is_Object()) {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _595___mcc_h4 = ((Std.JSON.Grammar.Value_Object)_source23)._obj;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _596_obj = _595___mcc_h4;
      Std.JSON.Utils.Views.Writers.Writer__ _597_wr = __default.Object(_596_obj, writer);
      return _597_wr;
    } else {
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _598___mcc_h5 = ((Std.JSON.Grammar.Value_Array)_source23)._arr;
      Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> _599_arr = _598___mcc_h5;
      Std.JSON.Utils.Views.Writers.Writer__ _600_wr = __default.Array(_599_arr, writer);
      return _600_wr;
    }
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ String(Std.JSON.Grammar.jstring str, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    return (((writer).Append((str).dtor_lq())).Append((str).dtor_contents())).Append((str).dtor_rq());
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Number(Std.JSON.Grammar.jnumber num, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ _601_wr1 = ((writer).Append((num).dtor_minus())).Append((num).dtor_num());
    Std.JSON.Utils.Views.Writers.Writer__ _602_wr2 = ((((num).dtor_frac()).is_NonEmpty()) ? (((_601_wr1).Append((((num).dtor_frac()).dtor_t()).dtor_period())).Append((((num).dtor_frac()).dtor_t()).dtor_num())) : (_601_wr1));
    Std.JSON.Utils.Views.Writers.Writer__ _603_wr3 = ((((num).dtor_exp()).is_NonEmpty()) ? ((((_602_wr2).Append((((num).dtor_exp()).dtor_t()).dtor_e())).Append((((num).dtor_exp()).dtor_t()).dtor_sign())).Append((((num).dtor_exp()).dtor_t()).dtor_num())) : (_602_wr2));
    Std.JSON.Utils.Views.Writers.Writer__ _604_wr = _603_wr3;
    return _604_wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ StructuralView(Std.JSON.Grammar.Structural<Std.JSON.Utils.Views.Core.View__> st, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    return (((writer).Append((st).dtor_before())).Append((st).dtor_t())).Append((st).dtor_after());
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Object(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> obj, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ _605_wr = __default.StructuralView((obj).dtor_l(), writer);
    Std.JSON.Utils.Views.Writers.Writer__ _606_wr = __default.Members(obj, _605_wr);
    Std.JSON.Utils.Views.Writers.Writer__ _607_wr = __default.StructuralView((obj).dtor_r(), _606_wr);
    return _607_wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Array(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> arr, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ _608_wr = __default.StructuralView((arr).dtor_l(), writer);
    Std.JSON.Utils.Views.Writers.Writer__ _609_wr = __default.Items(arr, _608_wr);
    Std.JSON.Utils.Views.Writers.Writer__ _610_wr = __default.StructuralView((arr).dtor_r(), _609_wr);
    return _610_wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Members(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> obj, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ wr = Std.JSON.Utils.Views.Writers.Writer.defaultValue();
    if(true) {
      Std.JSON.Utils.Views.Writers.Writer__ _out12;
      _out12 = __default.MembersImpl(obj, writer);
      wr = _out12;
    }
    return wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Items(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> arr, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ wr = Std.JSON.Utils.Views.Writers.Writer.defaultValue();
    if(true) {
      Std.JSON.Utils.Views.Writers.Writer__ _out13;
      _out13 = __default.ItemsImpl(arr, writer);
      wr = _out13;
    }
    return wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ MembersImpl(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> obj, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ wr = Std.JSON.Utils.Views.Writers.Writer.defaultValue();
    if(true) {
      wr = writer;
      dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>> _611_members;
      _611_members = (obj).dtor_data();
      java.math.BigInteger _hi1 = java.math.BigInteger.valueOf((_611_members).length());
      for (java.math.BigInteger _612_i = java.math.BigInteger.ZERO; _612_i.compareTo(_hi1) < 0; _612_i = _612_i.add(java.math.BigInteger.ONE)) {
        wr = __default.Member(((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)((_611_members).select(dafny.Helpers.toInt((_612_i))))), wr);
      }
    }
    return wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ ItemsImpl(Std.JSON.Grammar.Bracketed<Std.JSON.Utils.Views.Core.View__, Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> arr, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ wr = Std.JSON.Utils.Views.Writers.Writer.defaultValue();
    if(true) {
      wr = writer;
      dafny.DafnySequence<? extends Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>> _613_items;
      _613_items = (arr).dtor_data();
      java.math.BigInteger _hi2 = java.math.BigInteger.valueOf((_613_items).length());
      for (java.math.BigInteger _614_i = java.math.BigInteger.ZERO; _614_i.compareTo(_hi2) < 0; _614_i = _614_i.add(java.math.BigInteger.ONE)) {
        wr = __default.Item(((Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__>)(java.lang.Object)((_613_items).select(dafny.Helpers.toInt((_614_i))))), wr);
      }
    }
    return wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Member(Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.jKeyValue, Std.JSON.Utils.Views.Core.View__> m, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ _615_wr = __default.String(((m).dtor_t()).dtor_k(), writer);
    Std.JSON.Utils.Views.Writers.Writer__ _616_wr = __default.StructuralView(((m).dtor_t()).dtor_colon(), _615_wr);
    Std.JSON.Utils.Views.Writers.Writer__ _617_wr = __default.Value(((m).dtor_t()).dtor_v(), _616_wr);
    Std.JSON.Utils.Views.Writers.Writer__ _618_wr = ((((m).dtor_suffix()).is_Empty()) ? (_617_wr) : (__default.StructuralView(((m).dtor_suffix()).dtor_t(), _617_wr)));
    return _618_wr;
  }
  public static Std.JSON.Utils.Views.Writers.Writer__ Item(Std.JSON.Grammar.Suffixed<Std.JSON.Grammar.Value, Std.JSON.Utils.Views.Core.View__> m, Std.JSON.Utils.Views.Writers.Writer__ writer)
  {
    Std.JSON.Utils.Views.Writers.Writer__ _619_wr = __default.Value((m).dtor_t(), writer);
    Std.JSON.Utils.Views.Writers.Writer__ _620_wr = ((((m).dtor_suffix()).is_Empty()) ? (_619_wr) : (__default.StructuralView(((m).dtor_suffix()).dtor_t(), _619_wr)));
    return _620_wr;
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.ZeroCopy.Serializer._default";
  }
}
