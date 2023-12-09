// Class Cursor__
// Dafny class Cursor__ compiled into Java
package Std.JSON.Utils.Cursors;

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
import Std.JSON.Values.*;
import Std.JSON.Errors.*;
import Std.JSON.Spec.*;
import Std.JSON.Utils.Views.Core.*;
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;
import Std.JSON.Utils.Lexers.Strings.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Cursor__ {
  public dafny.DafnySequence<? extends java.lang.Byte> _s;
  public int _beg;
  public int _point;
  public int _end;
  public Cursor__ (dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int point, int end) {
    this._s = s;
    this._beg = beg;
    this._point = point;
    this._end = end;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Cursor__ o = (Cursor__)other;
    return true && java.util.Objects.equals(this._s, o._s) && this._beg == o._beg && this._point == o._point && this._end == o._end;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._s);
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._beg);
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._point);
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._end);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder ss = new StringBuilder();
    ss.append("Cursors.Cursor_.Cursor");
    ss.append("(");
    ss.append(dafny.Helpers.toString(this._s));
    ss.append(", ");
    ss.append(this._beg);
    ss.append(", ");
    ss.append(this._point);
    ss.append(", ");
    ss.append(this._end);
    ss.append(")");
    return ss.toString();
  }

  private static final Cursor__ theDefault = Std.JSON.Utils.Cursors.Cursor__.create(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), 0, 0, 0);
  public static Cursor__ Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Cursor__> _TYPE = dafny.TypeDescriptor.<Cursor__>referenceWithInitializer(Cursor__.class, () -> Cursor__.Default());
  public static dafny.TypeDescriptor<Cursor__> _typeDescriptor() {
    return (dafny.TypeDescriptor<Cursor__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Cursor__ create(dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int point, int end) {
    return new Cursor__(s, beg, point, end);
  }
  public static Cursor__ create_Cursor(dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int point, int end) {
    return create(s, beg, point, end);
  }
  public boolean is_Cursor() { return true; }
  public dafny.DafnySequence<? extends java.lang.Byte> dtor_s() {
    return this._s;
  }
  public int dtor_beg() {
    return this._beg;
  }
  public int dtor_point() {
    return this._point;
  }
  public int dtor_end() {
    return this._end;
  }
  public static Cursor__ OfView(Std.JSON.Utils.Views.Core.View__ v) {
    return Std.JSON.Utils.Cursors.Cursor__.create((v).dtor_s(), (v).dtor_beg(), (v).dtor_beg(), (v).dtor_end());
  }
  public static Cursor__ OfBytes(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    return Std.JSON.Utils.Cursors.Cursor__.create(bs, 0, 0, (bs).cardinalityInt());
  }
  public dafny.DafnySequence<? extends java.lang.Byte> Bytes() {
    return ((this).dtor_s()).subsequence((this).dtor_beg(), (this).dtor_end());
  }
  public Std.JSON.Utils.Views.Core.View__ Prefix() {
    return Std.JSON.Utils.Views.Core.View__.create((this).dtor_s(), (this).dtor_beg(), (this).dtor_point());
  }
  public Cursor__ Suffix() {
    Cursor__ _384_dt__update__tmp_h0 = this;
    int _385_dt__update_hbeg_h0 = (this).dtor_point();
    return Std.JSON.Utils.Cursors.Cursor__.create((_384_dt__update__tmp_h0).dtor_s(), _385_dt__update_hbeg_h0, (_384_dt__update__tmp_h0).dtor_point(), (_384_dt__update__tmp_h0).dtor_end());
  }
  public Split<Std.JSON.Utils.Views.Core.View__> Split() {
    return Std.JSON.Utils.Cursors.Split.<Std.JSON.Utils.Views.Core.View__>create(Std.JSON.Utils.Views.Core.View._typeDescriptor(), (this).Prefix(), (this).Suffix());
  }
  public int PrefixLength() {
    return (int)  (((this).dtor_point()) - ((this).dtor_beg()));
  }
  public int SuffixLength() {
    return (int)  (((this).dtor_end()) - ((this).dtor_point()));
  }
  public int Length() {
    return (int)  (((this).dtor_end()) - ((this).dtor_beg()));
  }
  public byte At(int idx) {
    return ((byte)(java.lang.Object)(((this).dtor_s()).select((int)  (((this).dtor_beg()) + (idx)))));
  }
  public byte SuffixAt(int idx) {
    return ((byte)(java.lang.Object)(((this).dtor_s()).select((int)  (((this).dtor_point()) + (idx)))));
  }
  public short Peek() {
    if ((this).EOF_q()) {
      return (short) -1;
    } else {
      return (short) java.lang.Byte.toUnsignedInt((this).SuffixAt(0));
    }
  }
  public boolean LookingAt(int c) {
    return ((this).Peek()) == (((short) (c)));
  }
  public Cursor__ Skip(int n) {
    Cursor__ _386_dt__update__tmp_h0 = this;
    int _387_dt__update_hpoint_h0 = (int)  (((this).dtor_point()) + (n));
    return Std.JSON.Utils.Cursors.Cursor__.create((_386_dt__update__tmp_h0).dtor_s(), (_386_dt__update__tmp_h0).dtor_beg(), _387_dt__update_hpoint_h0, (_386_dt__update__tmp_h0).dtor_end());
  }
  public Cursor__ Unskip(int n) {
    Cursor__ _388_dt__update__tmp_h0 = this;
    int _389_dt__update_hpoint_h0 = (int)  (((this).dtor_point()) - (n));
    return Std.JSON.Utils.Cursors.Cursor__.create((_388_dt__update__tmp_h0).dtor_s(), (_388_dt__update__tmp_h0).dtor_beg(), _389_dt__update_hpoint_h0, (_388_dt__update__tmp_h0).dtor_end());
  }
  public <__R> Std.Wrappers.Result<Cursor__, CursorError<__R>> Get(dafny.TypeDescriptor<__R> _td___R, __R err)
  {
    if ((this).EOF_q()) {
      return Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Failure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_OtherError(_td___R, err));
    } else {
      return Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Success(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), (this).Skip(1));
    }
  }
  public <__R> Std.Wrappers.Result<Cursor__, CursorError<__R>> AssertByte(dafny.TypeDescriptor<__R> _td___R, byte b)
  {
    short _390_nxt = (this).Peek();
    if ((_390_nxt) == ((short) java.lang.Byte.toUnsignedInt(b))) {
      return Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Success(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), (this).Skip(1));
    } else {
      return Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Failure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_ExpectingByte(_td___R, b, _390_nxt));
    }
  }
  public <__R> Std.Wrappers.Result<Cursor__, CursorError<__R>> AssertBytes(dafny.TypeDescriptor<__R> _td___R, dafny.DafnySequence<? extends java.lang.Byte> bs, int offset)
  {
    Cursor__ _this = this;
    TAIL_CALL_START: while (true) {
      if ((offset) == ((bs).cardinalityInt())) {
        return Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Success(Cursor__._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), _this);
      } else {
        Std.Wrappers.Result<Cursor__, CursorError<__R>> _391_valueOrError0 = (_this).<__R>AssertByte(_td___R, (((byte)(java.lang.Object)((bs).select(offset)))));
        if ((_391_valueOrError0).IsFailure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R))) {
          return (_391_valueOrError0).<Cursor__>PropagateFailure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Cursor__._typeDescriptor());
        } else {
          Cursor__ _392_ps = (_391_valueOrError0).Extract(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R));
          Cursor__ _in69 = _392_ps;
          dafny.DafnySequence<? extends java.lang.Byte> _in70 = bs;
          int _in71 = (int)  ((offset) + (1));
          _this = _in69;
          ;
          bs = _in70;
          offset = _in71;
          continue TAIL_CALL_START;
        }
      }
    }
  }
  public <__R> Std.Wrappers.Result<Cursor__, CursorError<__R>> AssertChar(dafny.TypeDescriptor<__R> _td___R, int c0)
  {
    return (this).<__R>AssertByte(_td___R, ((byte) (c0)));
  }
  public Cursor__ SkipByte() {
    if ((this).EOF_q()) {
      return this;
    } else {
      return (this).Skip(1);
    }
  }
  public Cursor__ SkipIf(java.util.function.Function<java.lang.Byte, Boolean> p) {
    if (((this).EOF_q()) || (!(((boolean)(java.lang.Object)((p).apply((this).SuffixAt(0))))))) {
      return this;
    } else {
      return (this).Skip(1);
    }
  }
  public Cursor__ SkipWhile(java.util.function.Function<java.lang.Byte, Boolean> p)
  {
    Cursor__ ps = Cursor.defaultValue();
    int _393_point_k;
    _393_point_k = (this).dtor_point();
    int _394_end;
    _394_end = (this).dtor_end();
    while ((java.lang.Integer.compareUnsigned(_393_point_k, _394_end) < 0) && (((boolean)(java.lang.Object)((p).apply(((byte)(java.lang.Object)(((this).dtor_s()).select(_393_point_k)))))))) {
      _393_point_k = (int)  ((_393_point_k) + (1));
    }
    ps = Std.JSON.Utils.Cursors.Cursor__.create((this).dtor_s(), (this).dtor_beg(), _393_point_k, (this).dtor_end());
    return ps;
  }
  public <__A, __R> Std.Wrappers.Result<Cursor__, CursorError<__R>> SkipWhileLexer(dafny.TypeDescriptor<__A> _td___A, dafny.TypeDescriptor<__R> _td___R, dafny.Function2<__A, java.lang.Short, Std.JSON.Utils.Lexers.Core.LexerResult<__A, __R>> step, __A st)
  {
    Std.Wrappers.Result<Cursor__, CursorError<__R>> pr = Std.Wrappers.Result.<Cursor__, CursorError<__R>>Default(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Cursor.defaultValue());
    if(true) {
      int _395_point_k;
      _395_point_k = (this).dtor_point();
      int _396_end;
      _396_end = (this).dtor_end();
      @SuppressWarnings({"unchecked", "deprecation"})
      __A _397_st_k;
      _397_st_k = st;
      while (true) {
        boolean _398_eof;
        _398_eof = (_395_point_k) == (_396_end);
        short _399_minusone;
        _399_minusone = (short) -1;
        short _400_c;
        _400_c = ((_398_eof) ? (_399_minusone) : ((short) java.lang.Byte.toUnsignedInt(((byte)(java.lang.Object)(((this).dtor_s()).select(_395_point_k))))));
        Std.JSON.Utils.Lexers.Core.LexerResult<__A, __R> _source15 = ((Std.JSON.Utils.Lexers.Core.LexerResult<__A, __R>)(java.lang.Object)((step).apply(_397_st_k, _400_c)));
        if (_source15.is_Accept()) {
          pr = Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Success(Cursor__._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.Cursor__.create((this).dtor_s(), (this).dtor_beg(), _395_point_k, (this).dtor_end()));
          return pr;
        } else if (_source15.is_Reject()) {
          __R _401___mcc_h0 = ((Std.JSON.Utils.Lexers.Core.LexerResult_Reject<__A, __R>)_source15)._err;
          __R _402_err = _401___mcc_h0;
          pr = Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Failure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_OtherError(_td___R, _402_err));
          return pr;
        } else {
          __A _403___mcc_h1 = ((Std.JSON.Utils.Lexers.Core.LexerResult_Partial<__A, __R>)_source15)._st;
          __A _404_st_k_k = _403___mcc_h1;
          if (_398_eof) {
            pr = Std.Wrappers.Result.<Cursor__, CursorError<__R>>create_Failure(Cursor._typeDescriptor(), CursorError.<__R>_typeDescriptor(_td___R), Std.JSON.Utils.Cursors.CursorError.<__R>create_EOF(_td___R));
            return pr;
          } else {
            _397_st_k = _404_st_k_k;
            _395_point_k = (int)  ((_395_point_k) + (1));
          }
        }
      }
    }
    return pr;
  }
  public boolean BOF_q()
  {
    return ((this).dtor_point()) == ((this).dtor_beg());
  }
  public boolean EOF_q()
  {
    return ((this).dtor_point()) == ((this).dtor_end());
  }
}
