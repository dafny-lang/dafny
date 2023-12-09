// Class View__
// Dafny class View__ compiled into Java
package Std.JSON.Utils.Views.Core;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class View__ {
  public dafny.DafnySequence<? extends java.lang.Byte> _s;
  public int _beg;
  public int _end;
  public View__ (dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int end) {
    this._s = s;
    this._beg = beg;
    this._end = end;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    View__ o = (View__)other;
    return true && java.util.Objects.equals(this._s, o._s) && this._beg == o._beg && this._end == o._end;
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._s);
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._beg);
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._end);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder ss = new StringBuilder();
    ss.append("Core.View_.View");
    ss.append("(");
    ss.append(dafny.Helpers.toString(this._s));
    ss.append(", ");
    ss.append(this._beg);
    ss.append(", ");
    ss.append(this._end);
    ss.append(")");
    return ss.toString();
  }

  private static final View__ theDefault = Std.JSON.Utils.Views.Core.View__.create(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), 0, 0);
  public static View__ Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<View__> _TYPE = dafny.TypeDescriptor.<View__>referenceWithInitializer(View__.class, () -> View__.Default());
  public static dafny.TypeDescriptor<View__> _typeDescriptor() {
    return (dafny.TypeDescriptor<View__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static View__ create(dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int end) {
    return new View__(s, beg, end);
  }
  public static View__ create_View(dafny.DafnySequence<? extends java.lang.Byte> s, int beg, int end) {
    return create(s, beg, end);
  }
  public boolean is_View() { return true; }
  public dafny.DafnySequence<? extends java.lang.Byte> dtor_s() {
    return this._s;
  }
  public int dtor_beg() {
    return this._beg;
  }
  public int dtor_end() {
    return this._end;
  }
  public int Length() {
    return (int)  (((this).dtor_end()) - ((this).dtor_beg()));
  }
  public dafny.DafnySequence<? extends java.lang.Byte> Bytes() {
    return ((this).dtor_s()).subsequence((this).dtor_beg(), (this).dtor_end());
  }
  public static View__ OfBytes(dafny.DafnySequence<? extends java.lang.Byte> bs) {
    return Std.JSON.Utils.Views.Core.View__.create(bs, 0, (bs).cardinalityInt());
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> OfString(dafny.DafnySequence<? extends dafny.CodePoint> s) {
    return dafny.DafnySequence.Create(Std.BoundedInts.uint8._typeDescriptor(), java.math.BigInteger.valueOf((s).length()), ((java.util.function.Function<dafny.DafnySequence<? extends dafny.CodePoint>, java.util.function.Function<java.math.BigInteger, java.lang.Byte>>)(_359_s) -> ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_360_i_boxed0) -> {
      java.math.BigInteger _360_i = ((java.math.BigInteger)(java.lang.Object)(_360_i_boxed0));
      return ((byte) (((dafny.CodePoint)((_359_s).select(dafny.Helpers.toInt((_360_i))))).value()));
    })).apply(s));
  }
  public boolean Byte_q(byte c)
  {
    boolean _hresult = false;
    _hresult = (((this).Length()) == (1)) && (((this).At(0)) == (c));
    return _hresult;
  }
  public boolean Char_q(int c) {
    return (this).Byte_q(((byte) (c)));
  }
  public byte At(int idx) {
    return ((byte)(java.lang.Object)(((this).dtor_s()).select((int)  (((this).dtor_beg()) + (idx)))));
  }
  public short Peek() {
    if ((this).Empty_q()) {
      return (short) -1;
    } else {
      return (short) java.lang.Byte.toUnsignedInt((this).At(0));
    }
  }
  public void CopyTo(byte[] dest, int start)
  {
    int _hi0 = (this).Length();
    for (int _361_idx = 0; java.lang.Integer.compareUnsigned(_361_idx, _hi0) < 0; _361_idx++) {
      int _index6 = (int)  ((start) + (_361_idx));
      (dest)[dafny.Helpers.toInt(_index6)] = ((byte)(java.lang.Object)(((this).dtor_s()).select((int)  (((this).dtor_beg()) + (_361_idx)))));
    }
  }
  public static View__ Empty()
  {
    return Std.JSON.Utils.Views.Core.View__.create(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), 0, 0);
  }
  public boolean Empty_q()
  {
    return ((this).dtor_beg()) == ((this).dtor_end());
  }
}
