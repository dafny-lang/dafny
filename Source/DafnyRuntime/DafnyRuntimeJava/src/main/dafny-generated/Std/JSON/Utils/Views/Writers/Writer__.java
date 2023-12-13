// Class Writer__
// Dafny class Writer__ compiled into Java
package Std.JSON.Utils.Views.Writers;

import JavaInternal.*;
import Std.Wrappers.*;
import Std.FileIOInternalExterns.*;
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

@SuppressWarnings({"unchecked", "deprecation"})
public class Writer__ {
  public int _length;
  public Chain _chain;
  public Writer__ (int length, Chain chain) {
    this._length = length;
    this._chain = chain;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    Writer__ o = (Writer__)other;
    return true && this._length == o._length && java.util.Objects.equals(this._chain, o._chain);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.lang.Integer.hashCode(this._length);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._chain);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Writers.Writer_.Writer");
    s.append("(");
    s.append(this._length);
    s.append(", ");
    s.append(dafny.Helpers.toString(this._chain));
    s.append(")");
    return s.toString();
  }

  private static final Writer__ theDefault = Std.JSON.Utils.Views.Writers.Writer__.create(0, Chain.Default());
  public static Writer__ Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Writer__> _TYPE = dafny.TypeDescriptor.<Writer__>referenceWithInitializer(Writer__.class, () -> Writer__.Default());
  public static dafny.TypeDescriptor<Writer__> _typeDescriptor() {
    return (dafny.TypeDescriptor<Writer__>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Writer__ create(int length, Chain chain) {
    return new Writer__(length, chain);
  }
  public static Writer__ create_Writer(int length, Chain chain) {
    return create(length, chain);
  }
  public boolean is_Writer() { return true; }
  public int dtor_length() {
    return this._length;
  }
  public Chain dtor_chain() {
    return this._chain;
  }
  public dafny.DafnySequence<? extends java.lang.Byte> Bytes() {
    return ((this).dtor_chain()).Bytes();
  }
  public static int SaturatedAddU32(int a, int b)
  {
    if (java.lang.Integer.compareUnsigned(a, (int)  ((Std.BoundedInts.__default.UINT32__MAX()) - (b))) <= 0) {
      return (int)  ((a) + (b));
    } else {
      return Std.BoundedInts.__default.UINT32__MAX();
    }
  }
  public Writer__ Append(Std.JSON.Utils.Views.Core.View__ v_k) {
    return Std.JSON.Utils.Views.Writers.Writer__.create(Writer__.SaturatedAddU32((this).dtor_length(), (v_k).Length()), ((this).dtor_chain()).Append(v_k));
  }
  public Writer__ Then(java.util.function.Function<Writer__, Writer__> fn) {
    return ((Writer__)(java.lang.Object)((fn).apply(this)));
  }
  public void CopyTo(byte[] dest)
  {
    ((this).dtor_chain()).CopyTo(dest, (this).dtor_length());
  }
  public byte[] ToArray()
  {
    byte[] bs = new byte[0];
    if(true) {
      java.util.function.Function<java.math.BigInteger, java.lang.Byte> _init4 = ((java.util.function.Function<java.math.BigInteger, java.lang.Byte>)(_377_i_boxed0) -> {
        java.math.BigInteger _377_i = ((java.math.BigInteger)(java.lang.Object)(_377_i_boxed0));
        return (byte) 0;
      });
      byte[] _nw5 = (byte[]) Std.BoundedInts.uint8._typeDescriptor().newArray(dafny.Helpers.toIntChecked(((this).dtor_length()), "Java arrays may be no larger than the maximum 32-bit signed int"));
      for (java.math.BigInteger _i0_4 = java.math.BigInteger.ZERO; _i0_4.compareTo(java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength(_nw5))) < 0; _i0_4 = _i0_4.add(java.math.BigInteger.ONE)) {
        _nw5[dafny.Helpers.toInt(_i0_4)] = ((byte)(java.lang.Object)(_init4.apply(_i0_4)));
      }
      bs = _nw5;
      (this).CopyTo(bs);
    }
    return bs;
  }
  public static Writer__ Empty()
  {
    return Std.JSON.Utils.Views.Writers.Writer__.create(0, Std.JSON.Utils.Views.Writers.Chain.create_Empty());
  }
  public boolean Unsaturated_q()
  {
    return ((this).dtor_length()) != (Std.BoundedInts.__default.UINT32__MAX());
  }
  public boolean Empty_q()
  {
    return ((this).dtor_chain()).is_Empty();
  }
}
