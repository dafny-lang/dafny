// Class Chain
// Dafny class Chain compiled into Java
package Std.JSON.Utils.Views.Writers;

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

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Chain {
  public Chain() {
  }

  private static final Chain theDefault = Std.JSON.Utils.Views.Writers.Chain.create_Empty();
  public static Chain Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Chain> _TYPE = dafny.TypeDescriptor.<Chain>referenceWithInitializer(Chain.class, () -> Chain.Default());
  public static dafny.TypeDescriptor<Chain> _typeDescriptor() {
    return (dafny.TypeDescriptor<Chain>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Chain create_Empty() {
    return new Chain_Empty();
  }
  public static Chain create_Chain(Chain previous, Std.JSON.Utils.Views.Core.View__ v) {
    return new Chain_Chain(previous, v);
  }
  public boolean is_Empty() { return this instanceof Chain_Empty; }
  public boolean is_Chain() { return this instanceof Chain_Chain; }
  public Chain dtor_previous() {
    Chain d = this;
    return ((Chain_Chain)d)._previous;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_v() {
    Chain d = this;
    return ((Chain_Chain)d)._v;
  }
  public java.math.BigInteger Length() {
    java.math.BigInteger _368___accumulator = java.math.BigInteger.ZERO;
    Chain _this = this;
    TAIL_CALL_START: while (true) {
      if ((_this).is_Empty()) {
        return (java.math.BigInteger.ZERO).add(_368___accumulator);
      } else {
        _368___accumulator = (dafny.Helpers.unsignedToBigInteger(((_this).dtor_v()).Length())).add(_368___accumulator);
        Chain _in64 = (_this).dtor_previous();
        _this = _in64;
        ;
        continue TAIL_CALL_START;
      }
    }
  }
  public java.math.BigInteger Count() {
    java.math.BigInteger _369___accumulator = java.math.BigInteger.ZERO;
    Chain _this = this;
    TAIL_CALL_START: while (true) {
      if ((_this).is_Empty()) {
        return (java.math.BigInteger.ZERO).add(_369___accumulator);
      } else {
        _369___accumulator = (java.math.BigInteger.ONE).add(_369___accumulator);
        Chain _in65 = (_this).dtor_previous();
        _this = _in65;
        ;
        continue TAIL_CALL_START;
      }
    }
  }
  public dafny.DafnySequence<? extends java.lang.Byte> Bytes() {
    dafny.DafnySequence<? extends java.lang.Byte> _370___accumulator = dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor());
    Chain _this = this;
    TAIL_CALL_START: while (true) {
      if ((_this).is_Empty()) {
        return dafny.DafnySequence.<java.lang.Byte>concatenate(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()), _370___accumulator);
      } else {
        _370___accumulator = dafny.DafnySequence.<java.lang.Byte>concatenate(((_this).dtor_v()).Bytes(), _370___accumulator);
        Chain _in66 = (_this).dtor_previous();
        _this = _in66;
        ;
        continue TAIL_CALL_START;
      }
    }
  }
  public Chain Append(Std.JSON.Utils.Views.Core.View__ v_k) {
    if (((this).is_Chain()) && (Std.JSON.Utils.Views.Core.__default.Adjacent((this).dtor_v(), v_k))) {
      return Std.JSON.Utils.Views.Writers.Chain.create_Chain((this).dtor_previous(), Std.JSON.Utils.Views.Core.__default.Merge((this).dtor_v(), v_k));
    } else {
      return Std.JSON.Utils.Views.Writers.Chain.create_Chain(this, v_k);
    }
  }
  public void CopyTo(byte[] dest, int end)
  {
    Chain _this = this;
    TAIL_CALL_START: while (true) {
      if(true) {
        if ((_this).is_Chain()) {
          int _371_end;
          _371_end = (int)  ((end) - (((_this).dtor_v()).Length()));
          ((_this).dtor_v()).CopyTo(dest, _371_end);
          Chain _in67 = (_this).dtor_previous();
          byte[] _in68 = dest;
          int _in69 = _371_end;
          _this = _in67;
          ;
          dest = _in68;
          end = _in69;
          continue TAIL_CALL_START;
        }
      }
      return;
    }
  }
}
