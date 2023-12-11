// Class __default
// Dafny class __default compiled into Java
package Std.JavaFileIOInternalExterns;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.Tuple3 INTERNAL__ReadBytesFromFile(dafny.DafnySequence<? extends dafny.CodePoint> path)
  {
    boolean isError = false;
    dafny.DafnySequence<? extends java.lang.Byte> bytesRead = dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
    dafny.DafnySequence<? extends dafny.CodePoint> errorMsg = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    boolean _299_r1;
    dafny.DafnySequence<? extends java.lang.Byte> _300_r2;
    dafny.DafnySequence<? extends dafny.CodePoint> _301_r3;
    boolean _out6;
    dafny.DafnySequence<? extends java.lang.Byte> _out7;
    dafny.DafnySequence<? extends dafny.CodePoint> _out8;
    dafny.Tuple3<Boolean, dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector2 = Std.DafnyStdLibsExterns.FileIO.INTERNAL_ReadBytesFromFile(path);
    _out6 = (boolean) (Object) _outcollector2.dtor__0();
    _out7 = (dafny.DafnySequence<? extends java.lang.Byte>) (Object) _outcollector2.dtor__1();
    _out8 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector2.dtor__2();
    _299_r1 = _out6;
    _300_r2 = _out7;
    _301_r3 = _out8;
    boolean _rhs6 = _299_r1;
    dafny.DafnySequence<? extends java.lang.Byte> _rhs7 = _300_r2;
    dafny.DafnySequence<? extends dafny.CodePoint> _rhs8 = _301_r3;
    isError = _rhs6;
    bytesRead = _rhs7;
    errorMsg = _rhs8;
    return new dafny.Tuple3<>(isError, bytesRead, errorMsg);
  }
  public static dafny.Tuple2 INTERNAL__WriteBytesToFile(dafny.DafnySequence<? extends dafny.CodePoint> path, dafny.DafnySequence<? extends java.lang.Byte> bytes)
  {
    boolean isError = false;
    dafny.DafnySequence<? extends dafny.CodePoint> errorMsg = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    boolean _302_r1;
    dafny.DafnySequence<? extends dafny.CodePoint> _303_r2;
    boolean _out9;
    dafny.DafnySequence<? extends dafny.CodePoint> _out10;
    dafny.Tuple2<Boolean, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector3 = Std.DafnyStdLibsExterns.FileIO.INTERNAL_WriteBytesToFile(path, bytes);
    _out9 = (boolean) (Object) _outcollector3.dtor__0();
    _out10 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector3.dtor__1();
    _302_r1 = _out9;
    _303_r2 = _out10;
    boolean _rhs9 = _302_r1;
    dafny.DafnySequence<? extends dafny.CodePoint> _rhs10 = _303_r2;
    isError = _rhs9;
    errorMsg = _rhs10;
    return new dafny.Tuple2<>(isError, errorMsg);
  }
  @Override
  public java.lang.String toString() {
    return "Std.JavaFileIOInternalExterns._default";
  }
}
