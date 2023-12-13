// Class __default
// Dafny class __default compiled into Java
package Std.FileIOInternalExterns;

import JavaInternal.*;
import Std.Wrappers.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.Tuple3 INTERNAL__ReadBytesFromFile(dafny.DafnySequence<? extends dafny.CodePoint> path)
  {
    boolean isError = false;
    dafny.DafnySequence<? extends java.lang.Byte> bytesRead = dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE);
    dafny.DafnySequence<? extends dafny.CodePoint> errorMsg = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    boolean _28_r1;
    dafny.DafnySequence<? extends java.lang.Byte> _29_r2;
    dafny.DafnySequence<? extends dafny.CodePoint> _30_r3;
    boolean _out0;
    dafny.DafnySequence<? extends java.lang.Byte> _out1;
    dafny.DafnySequence<? extends dafny.CodePoint> _out2;
    dafny.Tuple3<Boolean, dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector0 = Std.FileIOInternalExterns.FileIO.INTERNAL_ReadBytesFromFile(path);
    _out0 = (boolean) (Object) _outcollector0.dtor__0();
    _out1 = (dafny.DafnySequence<? extends java.lang.Byte>) (Object) _outcollector0.dtor__1();
    _out2 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector0.dtor__2();
    _28_r1 = _out0;
    _29_r2 = _out1;
    _30_r3 = _out2;
    boolean _rhs0 = _28_r1;
    dafny.DafnySequence<? extends java.lang.Byte> _rhs1 = _29_r2;
    dafny.DafnySequence<? extends dafny.CodePoint> _rhs2 = _30_r3;
    isError = _rhs0;
    bytesRead = _rhs1;
    errorMsg = _rhs2;
    return new dafny.Tuple3<>(isError, bytesRead, errorMsg);
  }
  public static dafny.Tuple2 INTERNAL__WriteBytesToFile(dafny.DafnySequence<? extends dafny.CodePoint> path, dafny.DafnySequence<? extends java.lang.Byte> bytes)
  {
    boolean isError = false;
    dafny.DafnySequence<? extends dafny.CodePoint> errorMsg = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    boolean _31_r1;
    dafny.DafnySequence<? extends dafny.CodePoint> _32_r2;
    boolean _out3;
    dafny.DafnySequence<? extends dafny.CodePoint> _out4;
    dafny.Tuple2<Boolean, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector1 = Std.FileIOInternalExterns.FileIO.INTERNAL_WriteBytesToFile(path, bytes);
    _out3 = (boolean) (Object) _outcollector1.dtor__0();
    _out4 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector1.dtor__1();
    _31_r1 = _out3;
    _32_r2 = _out4;
    boolean _rhs3 = _31_r1;
    dafny.DafnySequence<? extends dafny.CodePoint> _rhs4 = _32_r2;
    isError = _rhs3;
    errorMsg = _rhs4;
    return new dafny.Tuple2<>(isError, errorMsg);
  }
  @Override
  public java.lang.String toString() {
    return "Std.JavaFileIOInternalExterns._default";
  }
}
