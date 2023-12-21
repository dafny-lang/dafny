// Class __default
// Dafny class __default compiled into Java
package Std.FileIO;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> ReadBytesFromFile(dafny.DafnySequence<? extends dafny.CodePoint> path)
  {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> res = Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>Default(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE));
    boolean _136_isError;
    dafny.DafnySequence<? extends java.lang.Byte> _137_bytesRead;
    dafny.DafnySequence<? extends dafny.CodePoint> _138_errorMsg;
    boolean _out1;
    dafny.DafnySequence<? extends java.lang.Byte> _out2;
    dafny.DafnySequence<? extends dafny.CodePoint> _out3;
    dafny.Tuple3<Boolean, dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector0 = Std.FileIOInternalExterns.__default.INTERNAL__ReadBytesFromFile(path);
    _out1 = (boolean) (Object) _outcollector0.dtor__0();
    _out2 = (dafny.DafnySequence<? extends java.lang.Byte>) (Object) _outcollector0.dtor__1();
    _out3 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector0.dtor__2();
    _136_isError = _out1;
    _137_bytesRead = _out2;
    _138_errorMsg = _out3;
    res = ((_136_isError) ? (Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _138_errorMsg)) : (Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _137_bytesRead)));
    return res;
  }
  public static Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> WriteBytesToFile(dafny.DafnySequence<? extends dafny.CodePoint> path, dafny.DafnySequence<? extends java.lang.Byte> bytes)
  {
    Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> res = Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>Default(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.Tuple0.Default());
    boolean _139_isError;
    dafny.DafnySequence<? extends dafny.CodePoint> _140_errorMsg;
    boolean _out4;
    dafny.DafnySequence<? extends dafny.CodePoint> _out5;
    dafny.Tuple2<Boolean, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector1 = Std.FileIOInternalExterns.__default.INTERNAL__WriteBytesToFile(path, bytes);
    _out4 = (boolean) (Object) _outcollector1.dtor__0();
    _out5 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector1.dtor__1();
    _139_isError = _out4;
    _140_errorMsg = _out5;
    res = ((_139_isError) ? (Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _140_errorMsg)) : (Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.Tuple0.create())));
    return res;
  }
  @Override
  public java.lang.String toString() {
    return "Std.FileIO._default";
  }
}
