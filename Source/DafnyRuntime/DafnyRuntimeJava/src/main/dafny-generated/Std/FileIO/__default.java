// Class __default
// Dafny class __default compiled into Java
package Std.FileIO;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> ReadBytesFromFile(dafny.DafnySequence<? extends dafny.CodePoint> path)
  {
    Std.Wrappers.Result<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> res = Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>Default(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<java.lang.Byte> empty(dafny.TypeDescriptor.BYTE));
    boolean _141_isError;
    dafny.DafnySequence<? extends java.lang.Byte> _142_bytesRead;
    dafny.DafnySequence<? extends dafny.CodePoint> _143_errorMsg;
    boolean _out6;
    dafny.DafnySequence<? extends java.lang.Byte> _out7;
    dafny.DafnySequence<? extends dafny.CodePoint> _out8;
    dafny.Tuple3<Boolean, dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector2 = Std.FileIOInternalExterns.__default.INTERNAL__ReadBytesFromFile(path);
    _out6 = (boolean) (Object) _outcollector2.dtor__0();
    _out7 = (dafny.DafnySequence<? extends java.lang.Byte>) (Object) _outcollector2.dtor__1();
    _out8 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector2.dtor__2();
    _141_isError = _out6;
    _142_bytesRead = _out7;
    _143_errorMsg = _out8;
    res = ((_141_isError) ? (Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _143_errorMsg)) : (Std.Wrappers.Result.<dafny.DafnySequence<? extends java.lang.Byte>, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.DafnySequence.<java.lang.Byte>_typeDescriptor(dafny.TypeDescriptor.BYTE), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _142_bytesRead)));
    return res;
  }
  public static Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> WriteBytesToFile(dafny.DafnySequence<? extends dafny.CodePoint> path, dafny.DafnySequence<? extends java.lang.Byte> bytes)
  {
    Std.Wrappers.Result<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>> res = Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>Default(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.Tuple0.Default());
    boolean _144_isError;
    dafny.DafnySequence<? extends dafny.CodePoint> _145_errorMsg;
    boolean _out9;
    dafny.DafnySequence<? extends dafny.CodePoint> _out10;
    dafny.Tuple2<Boolean, dafny.DafnySequence<? extends dafny.CodePoint>> _outcollector3 = Std.FileIOInternalExterns.__default.INTERNAL__WriteBytesToFile(path, bytes);
    _out9 = (boolean) (Object) _outcollector3.dtor__0();
    _out10 = (dafny.DafnySequence<? extends dafny.CodePoint>) (Object) _outcollector3.dtor__1();
    _144_isError = _out9;
    _145_errorMsg = _out10;
    res = ((_144_isError) ? (Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>create_Failure(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), _145_errorMsg)) : (Std.Wrappers.Result.<dafny.Tuple0, dafny.DafnySequence<? extends dafny.CodePoint>>create_Success(dafny.Tuple0._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.Tuple0.create())));
    return res;
  }
  @Override
  public java.lang.String toString() {
    return "Std.FileIO._default";
  }
}
