// Class JSON
// Dafny class JSON compiled into Java
package Std.JSON.Values;

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

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class JSON {
  public JSON() {
  }

  private static final JSON theDefault = Std.JSON.Values.JSON.create_Null();
  public static JSON Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<JSON> _TYPE = dafny.TypeDescriptor.<JSON>referenceWithInitializer(JSON.class, () -> JSON.Default());
  public static dafny.TypeDescriptor<JSON> _typeDescriptor() {
    return (dafny.TypeDescriptor<JSON>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static JSON create_Null() {
    return new JSON_Null();
  }
  public static JSON create_Bool(boolean b) {
    return new JSON_Bool(b);
  }
  public static JSON create_String(dafny.DafnySequence<? extends dafny.CodePoint> str) {
    return new JSON_String(str);
  }
  public static JSON create_Number(Decimal num) {
    return new JSON_Number(num);
  }
  public static JSON create_Object(dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, JSON>> obj) {
    return new JSON_Object(obj);
  }
  public static JSON create_Array(dafny.DafnySequence<? extends JSON> arr) {
    return new JSON_Array(arr);
  }
  public boolean is_Null() { return this instanceof JSON_Null; }
  public boolean is_Bool() { return this instanceof JSON_Bool; }
  public boolean is_String() { return this instanceof JSON_String; }
  public boolean is_Number() { return this instanceof JSON_Number; }
  public boolean is_Object() { return this instanceof JSON_Object; }
  public boolean is_Array() { return this instanceof JSON_Array; }
  public boolean dtor_b() {
    JSON d = this;
    return ((JSON_Bool)d)._b;
  }
  public dafny.DafnySequence<? extends dafny.CodePoint> dtor_str() {
    JSON d = this;
    return ((JSON_String)d)._str;
  }
  public Decimal dtor_num() {
    JSON d = this;
    return ((JSON_Number)d)._num;
  }
  public dafny.DafnySequence<? extends dafny.Tuple2<dafny.DafnySequence<? extends dafny.CodePoint>, JSON>> dtor_obj() {
    JSON d = this;
    return ((JSON_Object)d)._obj;
  }
  public dafny.DafnySequence<? extends JSON> dtor_arr() {
    JSON d = this;
    return ((JSON_Array)d)._arr;
  }
}
