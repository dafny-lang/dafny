// Class Value
// Dafny class Value compiled into Java
package Std.JSON.Grammar;

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

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Value {
  public Value() {
  }

  private static final Value theDefault = Std.JSON.Grammar.Value.create_Null(jnull.defaultValue());
  public static Value Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Value> _TYPE = dafny.TypeDescriptor.<Value>referenceWithInitializer(Value.class, () -> Value.Default());
  public static dafny.TypeDescriptor<Value> _typeDescriptor() {
    return (dafny.TypeDescriptor<Value>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Value create_Null(Std.JSON.Utils.Views.Core.View__ n) {
    return new Value_Null(n);
  }
  public static Value create_Bool(Std.JSON.Utils.Views.Core.View__ b) {
    return new Value_Bool(b);
  }
  public static Value create_String(jstring str) {
    return new Value_String(str);
  }
  public static Value create_Number(jnumber num) {
    return new Value_Number(num);
  }
  public static Value create_Object(Bracketed<Std.JSON.Utils.Views.Core.View__, jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> obj) {
    return new Value_Object(obj);
  }
  public static Value create_Array(Bracketed<Std.JSON.Utils.Views.Core.View__, Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> arr) {
    return new Value_Array(arr);
  }
  public boolean is_Null() { return this instanceof Value_Null; }
  public boolean is_Bool() { return this instanceof Value_Bool; }
  public boolean is_String() { return this instanceof Value_String; }
  public boolean is_Number() { return this instanceof Value_Number; }
  public boolean is_Object() { return this instanceof Value_Object; }
  public boolean is_Array() { return this instanceof Value_Array; }
  public Std.JSON.Utils.Views.Core.View__ dtor_n() {
    Value d = this;
    return ((Value_Null)d)._n;
  }
  public Std.JSON.Utils.Views.Core.View__ dtor_b() {
    Value d = this;
    return ((Value_Bool)d)._b;
  }
  public jstring dtor_str() {
    Value d = this;
    return ((Value_String)d)._str;
  }
  public jnumber dtor_num() {
    Value d = this;
    return ((Value_Number)d)._num;
  }
  public Bracketed<Std.JSON.Utils.Views.Core.View__, jKeyValue, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> dtor_obj() {
    Value d = this;
    return ((Value_Object)d)._obj;
  }
  public Bracketed<Std.JSON.Utils.Views.Core.View__, Value, Std.JSON.Utils.Views.Core.View__, Std.JSON.Utils.Views.Core.View__> dtor_arr() {
    Value d = this;
    return ((Value_Array)d)._arr;
  }
}
