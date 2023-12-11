// Class LexerResult<T, R>
// Dafny class LexerResult<T, R> compiled into Java
package Std.JSON.Utils.Lexers.Core;

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

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class LexerResult<T, R> {
  protected dafny.TypeDescriptor<T> _td_T;
  protected dafny.TypeDescriptor<R> _td_R;
  public LexerResult(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    this._td_T = _td_T;
    this._td_R = _td_R;
  }

  public static <T, R> LexerResult<T, R> Default(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return Std.JSON.Utils.Lexers.Core.LexerResult.<T, R>create_Accept(_td_T, _td_R);
  }
  public static <T, R> dafny.TypeDescriptor<LexerResult<T, R>> _typeDescriptor(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return (dafny.TypeDescriptor<LexerResult<T, R>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<LexerResult<T, R>>referenceWithInitializer(LexerResult.class, () -> LexerResult.<T, R>Default(_td_T, _td_R));
  }
  public static <T, R> LexerResult<T, R> create_Accept(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R) {
    return new LexerResult_Accept<T, R>(_td_T, _td_R);
  }
  public static <T, R> LexerResult<T, R> create_Reject(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, R err) {
    return new LexerResult_Reject<T, R>(_td_T, _td_R, err);
  }
  public static <T, R> LexerResult<T, R> create_Partial(dafny.TypeDescriptor<T> _td_T, dafny.TypeDescriptor<R> _td_R, T st) {
    return new LexerResult_Partial<T, R>(_td_T, _td_R, st);
  }
  public boolean is_Accept() { return this instanceof LexerResult_Accept; }
  public boolean is_Reject() { return this instanceof LexerResult_Reject; }
  public boolean is_Partial() { return this instanceof LexerResult_Partial; }
  public R dtor_err() {
    LexerResult<T, R> d = this;
    return ((LexerResult_Reject<T, R>)d)._err;
  }
  public T dtor_st() {
    LexerResult<T, R> d = this;
    return ((LexerResult_Partial<T, R>)d)._st;
  }
}
