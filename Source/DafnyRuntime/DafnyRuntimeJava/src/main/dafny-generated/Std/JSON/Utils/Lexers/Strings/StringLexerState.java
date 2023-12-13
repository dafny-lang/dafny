// Class StringLexerState
// Dafny class StringLexerState compiled into Java
package Std.JSON.Utils.Lexers.Strings;

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
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class StringLexerState {
  public StringLexerState() {
  }

  private static final StringLexerState theDefault = Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Start();
  public static StringLexerState Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<StringLexerState> _TYPE = dafny.TypeDescriptor.<StringLexerState>referenceWithInitializer(StringLexerState.class, () -> StringLexerState.Default());
  public static dafny.TypeDescriptor<StringLexerState> _typeDescriptor() {
    return (dafny.TypeDescriptor<StringLexerState>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static StringLexerState create_Start() {
    return new StringLexerState_Start();
  }
  public static StringLexerState create_Body(boolean escaped) {
    return new StringLexerState_Body(escaped);
  }
  public static StringLexerState create_End() {
    return new StringLexerState_End();
  }
  public boolean is_Start() { return this instanceof StringLexerState_Start; }
  public boolean is_Body() { return this instanceof StringLexerState_Body; }
  public boolean is_End() { return this instanceof StringLexerState_End; }
  public boolean dtor_escaped() {
    StringLexerState d = this;
    return ((StringLexerState_Body)d)._escaped;
  }
}
