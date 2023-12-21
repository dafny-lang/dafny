// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Utils.Lexers.Strings;

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
import Std.JSON.Utils.Views.Writers.*;
import Std.JSON.Utils.Lexers.Core.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static <__R> Std.JSON.Utils.Lexers.Core.LexerResult<Boolean, __R> StringBody(dafny.TypeDescriptor<__R> _td___R, boolean escaped, short byte_)
  {
    if ((byte_) == (((short) ('\\')))) {
      return Std.JSON.Utils.Lexers.Core.LexerResult.<Boolean, __R>create_Partial(dafny.TypeDescriptor.BOOLEAN, _td___R, !(escaped));
    } else if (((byte_) == (((short) ('\"')))) && (!(escaped))) {
      return Std.JSON.Utils.Lexers.Core.LexerResult.<Boolean, __R>create_Accept(dafny.TypeDescriptor.BOOLEAN, _td___R);
    } else {
      return Std.JSON.Utils.Lexers.Core.LexerResult.<Boolean, __R>create_Partial(dafny.TypeDescriptor.BOOLEAN, _td___R, false);
    }
  }
  public static Std.JSON.Utils.Lexers.Core.LexerResult<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>> String(StringLexerState st, short byte_)
  {
    StringLexerState _source13 = st;
    if (_source13.is_Start()) {
      if ((byte_) == (((short) ('\"')))) {
        return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Partial(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(false));
      } else {
        return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Reject(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.asUnicodeString("String must start with double quote"));
      }
    } else if (_source13.is_Body()) {
      boolean _373___mcc_h0 = ((Std.JSON.Utils.Lexers.Strings.StringLexerState_Body)_source13)._escaped;
      boolean _374_escaped = _373___mcc_h0;
      if ((byte_) == (((short) ('\\')))) {
        return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Partial(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(!(_374_escaped)));
      } else if (((byte_) == (((short) ('\"')))) && (!(_374_escaped))) {
        return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Partial(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Utils.Lexers.Strings.StringLexerState.create_End());
      } else {
        return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Partial(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Body(false));
      }
    } else {
      return Std.JSON.Utils.Lexers.Core.LexerResult.<StringLexerState, dafny.DafnySequence<? extends dafny.CodePoint>>create_Accept(StringLexerState._typeDescriptor(), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
    }
  }
  public static boolean StringBodyLexerStart()
  {
    return false;
  }
  public static StringLexerState StringLexerStart()
  {
    return Std.JSON.Utils.Lexers.Strings.StringLexerState.create_Start();
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Utils.Lexers.Strings._default";
  }
}
