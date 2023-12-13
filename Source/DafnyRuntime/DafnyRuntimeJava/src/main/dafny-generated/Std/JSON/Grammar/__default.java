// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Grammar;

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
import Std.JSON.Utils.Lexers.Strings.*;
import Std.JSON.Utils.Cursors.*;
import Std.JSON.Utils.Parsers.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean Blank_q(byte b) {
    return ((((b) == ((byte) 32)) || ((b) == ((byte) 9))) || ((b) == ((byte) 10))) || ((b) == ((byte) 13));
  }
  public static boolean Digit_q(byte b) {
    return (java.lang.Integer.compareUnsigned(((byte) ('0')), b) <= 0) && (java.lang.Integer.compareUnsigned(b, ((byte) ('9'))) <= 0);
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> NULL()
  {
    return dafny.DafnySequence.<java.lang.Byte> of(((byte) ('n')), ((byte) ('u')), ((byte) ('l')), ((byte) ('l')));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> TRUE()
  {
    return dafny.DafnySequence.<java.lang.Byte> of(((byte) ('t')), ((byte) ('r')), ((byte) ('u')), ((byte) ('e')));
  }
  public static dafny.DafnySequence<? extends java.lang.Byte> FALSE()
  {
    return dafny.DafnySequence.<java.lang.Byte> of(((byte) ('f')), ((byte) ('a')), ((byte) ('l')), ((byte) ('s')), ((byte) ('e')));
  }
  public static Std.JSON.Utils.Views.Core.View__ DOUBLEQUOTE()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('\"'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ PERIOD()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('.'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ E()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('e'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ COLON()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) (':'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ COMMA()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) (','))));
  }
  public static Std.JSON.Utils.Views.Core.View__ LBRACE()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('{'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ RBRACE()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('}'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ LBRACKET()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('['))));
  }
  public static Std.JSON.Utils.Views.Core.View__ RBRACKET()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) (']'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ MINUS()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> of(((byte) ('-'))));
  }
  public static Std.JSON.Utils.Views.Core.View__ EMPTY()
  {
    return Std.JSON.Utils.Views.Core.View__.OfBytes(dafny.DafnySequence.<java.lang.Byte> empty(Std.BoundedInts.uint8._typeDescriptor()));
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Grammar._default";
  }
}
