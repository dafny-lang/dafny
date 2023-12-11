// Class SuffixedSequence
// Dafny class SuffixedSequence compiled into Java
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
public class SuffixedSequence<D, S> {
  protected dafny.TypeDescriptor<D> _td_D;
  protected dafny.TypeDescriptor<S> _td_S;
  public SuffixedSequence(dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S) {
    this._td_D = _td_D;
    this._td_S = _td_S;
  }
  public static <D, S> dafny.TypeDescriptor<dafny.DafnySequence<? extends Suffixed<D, S>>> _typeDescriptor(dafny.TypeDescriptor<D> _td_D, dafny.TypeDescriptor<S> _td_S) {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends Suffixed<D, S>>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<dafny.DafnySequence<? extends Suffixed<D, S>>>referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<Suffixed<D, S>> empty(Suffixed.<D, S>_typeDescriptor(_td_D, _td_S)));
  }
}
