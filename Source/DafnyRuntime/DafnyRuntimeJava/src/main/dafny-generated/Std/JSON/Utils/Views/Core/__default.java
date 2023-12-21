// Class __default
// Dafny class __default compiled into Java
package Std.JSON.Utils.Views.Core;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static boolean Adjacent(View__ lv, View__ rv)
  {
    return (((lv).dtor_end()) == ((rv).dtor_beg())) && (((lv).dtor_s()).equals((rv).dtor_s()));
  }
  public static View__ Merge(View__ lv, View__ rv)
  {
    View__ _363_dt__update__tmp_h0 = lv;
    int _364_dt__update_hend_h0 = (rv).dtor_end();
    return Std.JSON.Utils.Views.Core.View__.create((_363_dt__update__tmp_h0).dtor_s(), (_363_dt__update__tmp_h0).dtor_beg(), _364_dt__update_hend_h0);
  }
  @Override
  public java.lang.String toString() {
    return "Std.JSON.Utils.Views.Core._default";
  }
}
