// Class __default
// Dafny class __default compiled into Java
package Std.Strings.CharStrEscaping;

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

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static dafny.DafnySequence<? extends dafny.CodePoint> Escape(dafny.DafnySequence<? extends dafny.CodePoint> str, dafny.DafnySet<? extends dafny.CodePoint> mustEscape, int escape)
  {
    dafny.DafnySequence<? extends dafny.CodePoint> _184___accumulator = dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR);
    TAIL_CALL_START: while (true) {
      if ((str).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) {
        return dafny.DafnySequence.<dafny.CodePoint>concatenate(_184___accumulator, str);
      } else if ((mustEscape).<dafny.CodePoint>contains(dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()))) {
        _184___accumulator = dafny.DafnySequence.<dafny.CodePoint>concatenate(_184___accumulator, dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(escape), dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value())));
        dafny.DafnySequence<? extends dafny.CodePoint> _in56 = (str).drop(java.math.BigInteger.ONE);
        dafny.DafnySet<? extends dafny.CodePoint> _in57 = mustEscape;
        int _in58 = escape;
        str = _in56;
        mustEscape = _in57;
        escape = _in58;
        continue TAIL_CALL_START;
      } else {
        _184___accumulator = dafny.DafnySequence.<dafny.CodePoint>concatenate(_184___accumulator, dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value())));
        dafny.DafnySequence<? extends dafny.CodePoint> _in59 = (str).drop(java.math.BigInteger.ONE);
        dafny.DafnySet<? extends dafny.CodePoint> _in60 = mustEscape;
        int _in61 = escape;
        str = _in59;
        mustEscape = _in60;
        escape = _in61;
        continue TAIL_CALL_START;
      }
    }
  }
  public static Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> Unescape(dafny.DafnySequence<? extends dafny.CodePoint> str, int escape)
  {
    if ((str).equals(dafny.DafnySequence.<dafny.CodePoint> empty(dafny.TypeDescriptor.UNICODE_CHAR))) {
      return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), str);
    } else if ((((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value()) == (escape)) {
      if ((java.math.BigInteger.valueOf((str).length())).compareTo(java.math.BigInteger.ONE) > 0) {
        Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> _185_valueOrError0 = __default.Unescape((str).drop(java.math.BigInteger.valueOf(2L)), escape);
        if ((_185_valueOrError0).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR))) {
          return (_185_valueOrError0).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
        } else {
          dafny.DafnySequence<? extends dafny.CodePoint> _186_tl = (_185_valueOrError0).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
          return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ONE))))).value())), _186_tl));
        }
      } else {
        return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_None(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
      }
    } else {
      Std.Wrappers.Option<dafny.DafnySequence<? extends dafny.CodePoint>> _187_valueOrError1 = __default.Unescape((str).drop(java.math.BigInteger.ONE), escape);
      if ((_187_valueOrError1).IsFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR))) {
        return (_187_valueOrError1).<dafny.DafnySequence<? extends dafny.CodePoint>>PropagateFailure(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
      } else {
        dafny.DafnySequence<? extends dafny.CodePoint> _188_tl = (_187_valueOrError1).Extract(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR));
        return Std.Wrappers.Option.<dafny.DafnySequence<? extends dafny.CodePoint>>create_Some(dafny.DafnySequence.<dafny.CodePoint>_typeDescriptor(dafny.TypeDescriptor.UNICODE_CHAR), dafny.DafnySequence.<dafny.CodePoint>concatenate(dafny.DafnySequence.<dafny.CodePoint> of(dafny.TypeDescriptor.UNICODE_CHAR, dafny.CodePoint.valueOf(((dafny.CodePoint)((str).select(dafny.Helpers.toInt((java.math.BigInteger.ZERO))))).value())), _188_tl));
      }
    }
  }
  @Override
  public java.lang.String toString() {
    return "Std.Strings.CharStrEscaping._default";
  }
}
