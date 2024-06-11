// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;

namespace Std.Strings.CharStrEscaping {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> Escape(Dafny.ISequence<Dafny.Rune> str, Dafny.ISet<Dafny.Rune> mustEscape, Dafny.Rune escape)
    {
      Dafny.ISequence<Dafny.Rune> _177___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_177___accumulator, str);
      } else if ((mustEscape).Contains((str).Select(BigInteger.Zero))) {
        _177___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_177___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements(escape, (str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in56 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in57 = mustEscape;
        Dafny.Rune _in58 = escape;
        str = _in56;
        mustEscape = _in57;
        escape = _in58;
        goto TAIL_CALL_START;
      } else {
        _177___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_177___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in59 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in60 = mustEscape;
        Dafny.Rune _in61 = escape;
        str = _in59;
        mustEscape = _in60;
        escape = _in61;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> Unescape(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune escape)
    {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(str);
      } else if (((str).Select(BigInteger.Zero)) == (escape)) {
        if ((new BigInteger((str).Count)) > (BigInteger.One)) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _178_valueOrError0 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(new BigInteger(2)), escape);
          if ((_178_valueOrError0).IsFailure()) {
            return (_178_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
          } else {
            Dafny.ISequence<Dafny.Rune> _179_tl = (_178_valueOrError0).Extract();
            return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.One)), _179_tl));
          }
        } else {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
        }
      } else {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _180_valueOrError1 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(BigInteger.One), escape);
        if ((_180_valueOrError1).IsFailure()) {
          return (_180_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
        } else {
          Dafny.ISequence<Dafny.Rune> _181_tl = (_180_valueOrError1).Extract();
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)), _181_tl));
        }
      }
    }
  }
} // end of namespace Std.Strings.CharStrEscaping