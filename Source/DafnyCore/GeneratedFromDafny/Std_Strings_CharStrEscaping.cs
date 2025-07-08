// Dafny program the_program compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
#pragma warning disable CS0164 // This label has not been referenced
#pragma warning disable CS0162 // Unreachable code detected
#pragma warning disable CS1717 // Assignment made to same variable

namespace Std.Strings.CharStrEscaping {

  public partial class __default {
    public static Dafny.ISequence<Dafny.Rune> Escape(Dafny.ISequence<Dafny.Rune> str, Dafny.ISet<Dafny.Rune> mustEscape, Dafny.Rune escape)
    {
      Dafny.ISequence<Dafny.Rune> _0___accumulator = Dafny.Sequence<Dafny.Rune>.FromElements();
    TAIL_CALL_START: ;
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, str);
      } else if ((mustEscape).Contains((str).Select(BigInteger.Zero))) {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements(escape, (str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in0 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in1 = mustEscape;
        Dafny.Rune _in2 = escape;
        str = _in0;
        mustEscape = _in1;
        escape = _in2;
        goto TAIL_CALL_START;
      } else {
        _0___accumulator = Dafny.Sequence<Dafny.Rune>.Concat(_0___accumulator, Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)));
        Dafny.ISequence<Dafny.Rune> _in3 = (str).Drop(BigInteger.One);
        Dafny.ISet<Dafny.Rune> _in4 = mustEscape;
        Dafny.Rune _in5 = escape;
        str = _in3;
        mustEscape = _in4;
        escape = _in5;
        goto TAIL_CALL_START;
      }
    }
    public static Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> Unescape(Dafny.ISequence<Dafny.Rune> str, Dafny.Rune escape)
    {
      if ((str).Equals(Dafny.Sequence<Dafny.Rune>.FromElements())) {
        return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(str);
      } else if (((str).Select(BigInteger.Zero)) == (escape)) {
        if ((new BigInteger((str).Count)) > (BigInteger.One)) {
          Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _0_valueOrError0 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(new BigInteger(2)), escape);
          if ((_0_valueOrError0).IsFailure()) {
            return (_0_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
          } else {
            Dafny.ISequence<Dafny.Rune> _1_tl = (_0_valueOrError0).Extract();
            return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.One)), _1_tl));
          }
        } else {
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_None();
        }
      } else {
        Std.Wrappers._IOption<Dafny.ISequence<Dafny.Rune>> _2_valueOrError1 = Std.Strings.CharStrEscaping.__default.Unescape((str).Drop(BigInteger.One), escape);
        if ((_2_valueOrError1).IsFailure()) {
          return (_2_valueOrError1).PropagateFailure<Dafny.ISequence<Dafny.Rune>>();
        } else {
          Dafny.ISequence<Dafny.Rune> _3_tl = (_2_valueOrError1).Extract();
          return Std.Wrappers.Option<Dafny.ISequence<Dafny.Rune>>.create_Some(Dafny.Sequence<Dafny.Rune>.Concat(Dafny.Sequence<Dafny.Rune>.FromElements((str).Select(BigInteger.Zero)), _3_tl));
        }
      }
    }
  }
} // end of namespace Std.Strings.CharStrEscaping