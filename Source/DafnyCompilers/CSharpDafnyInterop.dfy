include "../AutoExtern/CSharpModel.dfy"
include "CSharpDafnyModel.dfy"
include "CSharpInterop.dfy"

module {:extern "CSharpDafnyInterop"} CSharpDafnyInterop {
  import Microsoft
  import opened CSharpInterop

  class {:extern} StringUtils {
    static function method {:extern} ToCString(s: string) : System.String
    static function method {:extern} OfCString(s: System.String) : string
  }

  class {:extern} TypeConv {
    static function method {:extern} AsBool(o: System.Boolean) : bool
    static function method {:extern} AsInt(o: System.Numerics.BigInteger) : int
    static function method {:extern} AsReal(o: Microsoft.BaseTypes.BigDec) : real
    static function method {:extern} AsString(o: System.String) : string

    static function method {:extern} Numerator(r: real) : int
    static function method {:extern} Denominator(r: real) : int
  }

  class Reals { // DISCUSS: Not a module to be able to refer to TypeConv
    static function method AsIntegerRatio(r: real) : (int, int) {
      (TypeConv.Numerator(r), TypeConv.Denominator(r))
    }
  }

  class SyntaxTreeAdapter {
    var wr: Microsoft.Dafny.ConcreteSyntaxTree

    constructor(wr: Microsoft.Dafny.ConcreteSyntaxTree) {
      this.wr := wr;
    }

    method Write(value: string) {
      wr.Write(StringUtils.ToCString(value));
    }

    method WriteLine(value: string) {
      wr.WriteLine(StringUtils.ToCString(value));
    }

    method NewBlock(header: string) returns (st': SyntaxTreeAdapter) {
      var wr' := wr.NewBlock(StringUtils.ToCString(header));
      st' := new SyntaxTreeAdapter(wr');
    }
  }
}
