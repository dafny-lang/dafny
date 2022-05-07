include "Values.dfy"
include "Library.dfy"
include "CSharpDafnyInterop.dfy"

module Interp.Printer {
  import Values
  import opened Lib
  import Interop = CSharpDafnyInterop

  function method ToString(v: Values.T) : string {
    match v
      case Bool(b) => Str.of_bool(b)
      case Char(c) => "'" + Str.of_char(c) + "'"
      case Int(i) => Str.of_int(i)
      case Real(r) => var (n, d) := Interop.TypeConv.AsIntegerRatio(r); Str.of_int(n) + "/" + Str.of_int(d)
      case BigOrdinal(o) => "<*>" // FIXME
      case BitVector(width, value) => "bv" + Str.of_int(width, 10) + "(0x" + Str.of_int(value, 16) + ")"
      case Map(m) => "map[" + "<*>" + "]" // FIXME iterate over map
      case Multiset(ms) => "multiset{" + "<*>" + "}]" // FIXME iterate over multiset (convert to map?)
      case Seq(sq) => "[" + Lib.Str.Join(", ", Lib.Seq.Map(v requires v in sq => ToString(v), sq)) + "]"
      case Set(st) => "set{" + "<*>" + "}" // FIXME iterate over set
      case Closure(ctx, vars, body) => "(" + Lib.Str.Join(", ", vars) + ") => <*>" // FIXME print context
  }
}
