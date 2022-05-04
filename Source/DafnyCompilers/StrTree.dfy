include "Library.dfy"

module StrTree {
  import Lib
  import opened Lib.Datatypes

  datatype StrTree =
    | Str(s: string)
    | SepSeq(sep: Option<string>, asts: seq<StrTree>)
    | Unsupported
  {
    function method ToString() : string {
      match this
        case Str(s) => s
        case SepSeq(sep, asts) =>
          var strs := Lib.Seq.Map(s requires s in asts => s.ToString(), asts);
          Lib.Str.Join(sep.UnwrapOr(""), strs)
        case Unsupported => "<*>"
    }
  }

  function method Seq(asts: seq<StrTree>) : StrTree {
    SepSeq(None, asts)
  }

  function method Concat(sep: string, asts: seq<StrTree>) : StrTree {
    SepSeq(Some(sep), asts)
  }

  function method Call(fn: StrTree, args: seq<StrTree>) : StrTree {
    Seq([fn, Str("("), Concat(", ", args), Str(")")])
  }

  function method SingleQuote(s: char): StrTree {
    Seq([Str("'"), Str([s]), Str("'")])
  }

  function method DoubleQuote(s: string): StrTree {
    Seq([Str("\""), Str(s), Str("\"")])
  }

  function method interleave<T>(
    outside: seq<T>, inside: seq<T>, start: int := 0
  ) : seq<T>
    requires |outside| == |inside| + 1
    requires 0 <= start < |outside|
    decreases |outside| - start
  {
    if start >= |inside| then [outside[start]]
    else [outside[start], inside[start]] + interleave(outside, inside, start + 1)
  }

  function countFormat(formatString: string, start: int := 0, count: int := 0) : int
    decreases |formatString| - start
    // Count placeholders in `formatString`, starting at position `start`.
    // `count` is an accumulator; the function is written this way because it yields
    // marginally better SMT solver performance (this function is used in specs).
  {
    if !(0 <= start < |formatString| - 1) then
      count
    else if formatString[start] == '{' && formatString[start + 1] == '}' then
      countFormat(formatString, start + 2, count + 1)
    else
      countFormat(formatString, start + 1, count)
  }

  lemma countFormat_Acc(formatString: string, start: int := 0, count: int := 0)
    decreases |formatString| - start
    ensures countFormat(formatString, start, count)
         == countFormat(formatString, start) + count
  {}

  lemma splitFormat_countFormat(formatString: string, start: int := 0, pos: int := start)
    requires 0 <= start <= pos <= |formatString|
    decreases |formatString| - pos
    ensures |splitFormat(formatString, start, pos)|
         == 1 + countFormat(formatString, pos)
  {
    if pos >= |formatString| - 1 {
    } else if formatString[pos] == '{' && formatString[pos + 1] == '}' {
      countFormat_Acc(formatString, pos + 2, 1);
      splitFormat_countFormat(formatString, pos + 2, pos + 2);
    } else {}
  }

  function method splitFormat(formatString: string, prev: int := 0, pos: int := prev)
    : (parts: seq<StrTree>)
    requires 0 <= prev <= pos <= |formatString|
    ensures |parts| > 0
    decreases |formatString| - pos
  {
    if pos >= |formatString| - 1 then
      [Str(formatString[prev..])]
    else if formatString[pos] == '{' && formatString[pos + 1] == '}' then
      [Str(formatString[prev..pos])] + splitFormat(formatString, pos + 2, pos + 2)
    else
      splitFormat(formatString, prev, pos + 1)
  }

  function method Format(formatString: string, values: seq<StrTree>) : StrTree
    requires countFormat(formatString) == |values|
  {
    splitFormat_countFormat(formatString);
    Seq(interleave(splitFormat(formatString), values))
  }
}
