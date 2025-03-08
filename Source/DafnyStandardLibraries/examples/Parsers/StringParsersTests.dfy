module StringParsersTests refines Std.Parsers.StringParsers {
  datatype ParserResultArray =
      ASuccess(result: string, pos: nat)
    | AFailure(pos: nat)

  method ParseString(expected: string, input: array<char>, i: nat)
    returns (result: ParserResultArray)
    requires i <= input.Length
    ensures result.ASuccess? <==> String(expected)(input[..][i..]).Success?
    ensures if result.ASuccess? then
              result.result == String(expected)(input[..][i..]).result
            else
              result.pos == i + |input[..]|-|String(expected)(input[..][i..]).Remaining()|
  {
    reveal String();
    if i + |expected| <= input.Length && input[i..i+|expected|] == expected {
      result := ASuccess(expected, i+|expected|);
    } else {
      result := AFailure(i);
      assert String(expected)(input[..][i..]).Remaining() == input[..];
    }
  }
  method OptimizedSplit(input: string) returns (result: seq<string>)
    ensures Success(result, "") ==
            ConcatL(RepSep(ZeroOrMore(CharTest((c: char) => c != ',', "noncomma")), String(",")),
                    EndOfString())(input)
  {
  }
}
