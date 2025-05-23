/**
 This example demonstrates how to use Rec to create an SMT parser,
 and RecNoStack to create an SMT parser that does not consume any stack.
*/
module ExampleParsers.SmtParser {
  import Std.Collections.Seq
  import opened Std.Parsers.StringBuilders

  function SeqToString<T>(s: seq<T>, f: T --> string, separator: string := ""): string
    requires forall t <- s :: f.requires(t)
  {
    Seq.Join(Seq.MapPartialFunction(f, s), separator)
  }

  datatype TopLevelSmt = TopLevelSmt(s: seq<SmtNode>)
  {
    function ToString(): string {
      SeqToString(s, (c: SmtNode) => c.ToString(""), "\n")
    }
  }

  datatype SmtNode =
    | Identifier(name: string)
    | Parentheses(s: seq<SmtNode>) {

    function ToString(indent: string := ""): string {
      match this {
        case Identifier(name) => if name == "" then "()" else name
        case Parentheses(s) =>
          if |s| > 0 then
            var name := s[0].ToString(indent);
            "(" + name +
            SeqToString(s[1..], (argument: SmtNode) requires argument < this =>
                          "\n  " + indent + argument.ToString(indent + "  ")
            ) + ")"
          else
            "()"
      }
    }
  }

  const charNotParenNotSpace :=
    //Debug("charNotParenNoSpace",
    CharTest((c: char) => c !in "\r\n \t)", "non-space and not a ')'")
  const noParensNoSpace :=
    //Debug("noParensNoSpace",
    charNotParenNotSpace.I_I(charNotParenNotSpace.Rep()).M((r: (char, string)) => [r.0] + r.1)

  const notNewline :=
    CharTest((c: char) => c !in "\n", "anything except newline")

  function Add(s: string, t: string): string { s + t }

  const WSOrComment: B<string> :=
    WS.I_I(
      S(";").I_I(notNewline.Rep()).M2(MId, Add)
      .I_I(O([S("\n"), EOS.M(x => "")])).M2(MId, Add)
      .I_I(WS).M2(MId, Add).Rep()
    ).M((wsMore: (string, seq<string>)) => wsMore.0 + SeqToString(wsMore.1, MId))

  /** Assumes that we started parsing parentheses and we already parsed 'acc'  */
  function RecContinueAcc(input: Input, acc: seq<SmtNode>): B<RecNoStackResult<SmtNode>>
    decreases InputLength(input)
  {
    O([
        S(")").I_e(WSOrComment).M(_ => RecReturn(Parentheses(acc))),
        SucceedWith(
          RecContinue(
            (r: SmtNode, input2: Input) =>
              (if InputLength(input) <= InputLength(input2) then
                 ResultWith(RecursiveProgressError<RecNoStackResult<SmtNode>>("RecContinueAcc", input, input2))
               else
                 RecContinueAcc(input2, acc + [r]))
          ))])
  }

  // Parses
  //   (name ...sequence of SmtNode space-separated)
  // | name
  // But does not consume stack like parserSmtNode does
  const parserSmtNode2: B<SmtNode> :=
    RecNoStack(
      O([
          S("(").I_e(WSOrComment).ThenWithRemaining(
            (openingParen: string, remaining: Input) =>
              RecContinueAcc(remaining, [])),
          noParensNoSpace.I_e(WSOrComment).M((r: string) => RecReturn(Identifier(r)))
        ]))

  // Parses
  //   (name ...sequence of SmtNode space-separated)
  // | name
  const parserSmtNode: B<SmtNode>
    :=
    Rec((SmtNode: B<SmtNode>) =>
          O([
              // Either
              // (
              S("(").e_I(WSOrComment).Then(
                (r: string) =>
                  SmtNode.I_e(WSOrComment)
                  .Rep().I_e(S(")")).I_e(WSOrComment)
              ).M((r: seq<SmtNode>) => Parentheses(r)).I_e(WSOrComment),
              // Or
              // Anything that is not followed by ) or a space
              noParensNoSpace.M((r: string) => Identifier(r)).I_e(WSOrComment)
            ]))

  const p: B<TopLevelSmt>
    :=
    parserSmtNode.Rep().I_e(WSOrComment).End().M(statements => TopLevelSmt(statements))

  const p2: B<TopLevelSmt>
    :=
    parserSmtNode2.Rep().I_e(WSOrComment).End().M(statements => TopLevelSmt(statements))

  method TestInput(parser: B<TopLevelSmt>, input: string, expectParse: string) {
    var result := parser.Apply(input);
    match result {
      case ParseSuccess(value, remaining) =>
        expect value.ToString() == expectParse;
      case ParseFailure(error, sub_data) =>
        print FailureToString(input, result);
        expect result.ParseSuccess?;
    }
  }

  @Test
  method TestSmtParser() {
    TestInput(p, "(a b)", "(a\n  b)");
    TestInput(p, "((a c d) (b (d)))", "((a\n  c\n  d)\n  (b\n    (d)))");
    TestInput(p2, "(a b)", "(a\n  b)");
    TestInput(p2, "((a c d) (b (d)))", "((a\n  c\n  d)\n  (b\n    (d)))");
  }
}