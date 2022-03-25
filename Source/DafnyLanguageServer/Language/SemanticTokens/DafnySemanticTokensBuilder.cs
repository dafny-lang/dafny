using System;
using Microsoft.Boogie;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Language.SemanticTokens;

public class DafnySemanticTokensBuilder {
  private readonly SemanticTokensBuilder builder;

  public DafnySemanticTokensBuilder(SemanticTokensBuilder builder) {
    this.builder = builder;
  }

  public void Push(string source, IToken? tok, SemanticTokenType tokenType, params SemanticTokenModifier[] modifiers) {
    if (tok == null || tok == Token.NoToken) {
      Console.Error.WriteLine($"{source}: null");
      return;
    }
    var pos = tok.GetLspPosition();
    Console.Error.WriteLine($"{source}: ({pos.Line}, {pos.Character}) {tok.kind} = '{tok.val}'");
    builder.Push(pos.Line, pos.Character, tok.val.Length, tokenType, modifiers);
  }

  public void Push(string source, IToken? tok, IToken? endTok, SemanticTokenType tokenType, params SemanticTokenModifier[] modifiers) {
    if (tok == null || tok == Token.NoToken) {
      Console.Error.WriteLine($"{source}: null");
      return;
    }
    if (endTok == null || endTok == Token.NoToken) {
      Push(source, tok, tokenType, modifiers);
      return;
    }
    var range = new Range(tok.GetLspPosition(), endTok.GetLspPosition());
    Console.Error.WriteLine($"{source}: ({range.Start.Line}, {range.Start.Character})-({range.End.Line}, {range.End.Character}) {tok.kind} = '{tok.val}'");
    builder.Push(range, tokenType, modifiers);
  }

  public void Push(string source, IToken? tok) {
    if (tok == null || tok == Token.NoToken) {
      Console.Error.WriteLine($"{source}: null");
      return;
    }

    var noModifiers = Array.Empty<SemanticTokenModifier>();
    (SemanticTokenType? tokenType, SemanticTokenModifier[] modifiers) =
#pragma warning disable CS8524
      // [CS8524] The switch expression does not handle some values of its input type (it is not exhaustive) involving
      // an unnamed enum value. For example, the pattern '(Microsoft.Dafny.Parser.TokenClass)16' is not covered.
      Parser.TokenClassificationMap[tok.kind] switch {
        Parser.TokenClass.Other => ((SemanticTokenType?)null, noModifiers),
        Parser.TokenClass.Ident => ((SemanticTokenType?)null, noModifiers),
        Parser.TokenClass.Digits => (SemanticTokenType.Number, noModifiers),
        Parser.TokenClass.Constant => (SemanticTokenType.Number, new [] { SemanticTokenModifier.DefaultLibrary }),
        Parser.TokenClass.Special => (SemanticTokenType.Macro, noModifiers),
        Parser.TokenClass.Comprehension => (SemanticTokenType.Type, new [] { SemanticTokenModifier.DefaultLibrary }),
        Parser.TokenClass.Type => (SemanticTokenType.Type, noModifiers),
        Parser.TokenClass.Macro => (SemanticTokenType.Macro, new [] { SemanticTokenModifier.DefaultLibrary }),
        Parser.TokenClass.Builtin => (SemanticTokenType.Function, new [] { SemanticTokenModifier.DefaultLibrary }),
        Parser.TokenClass.String => (SemanticTokenType.String, noModifiers),
        Parser.TokenClass.Punctuation => ((SemanticTokenType?)null, noModifiers),
        Parser.TokenClass.Assertion => (SemanticTokenType.Keyword, new [] { SemanticTokenModifier.DefaultLibrary, SemanticTokenModifier.Documentation }),
        Parser.TokenClass.Block => (SemanticTokenType.Keyword, noModifiers),
        Parser.TokenClass.ControlFlow => (SemanticTokenType.Keyword, noModifiers),
        Parser.TokenClass.Keyword => (SemanticTokenType.Keyword, noModifiers),
        Parser.TokenClass.Declaration => (SemanticTokenType.Keyword, new[] { SemanticTokenModifier.Declaration }),
        Parser.TokenClass.Modifier => (SemanticTokenType.Modifier, noModifiers),
        Parser.TokenClass.Directive => (SemanticTokenType.Keyword, new[] { SemanticTokenModifier.Declaration }),
        Parser.TokenClass.Specification => (SemanticTokenType.Keyword, new [] { SemanticTokenModifier.DefaultLibrary, SemanticTokenModifier.Documentation }),
        Parser.TokenClass.Label => (SemanticTokenType.Keyword, noModifiers),
        Parser.TokenClass.Operator => (SemanticTokenType.Operator, noModifiers),
        Parser.TokenClass.Comment => (SemanticTokenType.Comment, noModifiers),
      };
#pragma warning restore CS8524

    if (tokenType.HasValue) {
      Push(source, tok, tokenType.Value, modifiers);
    }
  }
}
