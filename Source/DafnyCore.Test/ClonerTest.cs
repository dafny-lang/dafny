using Microsoft.Dafny;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Logging.Abstractions;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Tomlyn;

namespace DafnyCore.Test;

public class ClonerTest {
  class DummyDecl : Declaration {
    public DummyDecl(Cloner cloner, Declaration original) : base(cloner, original) {
    }

    public DummyDecl(IOrigin origin, Name name, Attributes attributes, bool isRefining) : base(origin, name,
      attributes, isRefining) {
    }

    public override SymbolKind? Kind => null;
    public override string GetDescription(DafnyOptions options) {
      return "";
    }
  }

  [Fact]
  public void ClonerKeepsBodyStartTok() {
    var tokenBodyStart = new Token() { line = 2 };
    var rangeToken = new SourceOrigin(Token.NoToken, Token.NoToken);
    var specificationFrame = new LiteralExpr(Microsoft.Dafny.Token.NoToken, 1);
    var formal1 = new Formal(new SourceOrigin(tokenBodyStart, tokenBodyStart), "a", Microsoft.Dafny.Type.Bool, true, false, null) {
      IsTypeExplicit = true
    };
    var formal2 = new Formal(new SourceOrigin(tokenBodyStart, tokenBodyStart), "b", Microsoft.Dafny.Type.Bool, true, false, null) {
      IsTypeExplicit = false
    };
    var dummyDecl = new Method(rangeToken, new Name(rangeToken, "hello"),
      false, false, [], [formal1, formal2],
      [], [],
      new Specification<FrameExpression>(), new Specification<FrameExpression>([], null),
      [], new Specification<Expression>([], null),
      new BlockStmt(rangeToken, []), null, Token.NoToken, false);

    dummyDecl.BodyStartTok = tokenBodyStart;
    var cloner = new Cloner();
    var dummyDecl2 = cloner.CloneMethod(dummyDecl);
    Assert.Equal(2, dummyDecl2.BodyStartTok.line);
    Assert.Equal(2, dummyDecl2.Ins[0].Origin.StartToken.line);
    Assert.True(dummyDecl2.Ins[0].IsTypeExplicit);
    Assert.Equal(2, dummyDecl2.Ins[1].Origin.StartToken.line);
    Assert.False(dummyDecl2.Ins[1].IsTypeExplicit);
  }
}