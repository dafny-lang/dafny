using System.Collections.Generic;
using Bpl = Microsoft.Boogie;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny translator tests")]
public class TranslatorTest {

  private void Expect(Bpl.Expr expr, bool isAlwaysTrue, bool isAlwaysFalse) {
    Assert.Equal(isAlwaysTrue, BoogieGenerator.IsExprAlways(expr, true));
    Assert.Equal(isAlwaysFalse, BoogieGenerator.IsExprAlways(expr, false));
  }

  [Fact]
  public void EnsuresIsAlwaysOptimizedCorrectly() {
    var @true = new Bpl.LiteralExpr(Bpl.Token.NoToken, true);
    const bool yes = true;
    const bool no = false;
    Bpl.IToken nt = Bpl.Token.NoToken;
    Expect(@true, isAlwaysTrue: yes, isAlwaysFalse: no);

    var @false = new Bpl.LiteralExpr(nt, false);
    Expect(@false, isAlwaysTrue: no, isAlwaysFalse: yes);

    var var = new Bpl.IdentifierExpr(nt, "v");
    Expect(var, isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Imp(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(@false, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Imp(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.And(@true, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(@false, var), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.And(var, @true), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.And(var, @false), isAlwaysTrue: no, isAlwaysFalse: yes);

    Expect(Bpl.Expr.Or(@true, var), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(@false, var), isAlwaysTrue: no, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @true), isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(Bpl.Expr.Or(var, @false), isAlwaysTrue: no, isAlwaysFalse: no);

    Expect(Bpl.Expr.Not(@true), isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(Bpl.Expr.Not(@false), isAlwaysTrue: yes, isAlwaysFalse: no);

    var forallTrue = new Bpl.ForallExpr(nt, [], [], @true);
    var forallFalse = new Bpl.ForallExpr(nt, [], [], @false);

    Expect(forallTrue, isAlwaysTrue: yes, isAlwaysFalse: no);
    Expect(forallFalse, isAlwaysTrue: no, isAlwaysFalse: no);

    var existsTrue = new Bpl.ExistsExpr(nt, [], @true);
    var existsFalse = new Bpl.ExistsExpr(nt, [], @false);

    Expect(existsFalse, isAlwaysTrue: no, isAlwaysFalse: yes);
    Expect(existsTrue, isAlwaysTrue: no, isAlwaysFalse: no);

    var forallFalseImpliesSomething = new Bpl.ForallExpr(nt, [], [], Bpl.Expr.Imp(@false, var));
    Expect(forallFalseImpliesSomething, isAlwaysTrue: yes, isAlwaysFalse: no);
  }
}
