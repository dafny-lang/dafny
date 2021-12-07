using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class DeclarationStmtOrExpr {
    public IToken? Tok;
    public IToken? EndTok;

    protected DeclarationStmtOrExpr(IToken? tok, IToken endTok) {
      Tok = tok;
      EndTok = endTok;
    }
  }

  public class StmtDeclaration : DeclarationStmtOrExpr {
    public BlockStmt Declaration;

    public StmtDeclaration(BlockStmt declaration) : base(declaration.Tok, declaration.EndTok) {
      Declaration = declaration;
    }
  }

  public class ExprDeclaration : DeclarationStmtOrExpr {
    public Expression Declaration;
    public ExprDeclaration(Expression declaration) : base(declaration.tok, Token.NoToken) {
      Declaration = declaration;
    }
  }

  public class ScopeSymbol : Symbol, ILocalizableSymbol {
    public DeclarationStmtOrExpr Declaration { get; }
    public object Node => Declaration;
    public List<ISymbol> Symbols { get; } = new List<ISymbol>();
    public override IEnumerable<ISymbol> Children => Symbols;

    public ScopeSymbol(ISymbol? scope, BlockStmt declaration) : base(scope, string.Empty) {
      Declaration = new StmtDeclaration(declaration);
    }

    public ScopeSymbol(ISymbol? scope, Expression declaration) : base(scope, string.Empty) {
      Declaration = new ExprDeclaration(declaration);
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return "";
    }
  }
}
