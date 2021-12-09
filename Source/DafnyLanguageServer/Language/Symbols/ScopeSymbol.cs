using System.Collections.Generic;
using System.Threading;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Language.Symbols {
  public abstract class DeclarationStmtOrExpr {
    public IToken Tok;
    public IToken? EndTok;
    public object Node;

    protected DeclarationStmtOrExpr(IToken tok, IToken endTok, object node) {
      Tok = tok;
      EndTok = endTok;
      Node = node;
    }
  }

  public class StmtDeclaration : DeclarationStmtOrExpr {
    public BlockStmt Declaration;

    public StmtDeclaration(BlockStmt declaration) : base(declaration.Tok, declaration.EndTok, declaration) {
      Declaration = declaration;
    }
  }

  public class ExpressionDeclaration : DeclarationStmtOrExpr {
    public Expression Declaration;
    public ExpressionDeclaration(Expression declaration) : base(declaration.tok, Token.NoToken, declaration) {
      Declaration = declaration;
    }
  }

  public class FunctionDeclaration : DeclarationStmtOrExpr {
    public Function Declaration;
    public FunctionDeclaration(Function declaration) : base(declaration.tok, Token.NoToken, declaration) {
      Declaration = declaration;
    }
  }

  public class MethodDeclaration : DeclarationStmtOrExpr {
    public Method Declaration;
    public MethodDeclaration(Method declaration) : base(declaration.tok, Token.NoToken, declaration) {
      Declaration = declaration;
    }
  }
  public class ScopeSymbol : Symbol, ILocalizableSymbol {
    public DeclarationStmtOrExpr Declaration { get; }
    public object Node => Declaration.Node;
    public List<ISymbol> Symbols { get; } = new List<ISymbol>();
    public override IEnumerable<ISymbol> Children => Symbols;

    public ScopeSymbol(ISymbol? scope, BlockStmt declaration) : base(scope, string.Empty) {
      Declaration = new StmtDeclaration(declaration);
    }

    public ScopeSymbol(ISymbol? scope, Expression declaration) : base(scope, string.Empty) {
      Declaration = new ExpressionDeclaration(declaration);
    }

    public ScopeSymbol(ISymbol? scope, Function declaration) : base(scope, string.Empty) {
      Declaration = new FunctionDeclaration(declaration);
    }
    public ScopeSymbol(ISymbol? scope, Method declaration) : base(scope, string.Empty) {
      Declaration = new MethodDeclaration(declaration);
    }

    public override TResult Accept<TResult>(ISymbolVisitor<TResult> visitor) {
      return visitor.Visit(this);
    }

    public string GetDetailText(CancellationToken cancellationToken) {
      return "";
    }
  }
}
