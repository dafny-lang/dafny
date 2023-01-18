using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Compilers;

public class CheckHasNoAssumesVisitor : BottomUpVisitor {
  readonly ISinglePassCompiler compiler;
  ConcreteSyntaxTree wr;
  public CheckHasNoAssumesVisitor(ISinglePassCompiler c, ConcreteSyntaxTree wr) {
    Contract.Requires(c != null);
    compiler = c;
    this.wr = wr;
  }
  private void RejectAssume(IToken tok, Attributes attributes, ConcreteSyntaxTree wr) {
    if (!Attributes.Contains(attributes, "axiom")) {
      compiler.Error(tok, "an assume statement without an {{:axiom}} attribute cannot be compiled", wr);
    }
  }
  protected override void VisitOneStmt(Statement stmt) {
    if (stmt is AssumeStmt) {
      RejectAssume(stmt.Tok, stmt.Attributes, wr);
    } else if (stmt is AssignSuchThatStmt { AssumeToken: { Attrs: var attrs } }) {
      RejectAssume(stmt.Tok, attrs, wr);
    } else if (stmt is ForallStmt) {
      var s = (ForallStmt)stmt;
      if (s.Body == null) {
        compiler.Error(stmt.Tok, "a forall statement without a body cannot be compiled", wr);
      }
    } else if (stmt is OneBodyLoopStmt) {
      var s = (OneBodyLoopStmt)stmt;
      if (s.Body == null) {
        compiler.Error(stmt.Tok, "a loop without a body cannot be compiled", wr);
      }
    }
  }
}