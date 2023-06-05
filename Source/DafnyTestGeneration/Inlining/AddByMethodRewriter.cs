#nullable disable

using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;
using Microsoft.Dafny;
using Program = Microsoft.Dafny.Program;
using Function = Microsoft.Dafny.Function;

namespace DafnyTestGeneration.Inlining;

/// <summary>
/// Turns each function into a function-by-method.
/// Copies body of the function into the body of the corresponding method.
/// </summary>
public class AddByMethodRewriter : IRewriter {
  
  private Cloner cloner = new Cloner();

  protected internal AddByMethodRewriter(ErrorReporter reporter) : base(reporter) {
  }

  internal void PreResolve(Program program) {
    AddByMethod(program.DefaultModule);
  }

  private void AddByMethod(TopLevelDecl d) {
    if (d is LiteralModuleDecl moduleDecl) {
      moduleDecl.ModuleDef.TopLevelDecls.ForEach(AddByMethod);
    } else if (d is TopLevelDeclWithMembers withMembers) {
      withMembers.Members.OfType<Function>().Iter(AddByMethod);
    }
  }

  private static Attributes RemoveOpaqueAttr(Attributes attributes, Cloner cloner) {
    if (attributes == null) {
      return null;
    }

    if (attributes.Name == "opaque") {
      RemoveOpaqueAttr(attributes.Prev, cloner);
    }

    if (attributes is UserSuppliedAttributes) {
      var usa = (UserSuppliedAttributes)attributes;
      return new UserSuppliedAttributes(
        cloner.Tok(usa.tok),
        cloner.Tok(usa.OpenBrace),
        cloner.Tok(usa.CloseBrace),
        attributes.Args.ConvertAll(cloner.CloneExpr),
        RemoveOpaqueAttr(attributes.Prev, cloner));
    }

    return new Attributes(attributes.Name,
      attributes.Args.ConvertAll(cloner.CloneExpr),
      RemoveOpaqueAttr(attributes.Prev, cloner));
  }

  private void AddByMethod(Function func) {
    
    /*var formals = func.Formals.Select(formal => new Microsoft.Dafny.IdentifierExpr(new Token(), formal) as Expression).ToList();
    
    func.Ens.Add(new AttributedExpression(new BinaryExpr(
      new Token(), 
      BinaryExpr.Opcode.Eq, 
      new ApplyExpr(new Token(), new NameSegment(new Token(), func.Name, func.TypeArgs.ConvertAll(arg => new UserDefinedType(new Token(), arg) as Microsoft.Dafny.Type)), formals,new Token()), 
      cloner.CloneExpr(func.Body))));*/
    
    func.Attributes = RemoveOpaqueAttr(func.Attributes, new Cloner());
    if (func.IsGhost || func.Body == null || func.ByMethodBody != null || !Utils.AttributeFinder.MembersHasAttribute(func, "testInline")) {
      return;
    }

    var returnStatement = new ReturnStmt(func.Body.RangeToken,
      new List<AssignmentRhs> { new ExprRhs(new Cloner().CloneExpr(func.Body)) });
    func.ByMethodBody = new BlockStmt(
      func.Body.RangeToken,
      new List<Statement> { returnStatement });
    func.ByMethodTok = func.Body.tok;
  }
}