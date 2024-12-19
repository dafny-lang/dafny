using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// A CasePattern is either a BoundVar or a datatype constructor with optional arguments.
/// Lexically, the CasePattern starts with an identifier.  If it continues with an open paren (as
/// indicated by Arguments being non-null), then the CasePattern is a datatype constructor.  If
/// it continues with a colon (which is indicated by Var.Type not being a proxy type), then it is
/// a BoundVar.  But if it ends with just the identifier, then resolution is required to figure out
/// which it is; in this case, Var is non-null, because this is the only place where Var.IsGhost
/// is recorded by the parser.
/// </summary>
public class CasePattern<VT> : TokenNode
  where VT : class, IVariable {
  public readonly string Id;
  // After successful resolution, exactly one of the following two fields is non-null.

  [FilledInDuringResolution]
  public DatatypeCtor Ctor;  // finalized by resolution (null if the pattern is a bound variable)
  public VT Var;  // finalized by resolution (null if the pattern is a constructor)  Invariant:  Var != null ==> Arguments == null
  public List<CasePattern<VT>> Arguments;

  [FilledInDuringResolution] public Expression Expr;  // an r-value version of the CasePattern;

  public void MakeAConstructor() {
    this.Arguments = new List<CasePattern<VT>>();
  }

  public CasePattern(Cloner cloner, CasePattern<VT> original) {
    tok = cloner.Origin(original.Tok);
    Id = original.Id;
    if (original.Var != null) {
      Var = cloner.CloneIVariable(original.Var, false);
    }

    if (original.Arguments != null) {
      Arguments = original.Arguments.Select(cloner.CloneCasePattern<VT>).ToList();
    }

    // In this case, tt is important to resolve the resolved fields AFTER the Arguments above.
    // If we resolve the expression first, the references to variables declared in the case pattern
    // will be cloned as references instead of declarations,
    // and when we clone the declarations the cache in Cloner.clones will incorrectly return
    // the original variable instead.
    if (cloner.CloneResolvedFields) {
      Expr = cloner.CloneExpr(original.Expr);
      Ctor = original.Ctor;
    }
  }

  public CasePattern(IOrigin tok, string id, [Captured] List<CasePattern<VT>> arguments) {
    Contract.Requires(tok != null);
    Contract.Requires(id != null);
    this.tok = tok;
    Id = id;
    Arguments = arguments;
  }

  public CasePattern(IOrigin tok, VT bv) {
    Contract.Requires(tok != null);
    Contract.Requires(bv != null);
    this.tok = tok;
    Id = bv.Name;
    Var = bv;
  }

  /// <summary>
  /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
  /// to Expr.
  /// </summary>
  public void AssembleExpr(List<Type> dtvTypeArgs) {
    Contract.Requires(Var != null || dtvTypeArgs != null);
    if (Var != null) {
      Contract.Assert(this.Id == this.Var.Name);
      this.Expr = new IdentifierExpr(this.Tok, this.Var);
    } else {
      var dtValue = new DatatypeValue(this.Tok, this.Ctor.EnclosingDatatype.Name, this.Id,
        this.Arguments == null ? new List<Expression>() : this.Arguments.ConvertAll(arg => arg.Expr));
      dtValue.Ctor = this.Ctor;  // resolve here
      dtValue.InferredTypeArgs.AddRange(dtvTypeArgs);  // resolve here
      dtValue.Type = new UserDefinedType(this.Tok, this.Ctor.EnclosingDatatype.Name, this.Ctor.EnclosingDatatype, dtvTypeArgs);
      this.Expr = dtValue;
    }
  }

  /// <summary>
  /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
  /// to Expr.
  /// </summary>
  public void AssembleExprPreType(List<PreType> dtvPreTypeArgs) {
    Contract.Requires(Var != null || dtvPreTypeArgs != null);
    if (Var != null) {
      Contract.Assert(this.Id == this.Var.Name);
      this.Expr = new IdentifierExpr(this.Tok, this.Var) {
        PreType = this.Var.PreType
      };
    } else {
      var dtValue = new DatatypeValue(this.Tok, this.Ctor.EnclosingDatatype.Name, this.Id,
        this.Arguments == null ? new List<Expression>() : this.Arguments.ConvertAll(arg => arg.Expr)) {
        Ctor = this.Ctor,
        PreType = new DPreType(this.Ctor.EnclosingDatatype, dtvPreTypeArgs)
      };
      dtValue.InferredPreTypeArgs.AddRange(dtvPreTypeArgs); // resolve here
      this.Expr = dtValue;
    }
  }

  public IEnumerable<VT> Vars {
    get {
      if (Var != null) {
        yield return Var;
      } else {
        if (Arguments != null) {
          foreach (var arg in Arguments) {
            foreach (var bv in arg.Vars) {
              yield return bv;
            }
          }
        }
      }
    }
  }

  public override IEnumerable<INode> Children => Var == null ? (Arguments ?? Enumerable.Empty<Node>()) : new[] { Var };
  public override IEnumerable<INode> PreResolveChildren => Children;
}