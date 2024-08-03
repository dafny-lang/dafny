using System.Collections.Generic;
using System.Linq;
using JetBrains.Annotations;
using Microsoft.Dafny;

namespace Microsoft.Dafny;

// Class to traverse a program top-down, especially aimed at identifying expressions and statements,
// and in their context
// How to use:
// - Define a subclass of ProgramTraverser
// - Implement the methods (TopDown|BottomUp)(Enter|Exit), override Traverse if needed.
// - Call any Traverse() method.
public class ProgramTraverser {
  public enum ContinuationStatus {
    Ok,    // Continue exploration
    Skip,  // Skip this node and its descendants  (valid only on entering a node)
    Stop,  // Stop the entire traversal here, but traverse ancestors in bottom-up
  }
  protected const ContinuationStatus ok = ContinuationStatus.Ok;
  protected const ContinuationStatus skip = ContinuationStatus.Skip;
  protected const ContinuationStatus stop = ContinuationStatus.Stop;
  // Returns true if statement needs to be traversed
  protected virtual ContinuationStatus OnEnter(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
    return ok;
  }
  // Returns true if expression needs to be traversed
  protected virtual ContinuationStatus OnEnter(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
    return ok;
  }

  // Returns true if need to stop the traversal entirely
  protected virtual bool OnExit(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
    return false;
  }
  // Returns true if need to stop the traversal entirely
  protected virtual bool OnExit(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
    return false;
  }

  protected virtual ContinuationStatus OnEnter(MemberDecl memberDecl, [CanBeNull] string field, [CanBeNull] object parent) {
    return ok;
  }

  // Traverse methods retun true to interrupt.
  public bool Traverse(Program program) {
    if (program == null) {
      return false;
    }

    return program.Modules().Any(Traverse);
  }

  public bool Traverse(ModuleDefinition moduleDefinition) {
    if (moduleDefinition == null) {
      return false;
    }

    return Traverse(moduleDefinition.TopLevelDecls);
  }

  public bool Traverse(IEnumerable<TopLevelDecl> topLevelDecls) {
    if (topLevelDecls == null) {
      return false;
    }

    foreach (var topLevelDecl in topLevelDecls) {
      if (Traverse(topLevelDecl)) {
        return true;
      }
    }

    return false;
  }

  public bool Traverse(ModuleDecl moduleDecl) {
    if (moduleDecl == null) {
      return false;
    }

    if (moduleDecl is LiteralModuleDecl l) {
      return Traverse(l.ModuleDef);
    } else if (moduleDecl is AbstractModuleDecl a) {
      return Traverse(a.CompileRoot);
    }/* else if (moduleDecl is AliasModuleDecl a) {
        
      } else if (moduleDecl is ModuleExportDecl m) {
        
      }*/

    return false;
  }

  public bool Traverse(Formal formal) {
    if (formal == null) {
      return false;
    }

    if (formal.DefaultValue != null && Traverse(formal.DefaultValue, "DefaultValue", formal)) {
      return true;
    }

    return false;
  }

  public bool Traverse(DatatypeCtor ctor) {
    if (ctor == null) {
      return false;
    }

    if (ctor.Formals.Any(Traverse)) {
      return true;
    }

    return false;
  }

  public bool Traverse(TopLevelDecl topd) {
    if (topd == null) {
      return false;
    }

    var d = topd is ClassLikeDecl classDecl && classDecl.NonNullTypeDecl != null ? classDecl.NonNullTypeDecl : topd;

    if (d is TopLevelDeclWithMembers tdm) {
      // ClassDecl, DatatypeDecl, AbstractTypeDecl, NewtypeDecl 
      if (tdm.Members.Any(memberDecl => Traverse(memberDecl, "Members", tdm))) {
        return true;
      }

      if (tdm is IteratorDecl iter) {
        // TODO: Import this
        if (Attributes.SubExpressions(iter.Attributes).Any(e => Traverse(e, "Attributes.SubExpressions", iter))) {
          return true;
        }
        if (Attributes.SubExpressions(iter.Reads.Attributes).Any(e => Traverse(e, "Reads.Attributes.SubExpressions", iter))) {
          return true;
        }
        if (iter.Reads.Expressions.Any(e => Traverse(e.E, "Reads.Expressions.E", iter))) {
          return true;
        }
        if (Attributes.SubExpressions(iter.Modifies.Attributes).Any(e => Traverse(e, "Modifies.Attributes.SubExpressions", iter))) {
          return true;
        }
        if (iter.Modifies.Expressions.Any(e => Traverse(e.E, "Modifies.Expressions.E", iter))) {
          return true;
        }
        if (Attributes.SubExpressions(iter.Decreases.Attributes).Any(e => Traverse(e, "Decreases.Attributes.SubExpressions", iter))) {
          return true;
        }
        if (iter.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions.E", iter))) {
          return true;
        }
        if (iter.Requires.Any(e => Traverse(e.E, "Requires.E", iter))) {
          return true;
        }
        if (iter.Ensures.Any(e => Traverse(e.E, "Ensures.E", iter))) {
          return true;
        }
        if (iter.YieldRequires.Any(e => Traverse(e.E, "YieldRequires.E", iter))) {
          return true;
        }
        if (iter.YieldEnsures.Any(e => Traverse(e.E, "YieldEnsures.E", iter))) {
          return true;
        }
        if (Traverse(iter.Body, "Body", iter)) {
          return true;
        }
      }

      if (tdm is DatatypeDecl dtd) {
        if (dtd.Ctors.Any(Traverse)) {
          return true;
        }
      }
    } else if (d is ModuleDecl md) {
      return Traverse(md);
    } else if (d is TypeSynonymDecl tsd) {
      // Nothing here.
    }

    return false;
  }

  public bool Traverse(MemberDecl memberDeclaration, [CanBeNull] string field, [CanBeNull] object parent) {
    if (memberDeclaration == null) {
      return false;
    }

    var enterResult = OnEnter(memberDeclaration, field, parent);
    if (enterResult is stop or skip) {
      return enterResult == stop;
    }

    if (memberDeclaration is Field fi) {
      if (fi.SubExpressions.Any(expr => Traverse(expr, "SubExpressions", fi))) {
        return true;
      }
    } else if (memberDeclaration is Function f) {
      if (f.Ins.Any(Traverse)) {
        return true;
      }
      if (f.Result != null && f.Result.DefaultValue != null && Traverse(f.Result.DefaultValue, "Result.DefaultValue", f)) {
        return true;
      }
      if (f.Req.Any(e => Traverse(e.E, "Req.E", f))) {
        return true;
      }
      if (f.Reads.Expressions.Any(e => Traverse(e.E, "Reads.E", f))) {
        return true;
      }
      if (f.Ens.Any(e => Traverse(e.E, "Ens.E", f))) {
        return true;
      }
      if (f.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions", f))) {
        return true;
      }
      if (Traverse(f.Body, "Body", f)) {
        return true;
      }

      if (f.ByMethodDecl != null && Traverse(f.ByMethodDecl, "ByMethodDecl", f)) {
        return true;
      }

      if (f.ByMethodDecl == null || f.ByMethodDecl.Body != f.ByMethodBody) {
        if (f.ByMethodBody != null && Traverse(f.ByMethodBody, "ByMethodBody", f)) {
          return true;
        }
      }
    } else if (memberDeclaration is Method m) {
      // For example, default value of formals is non-ghost
      if (m.Ins.Any(formal => formal.DefaultValue != null
                              && Traverse(formal.DefaultValue, "Ins.DefaultValue", m))) {
        return true;
      }
      if (m.Req.Any(e => Traverse(e.E, "Req.E", m))) {
        return true;
      }
      if (m.Reads.Expressions.Any(e => Traverse(e.E, "Reads.E", m))) {
        return true;
      }
      if (m.Mod.Expressions.Any(e => Traverse(e.E, "Mod.E", m) == true)) {
        return true;
      }
      if (m.Ens.Any(e => Traverse(e.E, "Ens.E", m))) {
        return true;
      }
      if (m.Decreases.Expressions.Any(e => Traverse(e, "Decreases.Expressions", m))) {
        return true;
      }
      if (Traverse(m.Body, "Body", m)) {
        return true;
      }
    }

    return false;
  }

  public virtual bool Traverse(Statement stmt, [CanBeNull] string field, [CanBeNull] object parent) {
    if (stmt == null) {
      return false;
    }

    var enterResult = OnEnter(stmt, field, parent);
    if (enterResult is stop or skip) {
      return enterResult == stop;
    }

    return stmt.NonSpecificationSubExpressions.Any(subExpr => Traverse(subExpr, "NonSpecificationSubExpressions", stmt)) ||
           stmt.SpecificationSubExpressions.Any(subExpr => Traverse(subExpr, "SpecificationSubExpressions", stmt)) ||
           stmt.SubStatements.Any(subStmt => Traverse(subStmt, "SubStatements", stmt)) ||
           OnExit(stmt, field, parent);
  }

  public virtual bool Traverse(Expression expr, [CanBeNull] string field, [CanBeNull] object parent) {
    if (expr == null) {
      return false;
    }

    var enterResult = OnEnter(expr, field, parent);
    if (enterResult is stop or skip) {
      return enterResult == stop;
    }

    return expr.SubExpressions.Any(subExpr => Traverse(subExpr, "SubExpression", expr)) ||
           OnExit(expr, field, parent);
  }
}