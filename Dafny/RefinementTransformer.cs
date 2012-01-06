//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
// This file contains the transformations that are applied to a module that is
// constructed as a refinement of another.  It is invoked during program resolution,
// so the transformation is done syntactically.  Upon return from the RefinementTransformer,
// the caller is expected to resolve the resulting module.
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny {
  public class RefinementTransformer
  {
    ResolutionErrorReporter reporter;
    public RefinementTransformer(ResolutionErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    public void Construct(ModuleDecl m) {
      Contract.Requires(m != null);
      Contract.Requires(m.RefinementBase != null);

      var prev = m.RefinementBase;

      // TODO: What to do with the attributes of prev?  Should they be copied as well?

      // Include the imports of the base.  Note, prev is itself NOT added as an import
      // of m; instead, the contents from prev is merged directly into m.
      // (Here, we change the import declarations.  But edges for these imports will
      // not be added to the importGraph of the calling resolver.  However, the refines
      // clause gave rise to an edge in the importGraph, so the transitive import edges
      // are represented in the importGraph.)
      foreach (var im in prev.Imports) {
        if (!m.ImportNames.Contains(im.Name)) {
          m.ImportNames.Add(im.Name);
          m.Imports.Add(im);
        }
      }

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < m.TopLevelDecls.Count; i++) {
        var d = m.TopLevelDecls[i];
        if (!declaredNames.ContainsKey(d.Name)) {
          declaredNames.Add(d.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var d in prev.TopLevelDecls) {
        int index;
        if (!declaredNames.TryGetValue(d.Name, out index)) {
          m.TopLevelDecls.Add(CloneDeclaration(d, m));
        } else {
          var nw = m.TopLevelDecls[index];
          if (d is ArbitraryTypeDecl) {
            // this is allowed to be refined by any type declaration, so just keep the new one
          } else if (nw is ArbitraryTypeDecl) {
            reporter.Error(nw, "an arbitrary type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
          } else if (nw is DatatypeDecl) {
            if (d is ClassDecl) {
              reporter.Error(nw, "a datatype declaration ({0}) in a refining module cannot replace a class declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeDatatype((DatatypeDecl)nw, (DatatypeDecl)d);
            }
          } else {
            Contract.Assert(nw is ClassDecl);
            if (d is DatatypeDecl) {
              reporter.Error(nw, "a class declaration ({0}) in a refining module cannot replace a datatype declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeClass((ClassDecl)nw, (ClassDecl)d);
            }
          }
        }
      }
    }

    IToken Tok(IToken tok) {
      // TODO: do something that makes it clear that this token is from a copy
      return tok;
    }

    // -------------------------------------------------- Cloning ---------------------------------------------------------------

    TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDecl m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      // top-level declarations clone their tokens
      if (d is ArbitraryTypeDecl) {
        var dd = (ArbitraryTypeDecl)d;
        return new ArbitraryTypeDecl(Tok(dd.tok), dd.Name, m, null);
      } else if (d is DatatypeDecl) {
        var dd = (DatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new DatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, null);
        return dt;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        var cl = new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, null);
        return cl;
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    DatatypeCtor CloneCtor(DatatypeCtor ct) {
      // datatype constructors clone their tokens
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), null);
    }

    TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(tp.tok, tp.Name);
    }

    MemberDecl CloneMember(MemberDecl member) {
      // members clone their tokens
      if (member is Field) {
        var f = (Field)member;
        return new Field(Tok(f.tok), f.Name, f.IsGhost, f.IsMutable, CloneType(f.Type), null);
      } else if (member is Function) {
        var f = (Function)member;
        var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
        return new Function(Tok(f.tok), f.Name, f.IsStatic, f.IsGhost, f.IsUnlimited, tps, f.Formals.ConvertAll(CloneFormal), CloneType(f.ResultType),
          f.Req.ConvertAll(CloneExpr), f.Reads.ConvertAll(CloneFrameExpr), f.Ens.ConvertAll(CloneExpr), CloneSpecExpr(f.Decreases), CloneExpr(f.Body), null);
      } else {
        var m = (Method)member;
        var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
        return new Method(Tok(m.tok), m.Name, m.IsStatic, m.IsGhost, tps, m.Ins.ConvertAll(CloneFormal), m.Outs.ConvertAll(CloneFormal),
          m.Req.ConvertAll(CloneMayBeFreeExpr), CloneSpecFrameExpr(m.Mod), m.Ens.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(m.Decreases), CloneBlockStmt(m.Body), null);
      }
    }

    Type CloneType(Type t) {
      // TODO
      return t;
    }

    Formal CloneFormal(Formal formal) {
      // TODO
      return formal;
    }

    Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      // TODO
      return spec;
    }

    Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      // TODO
      return frame;
    }

    FrameExpression CloneFrameExpr(FrameExpression frame) {
      // TODO
      return frame;
    }

    MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      // TODO
      return expr;
    }

    Expression CloneExpr(Expression expr) {
      // TODO
      return expr;
    }

    BlockStmt CloneBlockStmt(BlockStmt stmt) {
      // TODO
      return stmt;
    }

    Statement CloneStmt(Statement stmt) {
      // TODO
      return stmt;
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    DatatypeDecl MergeDatatype(DatatypeDecl nw, DatatypeDecl prev) {
      // TODO
      return nw;
    }

    ClassDecl MergeClass(ClassDecl nw, ClassDecl prev) {
      // TODO
      return nw;
    }
  }
}
