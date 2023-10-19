//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Security.Cryptography;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Core;
using DafnyCore.Verifier;
using Microsoft.BaseTypes;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Triggers;
using Action = System.Action;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {

    /// <summary>
    /// Fills in, if necessary, the e.translationDesugaring field, and returns it.
    /// Also, makes sure that letSuchThatExprInfo maps e to something.
    /// </summary>
    Expression LetDesugaring(LetExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(!e.Exact);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (e.GetTranslationDesugaring(this) == null) {
        // For let-such-that expression:
        //   var x:X, y:Y :| P(x,y,g); F(...)
        // where
        //   - g has type G, and
        //   - tt* denotes the list of type variables in the types X and Y and expression F(...),
        // declare a function for each bound variable:
        //   function $let$x(Ty*, G): X;
        //   function $let$y(Ty*, G): Y;
        //   function $let_canCall(Ty*, G): bool;
        // and add an axiom about these functions:
        //   axiom (forall tt*:Ty*, g:G ::
        //            { $let$x(tt*, g) }
        //            { $let$y(tt*, g) }
        //            $let$_canCall(tt*, g)) ==>
        //            P($let$x(tt*, g), $let$y(tt*, g), g));
        // and create the desugaring:
        //   var x:X, y:Y := $let$x(tt*, g), $let$y(tt*, g); F(...)
        if (e is SubstLetExpr) {
          // desugar based on the original letexpr.
          var expr = (SubstLetExpr)e;
          var orgExpr = expr.orgExpr;
          Expression d = LetDesugaring(orgExpr);
          e.SetTranslationDesugaring(this, Substitute(d, null, expr.substMap, expr.typeMap));
          var orgInfo = letSuchThatExprInfo[orgExpr];
          letSuchThatExprInfo.Add(expr, new LetSuchThatExprInfo(orgInfo, this, expr.substMap, expr.typeMap));
        } else {
          // First, determine "g" as a list of Dafny variables FVs plus possibly this, $Heap, and old($Heap),
          // and determine "tt*" as a list of Dafny type variables
          LetSuchThatExprInfo info;
          {
            var FVs = new HashSet<IVariable>();
            bool usesHeap = false, usesOldHeap = false;
            var FVsHeapAt = new HashSet<Label>();
            Type usesThis = null;
            FreeVariablesUtil.ComputeFreeVariables(options, e.RHSs[0], FVs, ref usesHeap, ref usesOldHeap, FVsHeapAt, ref usesThis, false);
            var FTVs = new HashSet<TypeParameter>();
            foreach (var bv in e.BoundVars) {
              FVs.Remove(bv);
              ComputeFreeTypeVariables(bv.Type, FTVs);
            }
            ComputeFreeTypeVariables(e.RHSs[0], FTVs);
            info = new LetSuchThatExprInfo(e.tok, letSuchThatExprInfo.Count, FVs.ToList(), FTVs.ToList(), usesHeap, usesOldHeap, FVsHeapAt, usesThis, currentDeclaration);
            letSuchThatExprInfo.Add(e, info);
          }

          foreach (var bv in e.BoundVars) {
            Bpl.Variable resType = new Bpl.Formal(bv.tok, new Bpl.TypedIdent(bv.tok, Bpl.TypedIdent.NoName, TrType(bv.Type)), false);
            Bpl.Expr ante;
            List<Variable> formals = info.GAsVars(this, true, out ante, null);
            var fn = new Bpl.Function(bv.tok, info.SkolemFunctionName(bv), formals, resType);

            if (InsertChecksums) {
              InsertChecksum(e.Body, fn);
            }

            sink.AddTopLevelDeclaration(fn);
          }
          var canCallFunction = AddLetSuchThatCanCallFunction(e, info);
          AddLetSuchThenCanCallAxiom(e, info, canCallFunction);

          // now that we've declared the functions and axioms, let's prepare the let-such-that desugaring
          {
            var etran = new ExpressionTranslator(this, predef, e.tok);
            var rhss = new List<Expression>();
            foreach (var bv in e.BoundVars) {
              var args = info.SkolemFunctionArgs(bv, this, etran);
              var rhs = new BoogieFunctionCall(bv.tok, info.SkolemFunctionName(bv), info.UsesHeap, info.UsesOldHeap, info.UsesHeapAt, args.Item1, args.Item2);
              rhs.Type = bv.Type;
              rhss.Add(rhs);
            }
            var expr = new LetExpr(e.tok, e.LHSs, rhss, e.Body, true);
            expr.Type = e.Type; // resolve here
            e.SetTranslationDesugaring(this, expr);
          }
        }
      }
      return e.GetTranslationDesugaring(this);
    }

    private Bpl.Function AddLetSuchThatCanCallFunction(LetExpr e, LetSuchThatExprInfo info) {
      Bpl.Variable resType = new Bpl.Formal(e.tok, new Bpl.TypedIdent(e.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool),
        false);
      List<Variable> formals = info.GAsVars(this, true, out var ante, null);
      var canCallFunction = new Bpl.Function(e.tok, info.CanCallFunctionName(), formals, resType);

      if (InsertChecksums) {
        InsertChecksum(e.Body, canCallFunction);
      }

      sink.AddTopLevelDeclaration(canCallFunction);
      return canCallFunction;
    }

    private void AddLetSuchThenCanCallAxiom(LetExpr e, LetSuchThatExprInfo info, Bpl.Function canCallFunction) {
      var etranCC = new ExpressionTranslator(this, predef, info.HeapExpr(this, false), info.HeapExpr(this, true));
      Bpl.Expr typeAntecedents; // later ignored
      List<Variable> gg = info.GAsVars(this, false, out typeAntecedents, etranCC);
      var gExprs = new List<Bpl.Expr>();
      foreach (Bpl.Variable g in gg) {
        gExprs.Add(new Bpl.IdentifierExpr(g.tok, g));
      }

      Bpl.Trigger tr = null;
      Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
      Bpl.Expr antecedent = Bpl.Expr.True;
      foreach (var bv in e.BoundVars) {
        // create a call to $let$x(g)
        var call = FunctionCall(e.tok, info.SkolemFunctionName(bv), TrType(bv.Type), gExprs);
        tr = new Bpl.Trigger(e.tok, true, new List<Bpl.Expr> { call }, tr);
        substMap.Add(bv, new BoogieWrapper(call, bv.Type));
        if (!(bv.Type.IsTypeParameter)) {
          Bpl.Expr wh = GetWhereClause(bv.tok, call, bv.Type, etranCC, NOALLOC);
          if (wh != null) {
            antecedent = BplAnd(antecedent, wh);
          }
        }
      }

      var i = info.FTVs.Count + (info.UsesHeap ? 1 : 0) + (info.UsesOldHeap ? 1 : 0) + info.UsesHeapAt.Count;
      Expression receiverReplacement;
      if (info.ThisType == null) {
        receiverReplacement = null;
      } else {
        receiverReplacement = new BoogieWrapper(gExprs[i], info.ThisType);
        i++;
      }

      foreach (var fv in info.FVs) {
        var ge = gExprs[i];
        substMap.Add(fv, new BoogieWrapper(ge, fv.Type));
        i++;
      }

      var canCall = FunctionCall(e.tok, info.CanCallFunctionName(), Bpl.Type.Bool, gExprs);
      var p = Substitute(e.RHSs[0], receiverReplacement, substMap);
      Bpl.Expr ax = Bpl.Expr.Imp(canCall, BplAnd(antecedent, etranCC.TrExpr(p)));
      ax = BplForall(gg, tr, ax);
      AddOtherDefinition(canCallFunction, new Bpl.Axiom(e.tok, ax));
    }

    class LetSuchThatExprInfo {
      public readonly IToken Tok;
      public readonly int LetId;
      public readonly List<IVariable> FVs;
      public readonly List<Expression> FV_Exprs;  // these are what initially were the free variables, but they may have undergone substitution so they are here Expression's.
      public readonly List<TypeParameter> FTVs;
      public readonly List<Type> FTV_Types;
      public readonly bool UsesHeap;
      public readonly bool UsesOldHeap;
      public readonly List<Label> UsesHeapAt;
      public readonly Type ThisType;  // null if 'this' is not used
      public LetSuchThatExprInfo(IToken tok, int uniqueLetId,
      List<IVariable> freeVariables, List<TypeParameter> freeTypeVars,
      bool usesHeap, bool usesOldHeap, ISet<Label> usesHeapAt, Type thisType, Declaration currentDeclaration) {
        Tok = tok;
        LetId = uniqueLetId;
        FTVs = freeTypeVars;
        FTV_Types = Map(freeTypeVars, tt => (Type)new UserDefinedType(tt));
        FVs = freeVariables;
        FV_Exprs = new List<Expression>();
        foreach (var v in FVs) {
          var idExpr = new IdentifierExpr(v.Tok, v.AssignUniqueName(currentDeclaration.IdGenerator));
          idExpr.Var = v; idExpr.Type = v.Type;  // resolve here
          FV_Exprs.Add(idExpr);
        }
        UsesHeap = usesHeap;
        UsesOldHeap = usesOldHeap;
        // we convert the set of heap-at variables to a list here, once and for all; the order itself is not material, what matters is that we always use the same order
        UsesHeapAt = new List<Label>(usesHeapAt);
        ThisType = thisType;
      }
      public LetSuchThatExprInfo(LetSuchThatExprInfo template, BoogieGenerator boogieGenerator,
           Dictionary<IVariable, Expression> substMap,
           Dictionary<TypeParameter, Type> typeMap) {
        Contract.Requires(template != null);
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(substMap != null);
        Tok = template.Tok;
        LetId = template.LetId;  // reuse the ID, which ensures we get the same $let functions
        FTVs = template.FTVs;
        FTV_Types = template.FTV_Types.ConvertAll(t => t.Subst(typeMap));
        FVs = template.FVs;
        FV_Exprs = template.FV_Exprs.ConvertAll(e => BoogieGenerator.Substitute(e, null, substMap, typeMap));
        UsesHeap = template.UsesHeap;
        UsesOldHeap = template.UsesOldHeap;
        UsesHeapAt = template.UsesHeapAt;
        ThisType = template.ThisType;
      }
      public Tuple<List<Expression>, List<Type>> SkolemFunctionArgs(BoundVar bv, BoogieGenerator boogieGenerator, ExpressionTranslator etran) {
        Contract.Requires(bv != null);
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(etran != null);
        var args = new List<Expression>();
        if (ThisType != null) {
          var th = new ThisExpr(bv.tok);
          th.Type = ThisType;
          args.Add(th);
        }
        args.AddRange(FV_Exprs);
        return Tuple.Create(args, new List<Type>(FTV_Types));
      }
      public string SkolemFunctionName(BoundVar bv) {
        Contract.Requires(bv != null);
        return string.Format("$let#{0}_{1}", LetId, bv.Name);
      }
      public Bpl.Expr CanCallFunctionCall(BoogieGenerator boogieGenerator, ExpressionTranslator etran) {
        Contract.Requires(boogieGenerator != null);
        Contract.Requires(etran != null);
        var gExprs = new List<Bpl.Expr>();
        gExprs.AddRange(Map(FTV_Types, tt => boogieGenerator.TypeToTy(tt)));
        if (UsesHeap) {
          gExprs.Add(etran.HeapExpr);
        }
        if (UsesOldHeap) {
          gExprs.Add(etran.Old.HeapExpr);
        }
        foreach (var heapAtLabel in UsesHeapAt) {
          Bpl.Expr ve;
          var bv = BplBoundVar("$Heap_at_" + heapAtLabel.AssignUniqueId(boogieGenerator.CurrentIdGenerator), boogieGenerator.predef.HeapType, out ve);
          gExprs.Add(ve);
        }
        if (ThisType != null) {
          var th = new Bpl.IdentifierExpr(Tok, etran.This);
          gExprs.Add(th);
        }
        foreach (var v in FV_Exprs) {
          gExprs.Add(etran.TrExpr(v));
        }
        return FunctionCall(Tok, CanCallFunctionName(), Bpl.Type.Bool, gExprs);
      }
      public string CanCallFunctionName() {
        return string.Format("$let#{0}$canCall", LetId);
      }
      public Bpl.Expr HeapExpr(BoogieGenerator boogieGenerator, bool old) {
        Contract.Requires(boogieGenerator != null);
        return new Bpl.IdentifierExpr(Tok, old ? "$heap$old" : "$heap", boogieGenerator.predef.HeapType);
      }
      /// <summary>
      /// "wantFormals" means the returned list will consist of all in-parameters.
      /// "!wantFormals" means the returned list will consist of all bound variables.
      /// Guarantees that, in the list returned, "this" is the parameter immediately following
      /// the (0, 1, or 2) heap arguments, if there is a "this" parameter at all.
      /// Note, "typeAntecedents" is meaningfully filled only if "etran" is not null.
      /// </summary>
      public List<Variable> GAsVars(BoogieGenerator boogieGenerator, bool wantFormals, out Bpl.Expr typeAntecedents, ExpressionTranslator etran) {
        Contract.Requires(boogieGenerator != null);
        var vv = new List<Variable>();
        // first, add the type variables
        vv.AddRange(Map(FTVs, tp => NewVar(NameTypeParam(tp), boogieGenerator.predef.Ty, wantFormals)));
        typeAntecedents = Bpl.Expr.True;
        if (UsesHeap) {
          var nv = NewVar("$heap", boogieGenerator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var isGoodHeap = boogieGenerator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        if (UsesOldHeap) {
          var nv = NewVar("$heap$old", boogieGenerator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var isGoodHeap = boogieGenerator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        foreach (var heapAtLabel in UsesHeapAt) {
          var nv = NewVar("$Heap_at_" + heapAtLabel.AssignUniqueId(boogieGenerator.CurrentIdGenerator), boogieGenerator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            // TODO: It's not clear to me that $IsGoodHeap predicates are needed for these axioms. (Same comment applies above for $heap$old.)
            // But $HeapSucc relations among the various heap variables appears not needed for either soundness or completeness, since the
            // let-such-that functions will always be invoked on arguments for which these properties are known.
            var isGoodHeap = boogieGenerator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        if (ThisType != null) {
          var nv = NewVar("this", boogieGenerator.TrType(ThisType), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var th = new Bpl.IdentifierExpr(Tok, nv);
            typeAntecedents = BplAnd(typeAntecedents, boogieGenerator.ReceiverNotNull(th));
            var wh = boogieGenerator.GetWhereClause(Tok, th, ThisType, etran, NOALLOC);
            if (wh != null) {
              typeAntecedents = BplAnd(typeAntecedents, wh);
            }
          }
        }
        foreach (var v in FVs) {
          var nv = NewVar(v.Name, boogieGenerator.TrType(v.Type), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var wh = boogieGenerator.GetWhereClause(Tok, new Bpl.IdentifierExpr(Tok, nv), v.Type, etran, NOALLOC);
            if (wh != null) {
              typeAntecedents = BplAnd(typeAntecedents, wh);
            }
          }
        }
        return vv;
      }
      Bpl.Variable NewVar(string name, Bpl.Type type, bool wantFormal) {
        Contract.Requires(name != null);
        Contract.Requires(type != null);
        if (wantFormal) {
          return new Bpl.Formal(Tok, new Bpl.TypedIdent(Tok, name, type), true);
        } else {
          return new Bpl.BoundVariable(Tok, new Bpl.TypedIdent(Tok, name, type));
        }
      }
    }

    Dictionary<LetExpr, LetSuchThatExprInfo> letSuchThatExprInfo = new Dictionary<LetExpr, LetSuchThatExprInfo>();
  }
}
