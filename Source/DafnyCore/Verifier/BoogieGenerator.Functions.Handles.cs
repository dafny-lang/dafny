using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using DafnyCore.Verifier;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using Bpl = Microsoft.Boogie;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny;

public partial class BoogieGenerator {
  
  public string FunctionHandle(Function f) {
    Contract.Requires(f != null);
    if (functionHandles.TryGetValue(f, out var name)) {
      Contract.Assert(name != null);
    } else {
      name = f.FullSanitizedName + "#Handle";
      functionHandles[f] = name;
      var formalVars = MkTyParamBinders(GetTypeParamsIncludingType(f), out var args);
      var argsRequires = new List<Expr>(args); // Requires don't have reveal parameters
      var formals = MkTyParamFormals(f.TypeArgs, false, true);
      var tyargs = new List<Expr>();
      foreach (var fm in f.Ins) {
        tyargs.Add(TypeToTy(fm.Type));
      }
      tyargs.Add(TypeToTy(f.ResultType));
      if (f.IsFuelAware()) {
        formalVars.Add(BplBoundVar("$ly", Predef.LayerType, out var ly));
        args.Add(ly);
        argsRequires.Add(ly);
        formals.Add(BplFormalVar("$fuel", Predef.LayerType, true));
        AddFuelSuccSynonymAxiom(f, true);
      }
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        formalVars.Add(BplBoundVar("$reveal", Boogie.Type.Bool, out var reveal));
        args.Add(reveal);
        formals.Add(BplFormalVar("$reveal", Boogie.Type.Bool, true));
      }

      Func<List<Expr>, List<Expr>> snocSelf = x => x;
      Func<List<Expr>, List<Expr>> snocPrevH = x => x;
      Expression selfExpr;
      Dictionary<IVariable, Expression> rhsDict = new Dictionary<IVariable, Expression>();
      if (f is TwoStateFunction) {
        // also add previous-heap to the list of fixed arguments of the handle
        var prevH = BplBoundVar("$prevHeap", Predef.HeapType, formalVars);
        formals.Add(BplFormalVar("h", Predef.HeapType, true));
        snocPrevH = xs => Snoc(xs, prevH);
      }
      if (f.IsStatic) {
        selfExpr = null;
      } else {
        var selfTy = TrType(UserDefinedType.FromTopLevelDecl(f.Origin, f.EnclosingClass));
        var self = BplBoundVar("$self", selfTy, formalVars);
        formals.Add(BplFormalVar("self", selfTy, true));
        snocSelf = xs => Snoc(xs, self);
        var wrapperType = UserDefinedType.FromTopLevelDecl(f.Origin, f.EnclosingClass);
        selfExpr = new BoogieWrapper(self, wrapperType);
      }

      // F#Handle(Ty, .., Ty, LayerType, ref) : HandleType
      sink.AddTopLevelDeclaration(
        new Bpl.Function(f.Origin, name, formals, BplFormalVar(null, Predef.HandleType, false)));

      var bvars = new List<Variable>();
      var lhsArgs = new List<Expr>();
      var rhsArgs = new List<Expr>();
      var funcVars = new List<Variable>();
      var funcArgs = new List<Expr>();
      var boxedFuncArgs = new List<Expr>();

      var idGen = f.IdGenerator.NestedFreshIdGenerator("$fh$");
      foreach (var fm in f.Ins) {
        string fmName = idGen.FreshId("x#");
        // Box and its [Unbox]args
        var fe = BplBoundVar(fmName, Predef.BoxType, bvars);
        lhsArgs.Add(fe);
        var be = UnboxUnlessInherentlyBoxed(fe, fm.Type);
        rhsArgs.Add(be);

        rhsDict[fm] = new BoogieWrapper(be, fm.Type);
        // args and its [Box]args
        var arg = BplBoundVar(fmName, TrType(fm.Type), funcVars);
        funcArgs.Add(arg);
        var boxed = BoxIfNotNormallyBoxed(arg.tok, arg, fm.Type);
        boxedFuncArgs.Add(boxed);
      }

      var h = BplBoundVar("$heap", Predef.HeapType, formalVars);

      int arity = f.Ins.Count;

      AddApplyBoxAxiomForFunctionHandle(f, name, snocSelf, snocPrevH, args, arity, h, lhsArgs, rhsArgs, formalVars, bvars);
      AddRequiresAxiomForFunctionHandle(f, name, snocSelf, snocPrevH, args, arity, tyargs, h, lhsArgs, formalVars, bvars, argsRequires, rhsArgs);
      AddIsMemberAxiomForFunctionHandle(f, name, snocSelf, snocPrevH, args, arity, h, lhsArgs, selfExpr, rhsDict, argsRequires, formalVars, bvars);
      AddApplyUnboxAxiomForFunctionHandle(f, name, snocSelf, snocPrevH, args, h, funcArgs, arity, boxedFuncArgs, formalVars, funcVars);
    }
    return name;
  }

  private void AddApplyUnboxAxiomForFunctionHandle(Function f, string name, Func<List<Expr>, List<Expr>> snocSelf, Func<List<Expr>, List<Expr>> snocPrevH, List<Expr> args,
    Expr h, List<Expr> funcArgs, int arity, List<Expr> boxedFuncArgs, List<Variable> formalVars, List<Variable> funcVars)
  {
    // F(Layer, Heap, self, arg1, .., argN)
    // = [Unbox]Apply1(Ty.., F#Handle(Layer, self), Heap, [Box]arg1, ..., [Box]argN)

    var fhandle = FunctionCall(f.Origin, name, Predef.HandleType, snocSelf(snocPrevH(args)));
    var argsH = f.ReadsHeap ? Snoc(snocPrevH(args), h) : args;
    var lhs = FunctionCall(f.Origin, f.FullSanitizedName, TrType(f.ResultType), Concat(snocSelf(argsH), funcArgs));
    var rhs = FunctionCall(f.Origin, Apply(arity), TrType(f.ResultType), Cons(h, Cons(fhandle, boxedFuncArgs)));
    var rhsUnboxed = UnboxUnlessInherentlyBoxed(rhs, f.ResultType);
    var tr = BplTriggerHeap(this, f.Origin, lhs, f.ReadsHeap ? null : h);

    AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Origin,
      BplForall(Concat(formalVars, funcVars), tr, Expr.Eq(lhs, rhsUnboxed)))));
  }

  private void AddIsMemberAxiomForFunctionHandle(Function f, string name, Func<List<Expr>, List<Expr>> snocSelf, Func<List<Expr>, List<Expr>> snocPrevH, List<Expr> args,
    int arity, Expr h, List<Expr> lhsArgs, Expression selfExpr, Dictionary<IVariable, Expression> rhsDict, List<Expr> argsRequires,
    List<Variable> formalVars, List<Variable> bvars)
  {
    // As a first approximation, the following axiom is of the form:
    // Reads(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
    //   =  $Frame_F(args...)
    // However, .reads ands .requires functions require special attention.
    // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
    // In both cases, the precondition of the receiving function must be checked before its reads clause can
    // be referred to.

    var fhandle = FunctionCall(f.Origin, name, Predef.HandleType, snocSelf(snocPrevH(args)));
    Expr lhs_inner = FunctionCall(f.Origin, Reads(arity), TrType(program.SystemModuleManager.ObjectSetType()), Cons(h, Cons(fhandle, lhsArgs)));

    Expr bx; var bxVar = BplBoundVar("$bx", Predef.BoxType, out bx);
    Expr unboxBx = FunctionCall(f.Origin, BuiltinFunction.Unbox, Predef.RefType, bx);
    Expr lhs = IsSetMember(f.Origin, lhs_inner, bx, true);

    var et = new ExpressionTranslator(this, Predef, h, f);
    var rhs = InRWClause_Aux(f.Origin, unboxBx, bx, null, f.Reads.Expressions, false, et, selfExpr, rhsDict);

    if (f.EnclosingClass is ArrowTypeDecl) {
      var argsH = f.ReadsHeap ? Snoc(snocPrevH(argsRequires), h) : argsRequires;
      var precondition = FunctionCall(f.Origin, Requires(arity), Bpl.Type.Bool, Concat(snocSelf(argsH), lhsArgs));
      sink.AddTopLevelDeclaration(new Axiom(f.Origin,
        BplForall(Cons(bxVar, Concat(formalVars, bvars)), BplTrigger(lhs), BplImp(precondition, Expr.Eq(lhs, rhs)))));
    } else {
      sink.AddTopLevelDeclaration(new Axiom(f.Origin,
        BplForall(Cons(bxVar, Concat(formalVars, bvars)), BplTrigger(lhs), Expr.Eq(lhs, rhs))));
    }
  }

  private void AddRequiresAxiomForFunctionHandle(Function f, string name, Func<List<Expr>, List<Expr>> snocSelf, Func<List<Expr>, List<Expr>> snocPrevH, List<Expr> args,
    int arity, List<Expr> tyargs, Expr h, List<Expr> lhsArgs, List<Variable> formalVars, List<Variable> bvars, List<Expr> argsRequires, List<Expr> rhsArgs)
  {
    // As a first approximation, the following axiom is of the form:
    // Requires(Ty.., F#Handle( Ty1, ..., TyN, Layer, reveal, self), Heap, arg1, ..., argN)
    //   = F#Requires(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)
    // However, .reads ands .requires functions require special attention.
    // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
    // The requires clause of the .requires function is simply true.
    // The requires clause of the .reads function checks that the precondition of the receiving function holds.

    var fhandle = FunctionCall(f.Origin, name, Predef.HandleType, snocSelf(snocPrevH(args)));
    var lhs = FunctionCall(f.Origin, Requires(arity), Bpl.Type.Bool, Cons(h, Cons(fhandle, lhsArgs)));
    Expr rhs;
    if (f.EnclosingClass is ArrowTypeDecl && f.Name == "requires") {
      AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.Origin,
        BplForall(Concat(formalVars, bvars), BplTrigger(lhs), Expr.Eq(lhs, Expr.True))));
    } else if (f.EnclosingClass is ArrowTypeDecl && f.Name == "reads") {
      var args_h = f.ReadsHeap ? Snoc(snocPrevH(argsRequires), h) : argsRequires;
      var pre = FunctionCall(f.Origin, Requires(arity), Bpl.Type.Bool, Concat(snocSelf(args_h), lhsArgs));
      AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Origin,
        BplForall(Concat(formalVars, bvars), BplTrigger(lhs), Expr.Eq(lhs, pre)))));
    } else {
      var args_h = f.ReadsHeap ? Snoc(snocPrevH(argsRequires), h) : argsRequires;
      rhs = FunctionCall(f.Origin, RequiresName(f), Bpl.Type.Bool, Concat(snocSelf(args_h), rhsArgs));
      AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.Origin,
        BplForall(Concat(formalVars, bvars), BplTrigger(lhs), Expr.Eq(lhs, rhs))));
    }
  }

  private void AddApplyBoxAxiomForFunctionHandle(Function f, string name, Func<List<Expr>, List<Expr>> snocSelf, Func<List<Expr>, List<Expr>> snocPrevH, List<Expr> args,
    int arity, Expr h, List<Expr> lhsArgs, List<Expr> rhsArgs, List<Variable> formalVars, List<Variable> bvars)
  {
    // Apply(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
    //   = [Box] F(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

    var fhandle = FunctionCall(f.Origin, name, Predef.HandleType, snocSelf(snocPrevH(args)));
    var lhs = FunctionCall(f.Origin, Apply(arity), TrType(f.ResultType),
      Cons(h, Cons(fhandle, lhsArgs)));
    var argsH = f.ReadsHeap ? Snoc(snocPrevH(args), h) : args;
    var rhs = FunctionCall(f.Origin, f.FullSanitizedName, TrType(f.ResultType), Concat(snocSelf(argsH), rhsArgs));
    var rhsBoxed = BoxIfNotNormallyBoxed(rhs.tok, rhs, f.ResultType);

    AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.Origin,
      BplForall(Concat(formalVars, bvars), BplTrigger(lhs), Expr.Eq(lhs, rhsBoxed)))));
  }
}
