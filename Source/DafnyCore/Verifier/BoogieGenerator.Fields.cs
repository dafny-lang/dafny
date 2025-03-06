using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text;
using Microsoft.Boogie;
using Bpl = Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using PODesc = Microsoft.Dafny.ProofObligationDescription;

namespace Microsoft.Dafny {
  public partial class BoogieGenerator {



    Bpl.Constant GetField(Field f) {
      Contract.Requires(f != null && f.IsMutable);
      Contract.Requires(sink != null && Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      Contract.Assert(VisibleInScope(f));

      Bpl.Constant fc;
      if (fields.TryGetValue(f, out fc)) {
        Contract.Assert(fc != null);
      } else {
        // const f: Field ty;
        Bpl.Type ty = Predef.FieldName(f.Origin);
        fc = new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, f.FullSanitizedName, ty), false);
        fields.Add(f, fc);
        // axiom FDim(f) == 0 && FieldOfDecl(C, name) == f &&
        //       $IsGhostField(f);    // if the field is a ghost field
        // OR:
        //       !$IsGhostField(f);    // if the field is not a ghost field
        Bpl.Expr fdim = Bpl.Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.FDim, ty, Bpl.Expr.Ident(fc)), Bpl.Expr.Literal(0));
        Bpl.Expr declType = Bpl.Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.FieldOfDecl, ty, new Bpl.IdentifierExpr(f.Origin, GetClass(cce.NonNull(f.EnclosingClass))), new Bpl.IdentifierExpr(f.Origin, GetFieldNameFamily(f.Name))), Bpl.Expr.Ident(fc));
        Bpl.Expr cond = BplAnd(fdim, declType);
        var ig = FunctionCall(f.Origin, BuiltinFunction.IsGhostField, ty, Bpl.Expr.Ident(fc));
        cond = BplAnd(cond, f.IsGhost ? ig : Bpl.Expr.Not(ig));
        Bpl.Axiom ax = new Bpl.Axiom(f.Origin, cond);
        AddOtherDefinition(fc, ax);
      }
      return fc;
    }


    Bpl.Function GetReadonlyField(Field f) {
      Contract.Requires(f != null && !f.IsMutable);
      Contract.Requires(sink != null && Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Function>() != null);

      Contract.Assert(VisibleInScope(f));

      Bpl.Function ff;
      if (fieldFunctions.TryGetValue(f, out ff)) {
        Contract.Assert(ff != null);
      } else {
        // Here are some built-in functions defined in "predef" (so there's no need to cache them in "fieldFunctions")
        if (f.EnclosingClass is ArrayClassDecl && f.Name == "Length") {
          return Predef.ArrayLength;
        } else if (f.EnclosingClass is ValuetypeDecl { Name: "real" } && f.Name == "Floor") {
          return Predef.RealFloor;
        } else if (f is SpecialField && !(f is DatatypeDestructor || f.EnclosingClass is TopLevelDeclWithMembers and not ValuetypeDecl)) {
          if (f.Name is "Keys" or "Values" or "Items") {
            var fType = f.Type.NormalizeExpand();
            Contract.Assert(fType is SetType);
            var setType = (SetType)fType;
            return f.Name switch {
              "Keys" => setType.Finite ? Predef.MapDomain : Predef.IMapDomain,
              "Values" => setType.Finite ? Predef.MapValues : Predef.IMapValues,
              _ => setType.Finite ? Predef.MapItems : Predef.IMapItems
            };
          }
          if (f.Name == "IsLimit") {
            return Predef.ORDINAL_IsLimit;
          } else if (f.Name == "IsSucc") {
            return Predef.ORDINAL_IsSucc;
          } else if (f.Name == "Offset") {
            return Predef.ORDINAL_Offset;
          } else if (f.Name == "IsNat") {
            return Predef.ORDINAL_IsNat;
          }
        } else if (f.FullSanitizedName == "_System.Tuple2._0") {
          return Predef.Tuple2Destructors0;
        } else if (f.FullSanitizedName == "_System.Tuple2._1") {
          return Predef.Tuple2Destructors1;
        }

        // Create a new function
        // function f(Ref): ty;
        List<Variable> formals = [];
        if (f is ConstantField) {
          formals.AddRange(MkTyParamFormals(GetTypeParams(f.EnclosingClass), false));
        }
        if (!f.IsStatic) {
          var udt = UserDefinedType.FromTopLevelDecl(f.Origin, f.EnclosingClass);
          Bpl.Type receiverType = TrType(udt);
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, f is ConstantField ? "this" : Bpl.TypedIdent.NoName, receiverType), true));
        }
        Bpl.Formal result = new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, Bpl.TypedIdent.NoName, TrType(f.Type)), false);
        ff = new Bpl.Function(f.Origin, f.FullSanitizedName, [], formals, result, null, null);

        if (InsertChecksums) {
          var dt = f.EnclosingClass as DatatypeDecl;
          if (dt != null) {
            InsertChecksum(dt, ff);
          }
          // TODO(wuestholz): Do we need to handle more cases?
        }

        // add the newly created function to the cache, so that there will only be one copy of it
        fieldFunctions.Add(f, ff);

        // declare function among Boogie top-level declarations, if needed, and treat certain fields specially
        if (f is ConstantField) {
          // declare the function with its initial value, if any
          // function QQ():int { 3 }
          var cf = (ConstantField)f;
          if (cf.Rhs != null && RevealedInScope(cf)) {
            var etran = new ExpressionTranslator(this, Predef, NewOneHeapExpr(f.Origin), null);
            if (!IsOpaque(cf, options)) {
              var definitionAxiom = ff.CreateDefinitionAxiom(etran.TrExpr(cf.Rhs));
              definitionAxiom.CanHide = true;
              sink.AddTopLevelDeclaration(definitionAxiom);
            }
          }
          sink.AddTopLevelDeclaration(ff);

        } else if (f.EnclosingClass is ArrayClassDecl) {
          // add non-negative-range axioms for array Length fields
          // axiom (forall o: Ref :: 0 <= array.Length(o));
          Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "o", Predef.RefType));
          Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(f.Origin, oVar);
          var rhs = new Bpl.NAryExpr(f.Origin, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o });
          Bpl.Expr body = Bpl.Expr.Le(Bpl.Expr.Literal(0), rhs);
          var trigger = BplTrigger(rhs);
          Bpl.Expr qq = new Bpl.ForallExpr(f.Origin, [oVar], trigger, body);
          sink.AddTopLevelDeclaration(new Bpl.Axiom(f.Origin, qq));
        }
      }
      return ff;
    }

    Bpl.Expr GetField(MemberSelectExpr fse) {
      Contract.Requires(fse != null);
      Contract.Requires(fse.Member != null && fse.Member is Field && ((Field)(fse.Member)).IsMutable);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return new Bpl.IdentifierExpr(fse.Origin, GetField((Field)fse.Member));
    }

    void AddWellformednessCheck(ConstantField decl) {
      Contract.Requires(decl != null);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(currentModule == null && codeContext == null && IsAllocContext == null && fuelContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && IsAllocContext == null && fuelContext == null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(decl.FullDafnyName, MethodTranslationKind.SpecWellformedness), null);
      if (!InVerificationScope(decl)) {
        // Checked in other file
        return;
      }

      // If there's no RHS, there's nothing to do
      if (decl.Rhs == null) {
        return;
      }

      currentModule = decl.EnclosingModule;
      codeContext = decl;
      fuelContext = FuelSetting.NewFuelContext(decl);
      var etran = new ExpressionTranslator(this, Predef, decl.Origin, null);

      // parameters of the procedure
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(decl.EnclosingClass), true);
      if (!decl.IsStatic) {
        var receiverType = ModuleResolver.GetThisType(decl.Origin, (TopLevelDeclWithMembers)decl.EnclosingClass);
        Contract.Assert(VisibleInScope(receiverType));

        var th = new Bpl.IdentifierExpr(decl.Origin, "this", TrReceiverType(decl));
        var wh = BplAnd(
          ReceiverNotNull(th),
          etran.GoodRef(decl.Origin, th, receiverType));
        // for class constructors, the receiver is encoded as an output parameter
        var thVar = new Bpl.Formal(decl.Origin, new Bpl.TypedIdent(decl.Origin, "this", TrReceiverType(decl), wh), true);
        inParams.Add(thVar);
      }

      // the procedure itself
      var req = new List<Bpl.Requires>();
      foreach (var typeBoundAxiom in TypeBoundAxioms(decl.Origin, decl.EnclosingClass.TypeArgs)) {
        req.Add(FreeRequires(decl.Origin, typeBoundAxiom, null));
      }

      var heapVar = new Bpl.IdentifierExpr(decl.Origin, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar };
      var name = MethodName(decl, MethodTranslationKind.SpecWellformedness);
      var proc = new Bpl.Procedure(decl.Origin, name, [],
        inParams, [],
        false, req, varlist, [], etran.TrAttributes(decl.Attributes, null));
      AddVerboseNameAttribute(proc, decl.FullDafnyName, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new Variables();
      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(false));
      builder.Add(new CommentCmd($"AddWellformednessCheck for {decl.WhatKind} {decl}"));
      builder.AddCaptureState(decl.Origin, false, "initial state");
      IsAllocContext = new IsAllocContext(options, true);

      DefineFrame(decl.Origin, etran.ReadsFrame(decl.Origin), [], builder, locals, null);

      // check well-formedness of the RHS expression
      CheckWellformed(decl.Rhs, new WFOptions(null, true), locals, builder, etran);
      builder.Add(new Bpl.AssumeCmd(decl.Rhs.Origin, etran.CanCallAssumption(decl.Rhs)));
      CheckSubrange(decl.Rhs.Origin, etran.TrExpr(decl.Rhs), decl.Rhs.Type, decl.Type, decl.Rhs, builder);

      if (EmitImplementation(decl.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(decl.Attributes, null);
        var implBody = builder.Collect(decl.Origin);

        AddImplementationWithAttributes(GetToken(decl), proc, implInParams,
          [], locals, implBody, kv);
      }

      Contract.Assert(currentModule == decl.EnclosingModule);
      Contract.Assert(codeContext == decl);
      IsAllocContext = null;
      fuelContext = null;
      Reset();
    }
  }
}
