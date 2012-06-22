//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Translator {
    [NotDelayed]
    public Translator() {
      Bpl.Program boogieProgram = ReadPrelude();
      if (boogieProgram != null) {
        sink = boogieProgram;
        predef = FindPredefinedDecls(boogieProgram);
      }
    }

    // translation state
    readonly Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>/*!*/ classes = new Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/,Bpl.Constant/*!*/>/*!*/ fields = new Dictionary<Field/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/, Bpl.Function/*!*/>/*!*/ fieldFunctions = new Dictionary<Field/*!*/, Bpl.Function/*!*/>();

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(classes));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fields));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fieldFunctions));
      Contract.Invariant(currentMethod == null || currentMethod.EnclosingClass.Module == currentModule);
    }

    readonly Bpl.Program sink;
    readonly PredefinedDecls predef;

    internal class PredefinedDecls {
      public readonly Bpl.Type RefType;
      public readonly Bpl.Type BoxType;
      public readonly Bpl.Type TickType;
      private readonly Bpl.TypeSynonymDecl setTypeCtor;
      private readonly Bpl.TypeSynonymDecl multiSetTypeCtor;
      private readonly Bpl.TypeCtorDecl mapTypeCtor;
      public readonly Bpl.Function ArrayLength;
      private readonly Bpl.TypeCtorDecl seqTypeCtor;
      readonly Bpl.TypeCtorDecl fieldName;
      public readonly Bpl.Type HeapType;
      public readonly string HeapVarName;
      public readonly Bpl.Type ClassNameType;
      public readonly Bpl.Type DatatypeType;
      public readonly Bpl.Type DtCtorId;
      public readonly Bpl.Expr Null;
      private readonly Bpl.Constant allocField;
      public readonly Bpl.Constant ClassDotArray;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(RefType != null);
        Contract.Invariant(BoxType != null);
        Contract.Invariant(TickType != null);
        Contract.Invariant(setTypeCtor != null);
        Contract.Invariant(multiSetTypeCtor != null);
        Contract.Invariant(ArrayLength != null);
        Contract.Invariant(seqTypeCtor != null);
        Contract.Invariant(fieldName != null);
        Contract.Invariant(HeapType != null);
        Contract.Invariant(HeapVarName != null);
        Contract.Invariant(ClassNameType != null);
        Contract.Invariant(DatatypeType != null);
        Contract.Invariant(DtCtorId != null);
        Contract.Invariant(Null != null);
        Contract.Invariant(allocField != null);
        Contract.Invariant(ClassDotArray != null);
      }


      public Bpl.Type SetType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, setTypeCtor, new Bpl.TypeSeq(ty));
      }

      public Bpl.Type MultiSetType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, multiSetTypeCtor, new Bpl.TypeSeq(ty));
      }
      public Bpl.Type MapType(IToken tok, Bpl.Type tya, Bpl.Type tyb) {
        Contract.Requires(tok != null);
        Contract.Requires(tya != null && tyb != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(Token.NoToken, mapTypeCtor, new Bpl.TypeSeq(tya, tyb));
      }

      public Bpl.Type SeqType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);
        return new Bpl.CtorType(Token.NoToken, seqTypeCtor, new Bpl.TypeSeq(ty));
      }

      public Bpl.Type FieldName(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(tok, fieldName, new Bpl.TypeSeq(ty));
      }

      public Bpl.IdentifierExpr Alloc(IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

        return new Bpl.IdentifierExpr(tok, allocField);
      }

      public PredefinedDecls(Bpl.TypeCtorDecl refType, Bpl.TypeCtorDecl boxType, Bpl.TypeCtorDecl tickType,
                             Bpl.TypeSynonymDecl setTypeCtor, Bpl.TypeSynonymDecl multiSetTypeCtor, Bpl.TypeCtorDecl mapTypeCtor, Bpl.Function arrayLength, Bpl.TypeCtorDecl seqTypeCtor, Bpl.TypeCtorDecl fieldNameType,
                             Bpl.GlobalVariable heap, Bpl.TypeCtorDecl classNameType,
                             Bpl.TypeCtorDecl datatypeType, Bpl.TypeCtorDecl dtCtorId,
                             Bpl.Constant allocField, Bpl.Constant classDotArray) {
        #region Non-null preconditions on parameters
        Contract.Requires(refType != null);
        Contract.Requires(boxType != null);
        Contract.Requires(tickType != null);
        Contract.Requires(setTypeCtor != null);
        Contract.Requires(multiSetTypeCtor != null);
        Contract.Requires(seqTypeCtor != null);
        Contract.Requires(fieldNameType != null);
        Contract.Requires(heap != null);
        Contract.Requires(classNameType != null);
        Contract.Requires(datatypeType != null);
        Contract.Requires(dtCtorId != null);
        Contract.Requires(allocField != null);
        Contract.Requires(classDotArray != null);
        #endregion

        Bpl.CtorType refT = new Bpl.CtorType(Token.NoToken, refType, new Bpl.TypeSeq());
        this.RefType = refT;
        this.BoxType = new Bpl.CtorType(Token.NoToken, boxType, new Bpl.TypeSeq());
        this.TickType = new Bpl.CtorType(Token.NoToken, tickType, new Bpl.TypeSeq());
        this.setTypeCtor = setTypeCtor;
        this.multiSetTypeCtor = multiSetTypeCtor;
        this.mapTypeCtor = mapTypeCtor;
        this.ArrayLength = arrayLength;
        this.seqTypeCtor = seqTypeCtor;
        this.fieldName = fieldNameType;
        this.HeapType = heap.TypedIdent.Type;
        this.HeapVarName = heap.Name;
        this.ClassNameType = new Bpl.CtorType(Token.NoToken, classNameType, new Bpl.TypeSeq());
        this.DatatypeType = new Bpl.CtorType(Token.NoToken, datatypeType, new Bpl.TypeSeq());
        this.DtCtorId = new Bpl.CtorType(Token.NoToken, dtCtorId, new Bpl.TypeSeq());
        this.allocField = allocField;
        this.Null = new Bpl.IdentifierExpr(Token.NoToken, "null", refT);
        this.ClassDotArray = classDotArray;
      }
    }

    static PredefinedDecls FindPredefinedDecls(Bpl.Program prog) {
      Contract.Requires(prog != null);
      if (prog.Resolve() != 0) {
        Console.WriteLine("Error: resolution errors encountered in Dafny prelude");
        return null;
      }

      Bpl.TypeCtorDecl refType = null;
      Bpl.TypeSynonymDecl setTypeCtor = null;
      Bpl.TypeSynonymDecl multiSetTypeCtor = null;
      Bpl.Function arrayLength = null;
      Bpl.TypeCtorDecl seqTypeCtor = null;
      Bpl.TypeCtorDecl fieldNameType = null;
      Bpl.TypeCtorDecl classNameType = null;
      Bpl.TypeCtorDecl datatypeType = null;
      Bpl.TypeCtorDecl dtCtorId = null;
      Bpl.TypeCtorDecl boxType = null;
      Bpl.TypeCtorDecl tickType = null;
      Bpl.TypeCtorDecl mapTypeCtor = null;
      Bpl.GlobalVariable heap = null;
      Bpl.Constant allocField = null;
      Bpl.Constant classDotArray = null;
      foreach (var d in prog.TopLevelDeclarations) {
        if (d is Bpl.TypeCtorDecl) {
          Bpl.TypeCtorDecl dt = (Bpl.TypeCtorDecl)d;
          if (dt.Name == "Seq") {
            seqTypeCtor = dt;
          } else if (dt.Name == "Field") {
            fieldNameType = dt;
          } else if (dt.Name == "ClassName") {
            classNameType = dt;
          } else if (dt.Name == "DatatypeType") {
            datatypeType = dt;
          } else if (dt.Name == "DtCtorId") {
            dtCtorId = dt;
          } else if (dt.Name == "ref") {
            refType = dt;
          } else if (dt.Name == "BoxType") {
            boxType = dt;
          } else if (dt.Name == "TickType") {
            tickType = dt;
          } else if (dt.Name == "Map") {
            mapTypeCtor = dt;
          }
        } else if (d is Bpl.TypeSynonymDecl) {
          Bpl.TypeSynonymDecl dt = (Bpl.TypeSynonymDecl)d;
          if (dt.Name == "Set") {
            setTypeCtor = dt;
          }
          if (dt.Name == "MultiSet") {
            multiSetTypeCtor = dt;
          }
        } else if (d is Bpl.Constant) {
          Bpl.Constant c = (Bpl.Constant)d;
          if (c.Name == "alloc") {
            allocField = c;
          } else if (c.Name == "class._System.array") {
            classDotArray = c;
          }
        } else if (d is Bpl.GlobalVariable) {
          Bpl.GlobalVariable v = (Bpl.GlobalVariable)d;
          if (v.Name == "$Heap") {
            heap = v;
          }
        } else if (d is Bpl.Function) {
          var f = (Bpl.Function)d;
          if (f.Name == "_System.array.Length")
            arrayLength = f;
        }
      }
      if (seqTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Seq");
      } else if (setTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Set");
      } else if (multiSetTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type MultiSet");
      } else if (mapTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Map");
      } else if (arrayLength == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.array.Length");
      } else if (fieldNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Field");
      } else if (classNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ClassName");
      } else if (datatypeType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type DatatypeType");
      } else if (dtCtorId == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type DtCtorId");
      } else if (refType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ref");
      } else if (boxType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type BoxType");
      } else if (tickType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type TickType");
      } else if (heap == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of $Heap");
      } else if (allocField == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of constant alloc");
      } else if (classDotArray == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of class._System.array");
      } else {
        return new PredefinedDecls(refType, boxType, tickType,
                                   setTypeCtor, multiSetTypeCtor, mapTypeCtor, arrayLength, seqTypeCtor, fieldNameType, heap, classNameType, datatypeType, dtCtorId,
                                   allocField, classDotArray);
      }
      return null;
    }

    static Bpl.Program ReadPrelude() {
      string preludePath = DafnyOptions.O.DafnyPrelude;
      if (preludePath == null)
      {
          //using (System.IO.Stream stream = cce.NonNull( System.Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream("DafnyPrelude.bpl")) // Use this once Spec#/VSIP supports designating a non-.resx project item as an embedded resource
          string codebase = cce.NonNull(System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
          preludePath = System.IO.Path.Combine(codebase, "DafnyPrelude.bpl");
      }

      Bpl.Program prelude;
      int errorCount = Bpl.Parser.Parse(preludePath, (List<string>)null, out prelude);
      if (prelude == null || errorCount > 0) {
        return null;
      } else {
        return prelude;
      }
/*
      List<string!> defines = new List<string!>();
      using (System.IO.Stream stream = new System.IO.FileStream(preludePath, System.IO.FileMode.Open, System.IO.FileAccess.Read))
      {
        BoogiePL.Buffer.Fill(new System.IO.StreamReader(stream), defines);
        //BoogiePL.Scanner.Init("<DafnyPrelude.bpl>");
        Bpl.Program prelude;
        int errorCount = BoogiePL.Parser.Parse(out prelude);
        if (prelude == null || errorCount > 0) {
          return null;
        } else {
          return prelude;
        }
      }
*/
    }

    public Bpl.Program Translate(Program program) {
      Contract.Requires(program != null);
      Contract.Ensures(Contract.Result<Bpl.Program>() != null);

      if (sink == null || predef == null) {
        // something went wrong during construction, which reads the prelude; an error has
        // already been printed, so just return an empty program here (which is non-null)
        return new Bpl.Program();
      }

      foreach (TopLevelDecl d in program.BuiltIns.SystemModule.TopLevelDecls) {
        if (d is ArbitraryTypeDecl) {
          // nothing to do--this is treated just like a type parameter
        } else if (d is DatatypeDecl) {
          AddDatatype((DatatypeDecl)d);
        } else {
          AddClassMembers((ClassDecl)d);
        }
      }
      foreach (ModuleDecl m in program.Modules) {
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          if (d is ArbitraryTypeDecl) {
            // nothing to do--this is treated just like a type parameter
          } else if (d is DatatypeDecl) {
            AddDatatype((DatatypeDecl)d);
          } else {
            AddClassMembers((ClassDecl)d);
          }
        }
      }
      return sink;
    }

    void AddDatatype(DatatypeDecl dt)
    {
      Contract.Requires(dt != null);
      Contract.Requires(sink != null && predef != null);
      sink.TopLevelDeclarations.Add(GetClass(dt));

      foreach (DatatypeCtor ctor in dt.Ctors) {
        // Add:  function #dt.ctor(paramTypes) returns (DatatypeType);
        Bpl.VariableSeq argTypes = new Bpl.VariableSeq();
        foreach (Formal arg in ctor.Formals) {
          Bpl.Variable a = new Bpl.Formal(arg.tok, new Bpl.TypedIdent(arg.tok, Bpl.TypedIdent.NoName, TrType(arg.Type)), true);
          argTypes.Add(a);
        }
        Bpl.Variable resType = new Bpl.Formal(ctor.tok, new Bpl.TypedIdent(ctor.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), false);
        Bpl.Function fn = new Bpl.Function(ctor.tok, ctor.FullName, argTypes, resType);
        sink.TopLevelDeclarations.Add(fn);

        // Add:  axiom (forall params :: #dt.ctor(params)-has-the-expected-type);
        Bpl.VariableSeq bvs;
        List<Bpl.Expr> args;
        CreateBoundVariables(ctor.Formals, out bvs, out args);
        Bpl.Expr ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
        List<Type> tpArgs = new List<Type>();  // we use an empty list of type arguments, because we don't want Good_Datatype to produce any DtTypeParams predicates anyway
        Bpl.Expr wh = new ExpressionTranslator(this, predef, ctor.tok).Good_Datatype(ctor.tok, ct, dt, tpArgs);
        if (bvs.Length != 0) {
          wh = new Bpl.ForallExpr(ctor.tok, bvs, wh);
        }
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, wh));

        // Add:  const unique ##dt.ctor: DtCtorId;
        Bpl.Constant cid = new Bpl.Constant(ctor.tok, new Bpl.TypedIdent(ctor.tok, "#" + ctor.FullName, predef.DtCtorId), true);
        sink.TopLevelDeclarations.Add(cid);

        // Add:  axiom (forall params :: DatatypeCtorId(#dt.ctor(params)) == ##dt.ctor);
        CreateBoundVariables(ctor.Formals, out bvs, out args);
        Bpl.Expr lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
        lhs = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, lhs);
        Bpl.Expr q = Bpl.Expr.Eq(lhs, new Bpl.IdentifierExpr(ctor.tok, cid));
        if (bvs.Length != 0) {
          q = new Bpl.ForallExpr(ctor.tok, bvs, q);
        }
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
        // Add:  axiom (forall d: DatatypeType :: dt.ctor?(d) ==> (exists params :: d == #dt.ctor(params));
        CreateBoundVariables(ctor.Formals, out bvs, out args);
        lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
        var dBv = new Bpl.BoundVariable(ctor.tok, new Bpl.TypedIdent(ctor.tok, "d", predef.DatatypeType));
        var dId = new Bpl.IdentifierExpr(ctor.tok, dBv.Name, predef.DatatypeType);
        q = Bpl.Expr.Eq(dId, lhs);
        if (bvs.Length != 0) {
          q = new Bpl.ExistsExpr(ctor.tok, bvs, q);
        }
        q = Bpl.Expr.Imp(FunctionCall(ctor.tok, ctor.QueryField.FullName, Bpl.Type.Bool, dId), q);
        q = new Bpl.ForallExpr(ctor.tok, new VariableSeq(dBv), q);
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));

        // Add:  function dt.ctor?(this: DatatypeType): bool { DatatypeCtorId(this) == ##dt.ctor }
        fn = GetReadonlyField(ctor.QueryField);
        lhs = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, new Bpl.IdentifierExpr(ctor.tok, fn.InParams[0].Name, predef.DatatypeType));
        fn.Body = Bpl.Expr.Eq(lhs, new Bpl.IdentifierExpr(ctor.tok, cid));  // this uses the "cid" defined for the previous axiom
        sink.TopLevelDeclarations.Add(fn);

        // Add:  axiom (forall params, h: HeapType ::
        //                 { DtAlloc(#dt.ctor(params), h) }
        //                 $IsGoodHeap(h) ==>
        //                     (DtAlloc(#dt.ctor(params), h) <==> ...each param has its expected type...));
        CreateBoundVariables(ctor.Formals, out bvs, out args);
        lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
        Bpl.BoundVariable hVar = new Bpl.BoundVariable(ctor.tok, new Bpl.TypedIdent(ctor.tok, "$h", predef.HeapType));
        Bpl.Expr h = new Bpl.IdentifierExpr(ctor.tok, hVar);
        bvs.Add(hVar); args.Add(h);
        ExpressionTranslator etranH = new ExpressionTranslator(this, predef, h);
        Bpl.Expr isGoodHeap = FunctionCall(ctor.tok, BuiltinFunction.IsGoodHeap, null, h);
        lhs = FunctionCall(ctor.tok, BuiltinFunction.DtAlloc, null, lhs, h);
        Bpl.Expr pt = Bpl.Expr.True;
        int i = 0;
        foreach (Formal arg in ctor.Formals) {
          Bpl.Expr whp = GetWhereClause(arg.tok, args[i], arg.Type, etranH);
          if (whp != null) {
            pt = BplAnd(pt, whp);
          }
          i++;
        }
        Bpl.Trigger tr = new Bpl.Trigger(ctor.tok, true, new ExprSeq(lhs));
        q = new Bpl.ForallExpr(ctor.tok, bvs, tr, Bpl.Expr.Imp(isGoodHeap, Bpl.Expr.Iff(lhs, pt)));
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));

        // Add injectivity axioms:
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          // function ##dt.ctor#i(DatatypeType) returns (Ti);
          var sf = ctor.Destructors[i];
          if (sf != null) {
            fn = GetReadonlyField(sf);
          } else {
            Contract.Assert(!arg.HasName);
            argTypes = new Bpl.VariableSeq();
            argTypes.Add(new Bpl.Formal(ctor.tok, new Bpl.TypedIdent(ctor.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), true));
            resType = new Bpl.Formal(arg.tok, new Bpl.TypedIdent(arg.tok, Bpl.TypedIdent.NoName, TrType(arg.Type)), false);
            string nm = "#" + ctor.FullName + "#" + i;
            fn = new Bpl.Function(ctor.tok, nm, argTypes, resType);
          }
          sink.TopLevelDeclarations.Add(fn);
          // axiom (forall params :: ##dt.ctor#i(#dt.ctor(params)) == params_i);
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          lhs = FunctionCall(ctor.tok, fn.Name, TrType(arg.Type), lhs);
          q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Eq(lhs, args[i]));
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));

          if (dt is IndDatatypeDecl) {
            if (arg.Type.IsDatatype || arg.Type.IsTypeParameter) {
              // for datatype:             axiom (forall params :: DtRank(params_i) < DtRank(#dt.ctor(params)));
              // for type-parameter type:  axiom (forall params :: DtRank(Unbox(params_i)) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                arg.Type.IsDatatype ? args[i] : FunctionCall(ctor.tok, BuiltinFunction.Unbox, predef.DatatypeType, args[i]));
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Lt(lhs, rhs));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
            } else if (arg.Type is SeqType) {
              // axiom (forall params, i: int :: 0 <= i && i < |arg| ==> DtRank(arg[i]) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, i: int :: 0 <= i && i < |arg| ==> DtRank(Unbox(Seq#Index(arg,i))) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable iVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "i", Bpl.Type.Int));
              bvs.Add(iVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, iVar);
              Bpl.Expr ante = Bpl.Expr.And(
                Bpl.Expr.Le(Bpl.Expr.Literal(0), ie),
                Bpl.Expr.Lt(ie, FunctionCall(arg.tok, BuiltinFunction.SeqLength, null, args[i])));
              lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                FunctionCall(arg.tok, BuiltinFunction.Unbox, predef.DatatypeType,
                  FunctionCall(arg.tok, BuiltinFunction.SeqIndex, predef.DatatypeType, args[i], ie)));
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
            } else if (arg.Type is SetType) {
              // axiom (forall params, d: Datatype :: arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype :: arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              Bpl.Expr ante = Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie));
              lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
            } else if (arg.Type is MultiSetType) {
              // axiom (forall params, d: Datatype :: 0 < arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype :: 0 < arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              Bpl.Expr ante = Bpl.Expr.Gt(Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie)), Bpl.Expr.Literal(0));
              lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
            }
          }
          i++;
        }
      }

      // Add:
      //   function $IsA#Dt(d: DatatypeType): bool {
      //     Dt.Ctor0?(d) || Dt.Ctor1?(d) || ...
      //   }
      var cases_dBv = new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, "d", predef.DatatypeType), true);
      var cases_dId = new Bpl.IdentifierExpr(dt.tok, cases_dBv.Name, predef.DatatypeType);
      Bpl.Expr cases_body = null;
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var disj = FunctionCall(ctor.tok, ctor.QueryField.FullName, Bpl.Type.Bool, cases_dId);
        cases_body = cases_body == null ? disj : Bpl.Expr.Or(cases_body, disj);
      }
      var cases_resType = new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
      var cases_fn = new Bpl.Function(dt.tok, "$IsA#" + dt.FullName, new Bpl.VariableSeq(cases_dBv), cases_resType);
      cases_fn.Body = cases_body;
      sink.TopLevelDeclarations.Add(cases_fn);
    }

    void CreateBoundVariables(List<Formal/*!*/>/*!*/ formals, out Bpl.VariableSeq/*!*/ bvs, out List<Bpl.Expr/*!*/>/*!*/ args)
    {
      Contract.Requires(formals != null);
      Contract.Ensures(Contract.ValueAtReturn(out bvs).Length == Contract.ValueAtReturn(out args).Count);
      Contract.Ensures(Contract.ValueAtReturn(out bvs) != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out args)));

      bvs = new Bpl.VariableSeq();
      args = new List<Bpl.Expr>();
      foreach (Formal arg in formals) {
        Contract.Assert(arg != null);
        var nm = string.Format("a{0}#{1}", bvs.Length, otherTmpVarCount);
        otherTmpVarCount++;
        Bpl.Variable bv = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, nm, TrType(arg.Type)));
        bvs.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.tok, bv));
      }
    }

    void AddClassMembers(ClassDecl c)
    {
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(c != null);
      if (c.Name == "array") {
        classes.Add(c, predef.ClassDotArray);
      } else {
        sink.TopLevelDeclarations.Add(GetClass(c));
      }

      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          Field f = (Field)member;
          if (f.IsMutable) {
            Bpl.Constant fc = GetField(f);
            sink.TopLevelDeclarations.Add(fc);
          } else {
            Bpl.Function ff = GetReadonlyField(f);
            if (ff != predef.ArrayLength)
              sink.TopLevelDeclarations.Add(ff);
          }

          AddAllocationAxiom(f);

        } else if (member is Function) {
          Function f = (Function)member;
          AddFunction(f);
          if (f.IsRecursive) {
            AddLimitedAxioms(f, 2);
            AddLimitedAxioms(f, 1);
          }
          for (int layerOffset = 0; layerOffset < 2; layerOffset++) {
            var body = f.Body == null ? null : f.Body.Resolved;
            if (body is MatchExpr) {
              AddFunctionAxiomCase(f, (MatchExpr)body, null, layerOffset);
              AddFunctionAxiom(f, null, f.Ens, null, layerOffset);
            } else {
              AddFunctionAxiom(f, body, f.Ens, null, layerOffset);
            }
            if (!f.IsRecursive) { break; }
          }
          AddFrameAxiom(f);
          AddWellformednessCheck(f);

        } else if (member is Method) {
          Method m = (Method)member;
          bool isRefinementMethod = RefinementToken.IsInherited(m.tok, m.EnclosingClass.Module);

          // wellformedness check for method specification
          Bpl.Procedure proc = AddMethod(m, 0, isRefinementMethod);
          sink.TopLevelDeclarations.Add(proc);
          AddMethodImpl(m, proc, true);
          // the method itself
          proc = AddMethod(m, 1, isRefinementMethod);
          sink.TopLevelDeclarations.Add(proc);
          if (isRefinementMethod) {
            proc = AddMethod(m, 2, isRefinementMethod);
            sink.TopLevelDeclarations.Add(proc);
            proc = AddMethod(m, 3, isRefinementMethod);
            sink.TopLevelDeclarations.Add(proc);
          }
          if (m.Body != null) {
            // ...and its implementation
            AddMethodImpl(m, proc, false);
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    void AddFunctionAxiomCase(Function f, MatchExpr me, Specialization prev, int layerOffset) {
      Contract.Requires(f != null);
      Contract.Requires(me != null);
      Contract.Requires(layerOffset == 0 || layerOffset == 1);

      IVariable formal = ((IdentifierExpr)me.Source.Resolved).Var;  // correctness of casts follows from what resolution checks
      foreach (MatchCaseExpr mc in me.Cases) {
        Contract.Assert(mc.Ctor != null);  // the field is filled in by resolution
        Specialization s = new Specialization(formal, mc, prev);
        var body = mc.Body.Resolved;
        if (body is MatchExpr) {
          AddFunctionAxiomCase(f, (MatchExpr)body, s, layerOffset);
        } else {
          AddFunctionAxiom(f, body, new List<Expression>(), s, layerOffset);
        }
      }
    }

    class Specialization
    {
      public readonly List<Formal/*!*/> Formals;
      public readonly List<Expression/*!*/> ReplacementExprs;
      public readonly List<BoundVar/*!*/> ReplacementFormals;
      public readonly Dictionary<IVariable, Expression> SubstMap;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(Formals));
        Contract.Invariant(cce.NonNullElements(ReplacementExprs));
        Contract.Invariant(Formals.Count == ReplacementExprs.Count);
        Contract.Invariant(cce.NonNullElements(ReplacementFormals));
        Contract.Invariant(SubstMap != null);
      }

      public Specialization(IVariable formal, MatchCase mc, Specialization prev) {
        Contract.Requires(formal is Formal || formal is BoundVar);
        Contract.Requires(mc != null);
        Contract.Requires(prev == null || formal is BoundVar || !prev.Formals.Contains((Formal)formal));

        List<Expression> rArgs = new List<Expression>();
        foreach (BoundVar p in mc.Arguments) {
          IdentifierExpr ie = new IdentifierExpr(p.tok, p.UniqueName);
          ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
          rArgs.Add(ie);
        }
        // create and resolve datatype value
        var r = new DatatypeValue(mc.tok, mc.Ctor.EnclosingDatatype.Name, mc.Ctor.Name, rArgs);
        r.Ctor = mc.Ctor;
        r.Type = new UserDefinedType(mc.tok, mc.Ctor.EnclosingDatatype.Name, new List<Type>()/*this is not right, but it seems like it won't matter here*/, null);

        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(formal, r);

        // Fill in the fields
        Formals = new List<Formal>();
        ReplacementExprs = new List<Expression>();
        ReplacementFormals = new List<BoundVar>();
        SubstMap = new Dictionary<IVariable, Expression>();
        if (prev != null) {
          Formals.AddRange(prev.Formals);
          foreach (var e in prev.ReplacementExprs) {
            ReplacementExprs.Add(Substitute(e, null, substMap));
          }
          foreach (var rf in prev.ReplacementFormals) {
            if (rf != formal) {
              ReplacementFormals.Add(rf);
            }
          }
          foreach (var entry in prev.SubstMap) {
            SubstMap.Add(entry.Key, Substitute(entry.Value, null, substMap));
          }
        }
        if (formal is Formal) {
          Formals.Add((Formal)formal);
          ReplacementExprs.Add(r);
        }
        ReplacementFormals.AddRange(mc.Arguments);
        SubstMap.Add(formal, r);
      }
    }

    void AddFunctionAxiom(Function/*!*/ f, Expression body, List<Expression/*!*/>/*!*/ ens, Specialization specialization, int layerOffset) {
      if (f is Predicate) {
        var ax = FunctionAxiom(f, FunctionAxiomVisibility.IntraModuleOnly, body, ens, specialization, layerOffset);
        sink.TopLevelDeclarations.Add(ax);
        ax = FunctionAxiom(f, FunctionAxiomVisibility.ForeignModuleOnly, body, ens, specialization, layerOffset);
        sink.TopLevelDeclarations.Add(ax);
      } else {
        var ax = FunctionAxiom(f, FunctionAxiomVisibility.All, body, ens, specialization, layerOffset);
        sink.TopLevelDeclarations.Add(ax);
      }
    }

    enum FunctionAxiomVisibility { All, IntraModuleOnly, ForeignModuleOnly }

    Bpl.Axiom/*!*/ FunctionAxiom(Function/*!*/ f, FunctionAxiomVisibility visibility, Expression body, List<Expression/*!*/>/*!*/ ens, Specialization specialization, int layerOffset) {
      Contract.Requires(f != null);
      Contract.Requires(ens != null);
      Contract.Requires(layerOffset == 0 || (layerOffset == 1 && f.IsRecursive));
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);

      // axiom
      //   mh < ModuleContextHeight ||                                                                    // (a)
      //   (mh == ModuleContextHeight && (fh <= FunctionContextHeight || InMethodContext))                // (b)
      //   ==>
      //   (forall $Heap, formals ::
      //       { f(args) }
      //       f#canCall(args) ||
      //       ( (mh != ModuleContextHeight || fh != FunctionContextHeight || InMethodContext) &&         // (c)
      //         $IsHeap($Heap) && this != null && formals-have-the-expected-types &&
      //         Pre($Heap,args))
      //       ==>
      //       body-can-make-its-calls &&                         // generated only for layerOffset==0
      //       f(args) == body &&                                                                         // (d)
      //       ens &&                                             // generated only for layerOffset==0
      //       f(args)-has-the-expected-type);                    // generated only for layerOffset==0
      //
      // The variables "formals" are the formals of function "f"; except, if a specialization is provided, then
      // "specialization.Formals" (which are expected to be among the formals of "f") are excluded and replaced by
      // "specialization.ReplacementFormals".
      // The list "args" is the list of formals of function "f"; except, if a specialization is provided, then
      // each of the "specialization.Formals" is replaced by the corresponding expression in "specialization.ReplacementExprs".
      // If a specialization is provided, occurrences of "specialization.Formals" in "body", "f.Req", and "f.Ens"
      // are also replaced by those corresponding expressions.
      //
      // The translation of "body" uses the #limited form whenever the callee is in the same SCC of the call graph.
      //
      // if layerOffset==1, then the names f#2 and f are used instead of f and f#limited.
      //
      // Visibility:  The above description is for visibility==All.  If visibility==IntraModuleOnly, then
      // disjunct (a) is dropped (which also has a simplifying effect on (c)).  Finally, if visibility==ForeignModuleOnly,
      // then disjunct (b) is dropped (which also has a simplify effect on(c)); furthermore, if f is a Predicate,
      // then the equality in (d) is replaced by an implication.
      //
      // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
      // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
      // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
      // sound after that, then it would also have been sound just before the allocation.
      //
      Bpl.VariableSeq formals = new Bpl.VariableSeq();
      Bpl.ExprSeq args = new Bpl.ExprSeq();
      Bpl.BoundVariable bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      formals.Add(bv);
      args.Add(new Bpl.IdentifierExpr(f.tok, bv));
      // ante:  $IsHeap($Heap) && this != null && formals-have-the-expected-types &&
      Bpl.Expr ante = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);

      Bpl.BoundVariable bvThis;
      Bpl.Expr bvThisIdExpr;
      if (f.IsStatic) {
        bvThis = null;
        bvThisIdExpr = null;
      } else {
        bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, predef.RefType));
        formals.Add(bvThis);
        bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        args.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(bvThisIdExpr, predef.Null),
          etran.GoodRef(f.tok, bvThisIdExpr, thisType));
        ante = Bpl.Expr.And(ante, wh);
      }
      if (specialization != null) {
        foreach (BoundVar p in specialization.ReplacementFormals) {
          bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)));
          formals.Add(bv);
          // add well-typedness conjunct to antecedent
          Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, bv), p.Type, etran);
          if (wh != null) { ante = Bpl.Expr.And(ante, wh); }
        }
      }
      foreach (Formal p in f.Formals) {
        int i = specialization == null ? -1 : specialization.Formals.FindIndex(val => val == p);
        if (i == -1) {
          bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)));
          formals.Add(bv);
          Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
          args.Add(formal);
          // add well-typedness conjunct to antecedent
          Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran);
          if (wh != null) { ante = Bpl.Expr.And(ante, wh); }
        } else {
          args.Add(etran.TrExpr(specialization.ReplacementExprs[i]));
          // note, well-typedness conjuncts for the replacement formals has already been done above
        }
      }

      // mh < ModuleContextHeight || (mh == ModuleContextHeight && (fh <= FunctionContextHeight || InMethodContext))
      ModuleDecl mod = f.EnclosingClass.Module;
      var activateForeign = Bpl.Expr.Lt(Bpl.Expr.Literal(mod.Height), etran.ModuleContextHeight());
      var activateIntra = 
        Bpl.Expr.And(
          Bpl.Expr.Eq(Bpl.Expr.Literal(mod.Height), etran.ModuleContextHeight()),
          Bpl.Expr.Or(
            Bpl.Expr.Le(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight()),
            etran.InMethodContext()));
      Bpl.Expr activate =
        visibility == FunctionAxiomVisibility.All ? Bpl.Expr.Or(activateForeign, activateIntra) :
        visibility == FunctionAxiomVisibility.IntraModuleOnly ? activateIntra : activateForeign;

      var substMap = new Dictionary<IVariable, Expression>();
      if (specialization != null) {
        substMap = specialization.SubstMap;
      }
      Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, FunctionName(f, 1+layerOffset), TrType(f.ResultType));
      Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), args);

      Bpl.Expr pre = Bpl.Expr.True;
      foreach (Expression req in f.Req) {
        pre = BplAnd(pre, etran.TrExpr(Substitute(req, null, substMap)));
      }
      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight || InMethodContext)
      Bpl.Expr useViaContext = visibility == FunctionAxiomVisibility.ForeignModuleOnly ? Bpl.Expr.True :
        Bpl.Expr.Or(Bpl.Expr.Or(
          visibility == FunctionAxiomVisibility.IntraModuleOnly ?
            (Bpl.Expr)Bpl.Expr.False :
            Bpl.Expr.Neq(Bpl.Expr.Literal(mod.Height), etran.ModuleContextHeight()),
          Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight())),
          etran.InMethodContext());
      // useViaCanCall: f#canCall(args)
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), args);

      // ante := useViaCanCall || (useViaContext && typeAnte && pre)
      ante = Bpl.Expr.Or(useViaCanCall, BplAnd(useViaContext, BplAnd(ante, pre)));

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new Bpl.ExprSeq(funcAppl));
      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(f.TypeArgs);
      Bpl.Expr meat;
      if (body == null) {
        meat = Bpl.Expr.True;
      } else {
        Expression bodyWithSubst = Substitute(body, null, substMap);
        if (layerOffset == 0) {
          meat = Bpl.Expr.And(
            CanCallAssumption(bodyWithSubst, etran),
            visibility == FunctionAxiomVisibility.ForeignModuleOnly && f is Predicate ?
              Bpl.Expr.Imp(funcAppl, etran.LimitedFunctions(f).TrExpr(bodyWithSubst)) :
              Bpl.Expr.Eq(funcAppl, etran.LimitedFunctions(f).TrExpr(bodyWithSubst)));
        } else {
          meat = visibility == FunctionAxiomVisibility.ForeignModuleOnly && f is Predicate ?
            Bpl.Expr.Imp(funcAppl, etran.TrExpr(bodyWithSubst)) :
            Bpl.Expr.Eq(funcAppl, etran.TrExpr(bodyWithSubst));
        }
      }
      if (layerOffset == 0) {
        foreach (Expression p in ens) {
          Bpl.Expr q = etran.LimitedFunctions(f).TrExpr(Substitute(p, null, substMap));
          meat = BplAnd(meat, q);
        }
        Bpl.Expr whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etran);
        if (whr != null) { meat = Bpl.Expr.And(meat, whr); }
      }
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, null, tr, Bpl.Expr.Imp(ante, meat));
      string comment = "definition axiom for " + FunctionName(f, 1+layerOffset);
      if (visibility == FunctionAxiomVisibility.IntraModuleOnly) {
        comment += " (intra-module)";
      } else if (visibility == FunctionAxiomVisibility.ForeignModuleOnly) {
        comment += " (foreign modules)";
      }
      if (specialization != null) {
        string sep = "{0}, specialized for '{1}'";
        foreach (var formal in specialization.Formals) {
          comment = string.Format(sep, comment, formal.Name);
          sep = "{0}, '{1}'";
        }
      }
      return new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    }

    void AddLimitedAxioms(Function f, int fromLayer) {
      Contract.Requires(f != null);
      Contract.Requires(f.IsRecursive);
      Contract.Requires(fromLayer == 1 || fromLayer == 2);
      Contract.Requires(sink != null && predef != null);
      // With fromLayer==1, generate:
      //   axiom (forall formals :: { f(args) } f(args) == f#limited(args))
      // With fromLayer==2, generate:
      // axiom (forall formals :: { f#2(args) } f#2(args) == f(args))

      Bpl.VariableSeq formals = new Bpl.VariableSeq();
      Bpl.ExprSeq args = new Bpl.ExprSeq();
      Bpl.BoundVariable bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      formals.Add(bv);
      args.Add(new Bpl.IdentifierExpr(f.tok, bv));
      Bpl.BoundVariable bvThis;
      Bpl.Expr bvThisIdExpr;
      if (f.IsStatic) {
        bvThis = null;
        bvThisIdExpr = null;
      } else {
        bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType));
        formals.Add(bvThis);
        bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        args.Add(bvThisIdExpr);
      }
      foreach (Formal p in f.Formals) {
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)));
        formals.Add(bv);
        args.Add(new Bpl.IdentifierExpr(p.tok, bv));
      }

      Bpl.FunctionCall origFuncID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, FunctionName(f, fromLayer), TrType(f.ResultType)));
      Bpl.Expr origFuncAppl = new Bpl.NAryExpr(f.tok, origFuncID, args);
      Bpl.FunctionCall limitedFuncID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, FunctionName(f, fromLayer-1), TrType(f.ResultType)));
      Bpl.Expr limitedFuncAppl = new Bpl.NAryExpr(f.tok, limitedFuncID, args);

      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(f.TypeArgs);

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new Bpl.ExprSeq(origFuncAppl));
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, null, tr, Bpl.Expr.Eq(origFuncAppl, limitedFuncAppl));
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax));
    }

    /// <summary>
    /// Returns the appropriate Boogie function for the given function.  In particular:
    /// Layer 2:  f#2        --currently used only for induction axioms
    /// Layer 1:  f          --this is the default name
    /// Layer 0:  f#limited  --does not trigger the function definition axiom
    /// </summary>
    public static string FunctionName(Function f, int layer) {
      Contract.Requires(f != null);
      Contract.Requires(0 <= layer && layer < 3);
      Contract.Ensures(Contract.Result<string>() != null);

      string name = f.FullName;
      switch (layer) {
        case 2: name += "#2"; break;
        case 0: name += "#limited"; break;
      }
      return name;
    }

    /// <summary>
    /// Generate:
    ///   axiom (forall h: [ref, Field x]x, o: ref ::
    ///        { h[o,f] }
    ///        $IsGoodHeap(h) && o != null && h[o,alloc] ==> h[o,f]-has-the-expected-type);
    /// </summary>
    void AddAllocationAxiom(Field f)
    {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);

      Bpl.BoundVariable hVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$h", predef.HeapType));
      Bpl.Expr h = new Bpl.IdentifierExpr(f.tok, hVar);
      ExpressionTranslator etran = new ExpressionTranslator(this, predef, h);
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$o", predef.RefType));
      Bpl.Expr o = new Bpl.IdentifierExpr(f.tok, oVar);

      // h[o,f]
      Bpl.Expr oDotF;
      if (f.IsMutable) {
        oDotF = ExpressionTranslator.ReadHeap(f.tok, h, o, new Bpl.IdentifierExpr(f.tok, GetField(f)));
      } else {
        oDotF = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(GetReadonlyField(f)), new Bpl.ExprSeq(o));
      }

      Bpl.Expr wh = GetWhereClause(f.tok, oDotF, f.Type, etran);
      if (wh != null) {
        // ante:  $IsGoodHeap(h) && o != null && h[o,alloc]
        Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.And(
          FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, h),
          Bpl.Expr.Neq(o, predef.Null)),
          etran.IsAlloced(f.tok, o));
        Bpl.Expr body = Bpl.Expr.Imp(ante, wh);
        Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new Bpl.ExprSeq(oDotF));
        Bpl.Expr ax = new Bpl.ForallExpr(f.tok, new Bpl.VariableSeq(hVar, oVar), tr, body);
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax));
      }
    }

    Bpl.Expr InSeqRange(IToken tok, Bpl.Expr index, Bpl.Expr seq, bool isSequence, Bpl.Expr lowerBound, bool includeUpperBound) {
      Contract.Requires(tok != null);
      Contract.Requires(index != null);
      Contract.Requires(seq != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (lowerBound == null) {
        lowerBound = Bpl.Expr.Literal(0);
      }
      Bpl.Expr lower = Bpl.Expr.Le(lowerBound, index);
      Bpl.Expr length = isSequence ?
        FunctionCall(tok, BuiltinFunction.SeqLength, null, seq) :
        ArrayLength(tok, seq, 1, 0);
      Bpl.Expr upper;
      if (includeUpperBound) {
        upper = Bpl.Expr.Le(index, length);
      } else {
        upper = Bpl.Expr.Lt(index, length);
      }
      return Bpl.Expr.And(lower, upper);
    }

    ModuleDecl currentModule = null;  // the name of the module whose members are currently being translated
    Method currentMethod = null;  // the method whose implementation is currently being translated
    int loopHeapVarCount = 0;
    int otherTmpVarCount = 0;
    Dictionary<string, Bpl.IdentifierExpr> _tmpIEs = new Dictionary<string, Bpl.IdentifierExpr>();
    Bpl.IdentifierExpr GetTmpVar_IdExpr(IToken tok, string name, Bpl.Type ty, Bpl.VariableSeq locals)  // local variable that's shared between statements that need it
    {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(ty != null);
      Contract.Requires(locals != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      Bpl.IdentifierExpr ie;
      if (_tmpIEs.TryGetValue(name, out ie)) {
        Contract.Assume(ie.Type.Equals(ty));
      } else {
        // the "tok" and "ty" of the first request for this variable is the one we use
        var v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, ty));  // important for the "$nw" client: no where clause (see GetNewVar_IdExpr)
        locals.Add(v);
        ie = new Bpl.IdentifierExpr(tok, v);
        _tmpIEs.Add(name, ie);
      }
      return ie;
    }

    Bpl.IdentifierExpr GetPrevHeapVar_IdExpr(IToken tok, Bpl.VariableSeq locals) {  // local variable that's shared between statements that need it
      Contract.Requires(tok != null);
      Contract.Requires(locals != null); Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      return GetTmpVar_IdExpr(tok, "$prevHeap", predef.HeapType, locals);
    }

    Bpl.IdentifierExpr GetNewVar_IdExpr(IToken tok, Bpl.VariableSeq locals)  // local variable that's shared between statements that need it
    {
      Contract.Requires(tok != null);
      Contract.Requires(locals != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      // important: the following declaration produces no where clause (that's why we're going through the trouble of setting of this variable in the first place)
      return GetTmpVar_IdExpr(tok, "$nw", predef.RefType, locals);
    }

    /// <summary>
    /// Returns an expression whose value is the same as "expr", but that is guaranteed to preserve the its value passed
    /// the evaluation of other expressions.  If necessary, a new local variable called "name" with type "ty" is added to "locals" and
    /// assigned in "builder" to be used to hold the value of "expr".  It is assumed that all requests for a given "name"
    /// have the same type "ty" and that these variables can be shared.
    /// As an optimization, if "otherExprsCanAffectPreviouslyKnownExpressions" is "false", then "expr" itself is returned.
    /// </summary>
    Bpl.Expr SaveInTemp(Bpl.Expr expr, bool otherExprsCanAffectPreviouslyKnownExpressions, string name, Bpl.Type ty, Bpl.StmtListBuilder builder, Bpl.VariableSeq locals) {
      Contract.Requires(expr != null);
      Contract.Requires(name != null);
      Contract.Requires(ty != null);
      Contract.Requires(locals != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (otherExprsCanAffectPreviouslyKnownExpressions) {
        var save = GetTmpVar_IdExpr(expr.tok, name, ty, locals);
        builder.Add(Bpl.Cmd.SimpleAssign(expr.tok, save, expr));
        return save;
      } else {
        return expr;
      }
    }

    void AddMethodImpl(Method m, Bpl.Procedure proc, bool wellformednessProc)
    {
      Contract.Requires(m != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);
      Contract.Requires(currentModule == null && currentMethod == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);
      Contract.Ensures(currentModule == null && currentMethod == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);

      currentModule = m.EnclosingClass.Module;
      currentMethod = m;

      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(m.TypeArgs);
      Bpl.VariableSeq inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Bpl.VariableSeq outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);
      Bpl.VariableSeq localVariables = new Bpl.VariableSeq();
      GenerateImplPrelude(m, inParams, outParams, builder, localVariables);

      Bpl.StmtList stmts;
      if (!wellformednessProc) {
        if (3 <= DafnyOptions.O.Induction && m.IsGhost && m.Mod.Expressions.Count == 0 && m.Outs.Count == 0) {
          var posts = new List<Expression>();
          m.Ens.ForEach(mfe => posts.Add(mfe.E));
          var allIns = new List<Formal>();
          if (!m.IsStatic) {
            allIns.Add(new ThisSurrogate(m.tok, Resolver.GetThisType(m.tok, (ClassDecl)m.EnclosingClass)));
          }
          allIns.AddRange(m.Ins);
          var inductionVars = ApplyInduction(allIns, m.Attributes, posts, delegate(System.IO.TextWriter wr) { wr.Write(m.FullName); });
          if (inductionVars.Count != 0) {
            // Let the parameters be this,x,y of the method M and suppose ApplyInduction returns this,y.
            // Also, let Pre be the precondition and VF be the decreases clause.
            // Then, insert into the method body what amounts to:
            //     assume case-analysis-on-parameter[[ y' ]];
            //     parallel (this', y' | Pre(this', x, y') && VF(this', x, y') << VF(this, x, y)) {
            //       this'.M(x, y');
            //     }
            // Generate bound variables for the parallel statement, and a substitution for the Pre and VF

            // assume case-analysis-on-parameter[[ y' ]];
            foreach (var inFormal in m.Ins) {
              var dt = inFormal.Type.AsDatatype;
              if (dt != null) {
                var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(inFormal.tok, "$IsA#" + dt.FullName, Bpl.Type.Bool));
                var f = new Bpl.IdentifierExpr(inFormal.tok, inFormal.UniqueName, TrType(inFormal.Type));
                builder.Add(new Bpl.AssumeCmd(inFormal.tok, new Bpl.NAryExpr(inFormal.tok, funcID, new Bpl.ExprSeq(f))));
              }
            }

            var parBoundVars = new List<BoundVar>();
            Expression receiverReplacement = null;
            var substMap = new Dictionary<IVariable, Expression>();
            foreach (var iv in inductionVars) {
              BoundVar bv;
              IdentifierExpr ie;
              CloneVariableAsBoundVar(iv.tok, iv, "$ih#" + iv.Name, out bv, out ie);
              parBoundVars.Add(bv);
              if (iv is ThisSurrogate) {
                Contract.Assert(receiverReplacement == null && substMap.Count == 0);  // the receiver comes first, if at all
                receiverReplacement = ie;
              } else {
                substMap.Add(iv, ie);
              }
            }

            // Generate a CallStmt for the recursive call
            Expression recursiveCallReceiver;
            if (receiverReplacement != null) {
              recursiveCallReceiver = receiverReplacement;
            } else if (m.IsStatic) {
              recursiveCallReceiver = new StaticReceiverExpr(m.tok, (ClassDecl)m.EnclosingClass);  // this also resolves it
            } else {
              recursiveCallReceiver = new ImplicitThisExpr(m.tok);
              recursiveCallReceiver.Type = Resolver.GetThisType(m.tok, (ClassDecl)m.EnclosingClass);  // resolve here
            }
            var recursiveCallArgs = new List<Expression>();
            foreach (var inFormal in m.Ins) {
              Expression inE;
              if (substMap.TryGetValue(inFormal, out inE)) {
                recursiveCallArgs.Add(inE);
              } else {
                var ie = new IdentifierExpr(inFormal.tok, inFormal.Name);
                ie.Var = inFormal;  // resolve here
                ie.Type = inFormal.Type;  // resolve here
                recursiveCallArgs.Add(ie);
              }
            }
            var recursiveCall = new CallStmt(m.tok, new List<Expression>(), recursiveCallReceiver, m.Name, recursiveCallArgs);
            recursiveCall.Method = m;  // resolve here

            Expression parRange = new LiteralExpr(m.tok, true);
            parRange.Type = Type.Bool;  // resolve here
            if (receiverReplacement != null) {
              // add "this' != null" to the range
              var nil = new LiteralExpr(receiverReplacement.tok);
              nil.Type = receiverReplacement.Type;  // resolve here
              var neqNull = new BinaryExpr(receiverReplacement.tok, BinaryExpr.Opcode.Neq, receiverReplacement, nil);
              neqNull.ResolvedOp = BinaryExpr.ResolvedOpcode.NeqCommon;  // resolve here
              neqNull.Type = Type.Bool;  // resolve here
              parRange = DafnyAnd(parRange, neqNull);
            }
            foreach (var pre in m.Req) {
              if (!pre.IsFree) {
                parRange = DafnyAnd(parRange, Substitute(pre.E, receiverReplacement, substMap));
              }
            }
            // construct an expression (generator) for:  VF' << VF
            ExpressionConverter decrCheck = delegate(Dictionary<IVariable, Expression> decrSubstMap, ExpressionTranslator exprTran) {
              var decrToks = new List<IToken>();
              var decrTypes = new List<Type>();
              var decrCallee = new List<Bpl.Expr>();
              var decrCaller = new List<Bpl.Expr>();
              bool decrInferred;  // we don't actually care
              foreach (var ee in MethodDecreasesWithDefault(m, out decrInferred)) {
                decrToks.Add(ee.tok);
                decrTypes.Add(ee.Type);
                decrCaller.Add(exprTran.TrExpr(ee));
                Expression es = Substitute(ee, receiverReplacement, substMap);
                es = Substitute(es, null, decrSubstMap);
                decrCallee.Add(exprTran.TrExpr(es));
              }
              return DecreasesCheck(decrToks, decrTypes, decrCallee, decrCaller, exprTran, null, null, false, true);
            };

#if VERIFY_CORRECTNESS_OF_TRANSLATION_PARALLEL_RANGE
            var definedness = new Bpl.StmtListBuilder();
            var exporter = new Bpl.StmtListBuilder();
            TrParallelCall(m.tok, parBoundVars, parRange, decrCheck, recursiveCall, definedness, exporter, localVariables, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(m.tok, null, definedness.Collect(m.tok), null, exporter.Collect(m.tok)));
#else
            TrParallelCall(m.tok, parBoundVars, parRange, decrCheck, recursiveCall, null, builder, localVariables, etran);
#endif
          }
        }
        // translate the body of the method
        Contract.Assert(m.Body != null);  // follows from method precondition and the if guard
        stmts = TrStmt2StmtList(builder, m.Body, localVariables, etran);
      } else {
        // check well-formedness of the preconditions, and then assume each one of them
        foreach (MaybeFreeExpression p in m.Req) {
          CheckWellformed(p.E, new WFOptions(), localVariables, builder, etran);
          builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
        }
        // Note: the modifies clauses are not checked for well-formedness (is that sound?), because it used to
        // be that the syntax was not rich enough for programmers to specify modifies clauses and always being
        // absolutely well-defined.
        // check well-formedness of the decreases clauses
        foreach (Expression p in m.Decreases.Expressions)
        {
          CheckWellformed(p, new WFOptions(), localVariables, builder, etran);
        }

        // play havoc with the heap according to the modifies clause
        builder.Add(new Bpl.HavocCmd(m.tok, new Bpl.IdentifierExprSeq((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr)));
        // assume the usual two-state boilerplate information
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, currentMethod.Mod.Expressions, etran.Old, etran, etran.Old))
        {
          if (tri.IsFree) {
            builder.Add(new Bpl.AssumeCmd(m.tok, tri.Expr));
          }
        }

        // also play havoc with the out parameters
        if (outParams.Length != 0) {  // don't create an empty havoc statement
          Bpl.IdentifierExprSeq outH = new Bpl.IdentifierExprSeq();
          foreach (Bpl.Variable b in outParams) {
            Contract.Assert(b != null);
            outH.Add(new Bpl.IdentifierExpr(b.tok, b));
          }
          builder.Add(new Bpl.HavocCmd(m.tok, outH));
        }

        // check wellformedness of postconditions
        foreach (MaybeFreeExpression p in m.Ens) {
          CheckWellformed(p.E, new WFOptions(), localVariables, builder, etran);
          builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
        }

        stmts = builder.Collect(m.tok);
      }

      QKeyValue kv = etran.TrAttributes(m.Attributes, null);

      Bpl.Implementation impl = new Bpl.Implementation(m.tok, proc.Name,
        typeParams, inParams, outParams,
        localVariables, stmts, kv);
      sink.TopLevelDeclarations.Add(impl);

      currentModule = null;
      currentMethod = null;
      loopHeapVarCount = 0;
      otherTmpVarCount = 0;
      _tmpIEs.Clear();
    }

    void GenerateImplPrelude(Method m, Bpl.VariableSeq inParams, Bpl.VariableSeq outParams,
                             Bpl.StmtListBuilder builder, Bpl.VariableSeq localVariables){
      Contract.Requires(m != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);

      // set up the information used to verify the method's modifies clause
      DefineFrame(m.tok, m.Mod.Expressions, builder, localVariables, null);
    }

    Bpl.Cmd CaptureState(IToken tok, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      string description = string.Format("{0}({1},{2}){3}{4}", tok.filename, tok.line, tok.col, additionalInfo == null ? "" : ": ", additionalInfo ?? "");
      QKeyValue kv = new QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return new Bpl.AssumeCmd(tok, Bpl.Expr.True, kv);
    }
    Bpl.Cmd CaptureState(IToken tok) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(tok, null);
    }

    void DefineFrame(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frameClause, Bpl.StmtListBuilder/*!*/ builder, Bpl.VariableSeq/*!*/ localVariables, string name){
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(frameClause));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(localVariables));
      Contract.Requires(predef != null);

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, tok);
      // Declare a local variable $_Frame: <alpha>[ref, Field alpha]bool
      Bpl.IdentifierExpr theFrame = etran.TheFrame(tok);  // this is a throw-away expression, used only to extract the type of the $_Frame variable
      Contract.Assert(theFrame.Type != null);  // follows from the postcondition of TheFrame
      Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name ?? theFrame.Name, theFrame.Type));
      localVariables.Add(frame);
      // $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
      Bpl.Expr consequent = InRWClause(tok, o, f, frameClause, etran, null, null);
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fVar), null,
                                           Bpl.Expr.Imp(ante, consequent));

      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));
    }

    void CheckFrameSubset(IToken tok, List<FrameExpression/*!*/>/*!*/ calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable,Expression/*!*/> substMap,
                          ExpressionTranslator/*!*/ etran, Bpl.StmtListBuilder/*!*/ builder, string errorMessage,
                          Bpl.QKeyValue kv)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(calleeFrame));
      Contract.Requires((receiverReplacement == null) == (substMap == null));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(etran != null);
      Contract.Requires(builder != null);
      Contract.Requires(errorMessage != null);
      Contract.Requires(predef != null);

      // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_Frame[o,f]);
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
      Bpl.Expr oInCallee = InRWClause(tok, o, f, calleeFrame, etran, receiverReplacement, substMap);
      Bpl.Expr inEnclosingFrame = Bpl.Expr.Select(etran.TheFrame(tok), o, f);
      Bpl.Expr q = new Bpl.ForallExpr(tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fVar),
                                      Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), inEnclosingFrame));
      builder.Add(Assert(tok, q, errorMessage, kv));
    }

    /// <summary>
    /// Generates:
    ///   axiom (forall h0: HeapType, h1: HeapType, formals... ::
    ///        { HeapSucc(h0,h1), F(h1,formals) }
    ///        heaps are well-formed and formals are allocated AND
    ///        HeapSucc(h0,h1)
    ///        AND
    ///        (forall(alpha) o: ref, f: Field alpha ::
    ///            o != null AND h0[o,alloc] AND h1[o,alloc] AND
    ///            o in reads clause of formals in h0
    ///            IMPLIES h0[o,f] == h1[o,f])
    ///        IMPLIES
    ///        F(h0,formals) == F(h1,formals)
    ///      );
    ///
    /// If the function is a recursive function, then the same axiom is also produced for "F#limited" instead of "F".
    /// </summary>
    void AddFrameAxiom(Function f)
    {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);

      Bpl.BoundVariable h0Var = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$h0", predef.HeapType));
      Bpl.BoundVariable h1Var = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$h1", predef.HeapType));
      Bpl.Expr h0 = new Bpl.IdentifierExpr(f.tok, h0Var);
      Bpl.Expr h1 = new Bpl.IdentifierExpr(f.tok, h1Var);
      ExpressionTranslator etran0 = new ExpressionTranslator(this, predef, h0);
      ExpressionTranslator etran1 = new ExpressionTranslator(this, predef, h1);

      Bpl.Expr wellFormed = Bpl.Expr.And(
        FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran0.HeapExpr),
        FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran1.HeapExpr));

      Bpl.TypeVariable alpha = new Bpl.TypeVariable(f.tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$o", predef.RefType));
      Bpl.Expr o = new Bpl.IdentifierExpr(f.tok, oVar);
      Bpl.BoundVariable fieldVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$f", predef.FieldName(f.tok, alpha)));
      Bpl.Expr field = new Bpl.IdentifierExpr(f.tok, fieldVar);
      Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
      Bpl.Expr oNotNullAlloced = Bpl.Expr.And(oNotNull, Bpl.Expr.And(etran0.IsAlloced(f.tok, o), etran1.IsAlloced(f.tok, o)));
      Bpl.Expr unchanged = Bpl.Expr.Eq(ExpressionTranslator.ReadHeap(f.tok, h0, o, field), ExpressionTranslator.ReadHeap(f.tok, h1, o, field));

      Bpl.Expr heapSucc = FunctionCall(f.tok, BuiltinFunction.HeapSucc, null, h0, h1);
      Bpl.Expr r0 = InRWClause(f.tok, o, field, f.Reads, etran0, null, null);
      Bpl.Expr q0 = new Bpl.ForallExpr(f.tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fieldVar),
        Bpl.Expr.Imp(Bpl.Expr.And(oNotNullAlloced, r0), unchanged));

      // bvars:  h0, h1, formals
      // f0args:  h0, formals
      // f1args:  h1, formals
      Bpl.VariableSeq bvars = new Bpl.VariableSeq();
      Bpl.ExprSeq f0args = new Bpl.ExprSeq();
      Bpl.ExprSeq f1args = new Bpl.ExprSeq();
      bvars.Add(h0Var);  bvars.Add(h1Var);
      f0args.Add(h0);
      f1args.Add(h1);
      if (!f.IsStatic) {
        Bpl.BoundVariable thVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType));
        Bpl.Expr th = new Bpl.IdentifierExpr(f.tok, thVar);
        bvars.Add(thVar);
        f0args.Add(th);
        f1args.Add(th);

        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(Bpl.Expr.Neq(th, predef.Null),
          Bpl.Expr.And(etran0.GoodRef(f.tok, th, thisType), etran1.GoodRef(f.tok, th, thisType)));
        wellFormed = Bpl.Expr.And(wellFormed, wh);
      }

      foreach (Formal p in f.Formals) {
        Bpl.BoundVariable bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)));
        bvars.Add(bv);
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        f0args.Add(formal);
        f1args.Add(formal);
        Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran0);
        if (wh != null) { wellFormed = Bpl.Expr.And(wellFormed, wh); }
        wh = GetWhereClause(p.tok, formal, p.Type, etran1);
        if (wh != null) { wellFormed = Bpl.Expr.And(wellFormed, wh); }
      }

      string axiomComment = "frame axiom for " + f.FullName;
      Bpl.FunctionCall fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullName, TrType(f.ResultType)));
      while (fn != null) {
        Bpl.Expr F0 = new Bpl.NAryExpr(f.tok, fn, f0args);
        Bpl.Expr F1 = new Bpl.NAryExpr(f.tok, fn, f1args);
        Bpl.Expr eq = Bpl.Expr.Eq(F0, F1);
        Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new Bpl.ExprSeq(heapSucc, F1));

        Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(f.TypeArgs);
        Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, bvars, null, tr,
          Bpl.Expr.Imp(Bpl.Expr.And(wellFormed, heapSucc),
          Bpl.Expr.Imp(q0, eq)));
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax, axiomComment));
        if (axiomComment != null && f.IsRecursive) {
          fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, FunctionName(f, 0), TrType(f.ResultType)));
          axiomComment = null;  // the comment goes only with the first frame axiom
        } else {
          break;  // no more frame axioms to produce
        }
      }
    }

    Bpl.Expr/*!*/ InRWClause(IToken/*!*/ tok, Bpl.Expr/*!*/ o, Bpl.Expr/*!*/ f, List<FrameExpression/*!*/>/*!*/ rw, ExpressionTranslator/*!*/ etran,
                             Expression receiverReplacement, Dictionary<IVariable,Expression/*!*/> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      Contract.Requires(f != null);
      Contract.Requires(etran != null);
      Contract.Requires(cce.NonNullElements(rw));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(predef != null);
      Contract.Requires((receiverReplacement == null) == (substMap == null));
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // requires o to denote an expression of type RefType
      // "rw" is is allowed to contain a WildcardExpr

      Bpl.Expr disjunction = null;
      foreach (FrameExpression rwComponent in rw) {
        Expression e = rwComponent.E;
        if (receiverReplacement != null) {
          Contract.Assert(substMap != null);
          e = Substitute(e, receiverReplacement, substMap);
        }
        Bpl.Expr disjunct;
        if (e is WildcardExpr) {
          disjunct = Bpl.Expr.True;
        } else if (e.Type is SetType) {
          // old(e)[Box(o)]
          disjunct = etran.TrInSet(tok, o, e, ((SetType)e.Type).Arg);
        } else if (e.Type is SeqType) {
          // (exists i: int :: 0 <= i && i < Seq#Length(old(e)) && Seq#Index(old(e),i) == Box(o))
          Bpl.Expr boxO = FunctionCall(tok, BuiltinFunction.Box, null, o);
          Bpl.Variable iVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$i", Bpl.Type.Int));
          Bpl.Expr i = new Bpl.IdentifierExpr(tok, iVar);
          Bpl.Expr iBounds = InSeqRange(tok, i, etran.TrExpr(e), true, null, false);
          Bpl.Expr XsubI = FunctionCall(tok, BuiltinFunction.SeqIndex, predef.BoxType, etran.TrExpr(e), i);
          // TODO: the equality in the next line should be changed to one that understands extensionality
          disjunct = new Bpl.ExistsExpr(tok, new Bpl.VariableSeq(iVar), Bpl.Expr.And(iBounds, Bpl.Expr.Eq(XsubI, boxO)));
        } else {
          // o == old(e)
          disjunct = Bpl.Expr.Eq(o, etran.TrExpr(e));
        }
        disjunct = Bpl.Expr.And(IsTotal(e, etran), disjunct);
        if (rwComponent.Field != null) {
          disjunct = Bpl.Expr.And(disjunct, Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.tok, GetField(rwComponent.Field))));
        }
        if (disjunction == null) {
          disjunction = disjunct;
        } else {
          disjunction = Bpl.Expr.Or(disjunction, disjunct);
        }
      }
      if (disjunction == null) {
        return Bpl.Expr.False;
      } else {
        return disjunction;
      }
    }

    void AddWellformednessCheck(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Requires(currentModule == null);
      Contract.Ensures(currentModule == null);

      currentModule = f.EnclosingClass.Module;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);
      // parameters of the procedure
      Bpl.VariableSeq inParams = new Bpl.VariableSeq();
      if (!f.IsStatic) {
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), predef.Null),
          etran.GoodRef(f.tok, new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), Resolver.GetReceiverType(f.tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType, wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in f.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.UniqueName, varType), p.Type, etran);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, varType, wh), true));
      }
      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(f.TypeArgs);
      // the procedure itself
      Bpl.RequiresSeq req = new Bpl.RequiresSeq();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      ModuleDecl mod = f.EnclosingClass.Module;
      Bpl.Expr context = Bpl.Expr.And(
        Bpl.Expr.Eq(Bpl.Expr.Literal(mod.Height), etran.ModuleContextHeight()),
        Bpl.Expr.Eq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight()));
      req.Add(Requires(f.tok, true, context, null, null));
      // check that postconditions hold
      var ens = new Bpl.EnsuresSeq();
      foreach (Expression p in f.Ens) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(p, etran, out splitHappened)) {
          if (!s.IsFree) {
            ens.Add(Ensures(s.E.tok, s.IsFree, s.E, null, null));
          }
        }
      }
      Bpl.Procedure proc = new Bpl.Procedure(f.tok, "CheckWellformed$$" + f.FullName, typeParams, inParams, new Bpl.VariableSeq(),
        req, new Bpl.IdentifierExprSeq(), ens, etran.TrAttributes(f.Attributes, null));
      sink.TopLevelDeclarations.Add(proc);

      VariableSeq implInParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Bpl.VariableSeq locals = new Bpl.VariableSeq();
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();

      // check well-formedness of the preconditions (including termination, but no reads checks), and then
      // assume each one of them
      foreach (Expression p in f.Req) {
        CheckWellformed(p, new WFOptions(f, null, false), locals, builder, etran);
        builder.Add(new Bpl.AssumeCmd(p.tok, etran.TrExpr(p)));
      }
      // Note: the reads clauses are not checked for well-formedness (is that sound?), because it used to
      // be that the syntax was not rich enough for programmers to specify reads clauses and always being
      // absolutely well-defined.
      // check well-formedness of the decreases clauses (including termination, but no reads checks)
      foreach (Expression p in f.Decreases.Expressions)
      {
        CheckWellformed(p, new WFOptions(f, null, false), locals, builder, etran);
      }
      // Generate:
      //   if (*) {
      //     check well-formedness of postcondition
      //     assume false;  // don't go on to check the postconditions
      //   } else {
      //     check well-formedness of body
      //     // fall through to check the postconditions themselves
      //   }
      // Here go the postconditions (termination checks included, but no reads checks)
      StmtListBuilder postCheckBuilder = new StmtListBuilder();
      // Assume the type returned by the call itself respects its type (this matter if the type is "nat", for example)
      {
        var args = new Bpl.ExprSeq();
        args.Add(etran.HeapExpr);
        if (!f.IsStatic) {
          args.Add(new Bpl.IdentifierExpr(f.tok, etran.This, predef.RefType));
        }
        foreach (var p in f.Formals) {
          args.Add(new Bpl.IdentifierExpr(p.tok, p.UniqueName, TrType(p.Type)));
        }
        Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, FunctionName(f, 1), TrType(f.ResultType));
        Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), args);

        var wh = GetWhereClause(f.tok, funcAppl, f.ResultType, etran);
        if (wh != null) {
          postCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, wh));
        }
      }
      // Now for the ensures clauses
      foreach (Expression p in f.Ens) {
        CheckWellformed(p, new WFOptions(f, f, false), locals, postCheckBuilder, etran);
        // assume the postcondition for the benefit of checking the remaining postconditions
        postCheckBuilder.Add(new Bpl.AssumeCmd(p.tok, etran.TrExpr(p)));
      }
      // Here goes the body (and include both termination checks and reads checks)
      StmtListBuilder bodyCheckBuilder = new StmtListBuilder();
      if (f.Body == null) {
        // don't fall through to postcondition checks
        bodyCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, Bpl.Expr.False));
      } else {
        Bpl.FunctionCall funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullName, TrType(f.ResultType)));
        Bpl.ExprSeq args = new Bpl.ExprSeq();
        args.Add(etran.HeapExpr);
        foreach (Variable p in implInParams) {
          args.Add(new Bpl.IdentifierExpr(f.tok, p));
        }
        Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, funcID, args);

        DefineFrame(f.tok, f.Reads, bodyCheckBuilder, locals, null);
        CheckWellformedWithResult(f.Body, new WFOptions(f, null, true), funcAppl, f.ResultType, locals, bodyCheckBuilder, etran);
      }
      // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
      postCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, Bpl.Expr.False));
      builder.Add(new Bpl.IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));

      Bpl.Implementation impl = new Bpl.Implementation(f.tok, proc.Name,
        typeParams, implInParams, new Bpl.VariableSeq(),
        locals, builder.Collect(f.tok));
      sink.TopLevelDeclarations.Add(impl);

      Contract.Assert(currentModule == f.EnclosingClass.Module);
      currentModule = null;
    }

    Bpl.Expr CtorInvocation(MatchCase mc, ExpressionTranslator etran, Bpl.VariableSeq locals, StmtListBuilder localTypeAssumptions) {
      Contract.Requires(mc != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      Bpl.ExprSeq args = new Bpl.ExprSeq();
      for (int i = 0; i < mc.Arguments.Count; i++) {
        BoundVar p = mc.Arguments[i];
        Bpl.Variable local = new Bpl.LocalVariable(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)));
        locals.Add(local);
        Type t = mc.Ctor.Formals[i].Type;
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, local), p.Type, etran);
        if (wh != null) {
          localTypeAssumptions.Add(new Bpl.AssumeCmd(p.tok, wh));
        }
        args.Add(etran.CondApplyBox(mc.tok, new Bpl.IdentifierExpr(p.tok, local), cce.NonNull(p.Type), t));
      }
      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(mc.tok, mc.Ctor.FullName, predef.DatatypeType);
      return new Bpl.NAryExpr(mc.tok, new Bpl.FunctionCall(id), args);
    }

    Bpl.Expr CtorInvocation(IToken tok, DatatypeCtor ctor, ExpressionTranslator etran, Bpl.VariableSeq locals, StmtListBuilder localTypeAssumptions) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // create local variables for the formals
      var args = new ExprSeq();
      foreach (Formal arg in ctor.Formals) {
        Contract.Assert(arg != null);
        var nm = string.Format("a{0}#{1}", args.Length, otherTmpVarCount);
        otherTmpVarCount++;
        Bpl.Variable bv = new Bpl.LocalVariable(arg.tok, new Bpl.TypedIdent(arg.tok, nm, TrType(arg.Type)));
        locals.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.tok, bv));
      }

      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(tok, ctor.FullName, predef.DatatypeType);
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(id), args);
    }

    Bpl.Expr IsTotal(Expression expr, ExpressionTranslator etran) {
      Contract.Requires(expr != null);Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (expr is LiteralExpr || expr is ThisExpr || expr is IdentifierExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        return Bpl.Expr.True;
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return IsTotal(e.Elements, etran);
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        if (e.Obj is ThisExpr) {
          return Bpl.Expr.True;
        } else {
          var t = IsTotal(e.Obj, etran);
          if (e.Obj.Type.IsRefType) {
            t = BplAnd(t, Bpl.Expr.Neq(etran.TrExpr(e.Obj), predef.Null));
          } else if (e.Field is DatatypeDestructor) {
            var dtor = (DatatypeDestructor)e.Field;
            t = BplAnd(t, FunctionCall(e.tok, dtor.EnclosingCtor.QueryField.FullName, Bpl.Type.Bool, etran.TrExpr(e.Obj)));
          }
          return t;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        bool isSequence = e.Seq.Type is SeqType;
        if (e.Seq.Type is MapType) {
          Bpl.Expr total = IsTotal(e.Seq, etran);
          Bpl.Expr map = etran.TrExpr(e.Seq);
          var e0 = etran.TrExpr(e.E0);
          Bpl.Expr inDomain = FunctionCall(expr.tok, BuiltinFunction.MapDomain, predef.MapType(e.tok, predef.BoxType, predef.BoxType), map);
          inDomain = Bpl.Expr.Select(inDomain, etran.BoxIfNecessary(e.tok, e0, e.E0.Type));
          total = BplAnd(total, inDomain);
          return total;
        } else {
          Bpl.Expr total = IsTotal(e.Seq, etran);
          Bpl.Expr seq = etran.TrExpr(e.Seq);
          Bpl.Expr e0 = null;
          if (e.E0 != null) {
            e0 = etran.TrExpr(e.E0);
            total = BplAnd(total, IsTotal(e.E0, etran));
            total = BplAnd(total, InSeqRange(expr.tok, e0, seq, isSequence, null, !e.SelectOne));
          }
          if (e.E1 != null) {
            total = BplAnd(total, IsTotal(e.E1, etran));
            total = BplAnd(total, InSeqRange(expr.tok, etran.TrExpr(e.E1), seq, isSequence, e0, true));
          }
          return total;
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        Bpl.Expr total = IsTotal(e.Array, etran);
        Bpl.Expr array = etran.TrExpr(e.Array);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          total = BplAnd(total, IsTotal(idx, etran));

          Bpl.Expr index = etran.TrExpr(idx);
          Bpl.Expr lower = Bpl.Expr.Le(Bpl.Expr.Literal(0), index);
          Bpl.Expr length = ArrayLength(idx.tok, array, e.Indices.Count, i);
          Bpl.Expr upper = Bpl.Expr.Lt(index, length);
          total = BplAnd(total, Bpl.Expr.And(lower, upper));
          i++;
        }
        return total;
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        Bpl.Expr total = IsTotal(e.Seq, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr index = etran.TrExpr(e.Index);
        total = BplAnd(total, IsTotal(e.Index, etran));
        total = BplAnd(total, InSeqRange(expr.tok, index, seq, true, null, false));
        total = BplAnd(total, IsTotal(e.Value, etran));
        return total;
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        // check well-formedness of receiver
        Bpl.Expr r = IsTotal(e.Receiver, etran);
        if (!e.Function.IsStatic && !(e.Receiver is ThisExpr)) {
          r = BplAnd(r, Bpl.Expr.Neq(etran.TrExpr(e.Receiver), predef.Null));
        }
        // check well-formedness of the other parameters
        r = BplAnd(r, IsTotal(e.Args, etran));
        // create a substitution map from each formal parameter to the corresponding actual parameter
        Dictionary<IVariable,Expression> substMap = new Dictionary<IVariable,Expression>();
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          var formal = e.Function.Formals[i];
          var s = CheckSubrange_Expr(e.Args[i].tok, etran.TrExpr(e.Args[i]), formal.Type);
          if (s != null) {
            r = BplAnd(r, s);
          }
          substMap.Add(formal, e.Args[i]);
        }
        // check that the preconditions for the call hold
        foreach (Expression p in e.Function.Req) {
          Expression precond = Substitute(p, e.Receiver, substMap);
          r = BplAnd(r, etran.TrExpr(precond));
        }
        // TODO: if this is a recursive call, also conjoin the well-ordering predicate
        return r;
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        var r = IsTotal(dtv.Arguments, etran);
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          var arg = dtv.Arguments[i];
          var s = CheckSubrange_Expr(arg.tok, etran.TrExpr(arg), formal.Type);
          if (s != null) {
            r = BplAnd(r, s);
          }
        }
        return r;
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        return IsTotal(e.E, etran.Old);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        return IsTotal(e.E, etran);
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        return IsTotal(e.E, etran);
      } else if (expr is AllocatedExpr) {
        AllocatedExpr e = (AllocatedExpr)expr;
        return IsTotal(e.E, etran);
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        Bpl.Expr t = IsTotal(e.E, etran);
        if (e.Op == UnaryExpr.Opcode.SetChoose) {
          Bpl.Expr emptySet = FunctionCall(expr.tok, BuiltinFunction.SetEmpty, predef.BoxType);
          return Bpl.Expr.And(t, Bpl.Expr.Neq(etran.TrExpr(e.E), emptySet));
        } else  if (e.Op == UnaryExpr.Opcode.SeqLength && !(e.E.Type is SeqType)) {
          return Bpl.Expr.And(t, Bpl.Expr.Neq(etran.TrExpr(e.E), predef.Null));
        }
        return t;
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        Bpl.Expr t0 = IsTotal(e.E0, etran);
        Bpl.Expr t1 = IsTotal(e.E1, etran);
        Bpl.Expr z = null;
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp:
            t1 = Bpl.Expr.Imp(etran.TrExpr(e.E0), t1);
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            t1 = Bpl.Expr.Imp(Bpl.Expr.Not(etran.TrExpr(e.E0)), t1);
            break;
          case BinaryExpr.ResolvedOpcode.Div:
          case BinaryExpr.ResolvedOpcode.Mod:
            z = Bpl.Expr.Neq(etran.TrExpr(e.E1), Bpl.Expr.Literal(0));
            break;
          default:
            break;
        }
        Bpl.Expr r = BplAnd(t0, t1);
        return z == null ? r : BplAnd(r, z);
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        Bpl.Expr total = Bpl.Expr.True;
        foreach (var rhs in e.RHSs) {
          total = BplAnd(total, IsTotal(rhs, etran));
        }
        return BplAnd(total, IsTotal(etran.GetSubstitutedBody(e), etran));

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var total = IsTotal(e.Term, etran);
        if (e.Range != null) {
          total = BplAnd(IsTotal(e.Range, etran), BplImp(etran.TrExpr(e.Range), total));
        }
        if (total != Bpl.Expr.True) {
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars);
          total = new Bpl.ForallExpr(expr.tok, bvars, Bpl.Expr.Imp(typeAntecedent, total));
        }
        return total;
      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        Bpl.Expr gTotal = IsTotal(e.Guard, etran);
        Bpl.Expr g = etran.TrExpr(e.Guard);
        Bpl.Expr bTotal = IsTotal(e.Body, etran);
        if (e is AssertExpr || DafnyOptions.O.DisallowSoundnessCheating) {
          return BplAnd(gTotal, BplAnd(g, bTotal));
        } else {
          return BplAnd(gTotal, Bpl.Expr.Imp(g, bTotal));
        }
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Bpl.Expr total = IsTotal(e.Test, etran);
        Bpl.Expr test = etran.TrExpr(e.Test);
        total = BplAnd(total, Bpl.Expr.Imp(test, IsTotal(e.Thn, etran)));
        total = BplAnd(total, Bpl.Expr.Imp(Bpl.Expr.Not(test), IsTotal(e.Els, etran)));
        return total;
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return IsTotal(e.ResolvedExpression, etran);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    Bpl.Expr/*!*/ IsTotal(List<Expression/*!*/>/*!*/ exprs, ExpressionTranslator/*!*/ etran) {
      Contract.Requires(etran != null);
      Contract.Requires(exprs != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      Bpl.Expr total = Bpl.Expr.True;
      foreach (Expression e in exprs) {
        Contract.Assert(e != null);
        total = BplAnd(total, IsTotal(e, etran));
      }
      return total;
    }

    Bpl.Expr CanCallAssumption(Expression expr, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (expr is LiteralExpr || expr is ThisExpr || expr is IdentifierExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        return Bpl.Expr.True;
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        return CanCallAssumption(e.Elements, etran);
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        List<Expression> l = new List<Expression>();
        foreach (ExpressionPair p in e.Elements) {
          l.Add(p.A); l.Add(p.B);
        }
        return CanCallAssumption(l, etran);
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        if (e.Obj is ThisExpr) {
          return Bpl.Expr.True;
        } else {
          Bpl.Expr r = CanCallAssumption(e.Obj, etran);
          return r;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        //bool isSequence = e.Seq.Type is SeqType;
        Bpl.Expr total = CanCallAssumption(e.Seq, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr e0 = null;
        if (e.E0 != null) {
          e0 = etran.TrExpr(e.E0);
          total = BplAnd(total, CanCallAssumption(e.E0, etran));
        }
        if (e.E1 != null) {
          total = BplAnd(total, CanCallAssumption(e.E1, etran));
        }
        return total;
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        Bpl.Expr total = CanCallAssumption(e.Array, etran);
        foreach (Expression idx in e.Indices) {
          total = BplAnd(total, CanCallAssumption(idx, etran));
        }
        return total;
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        Bpl.Expr total = CanCallAssumption(e.Seq, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr index = etran.TrExpr(e.Index);
        total = BplAnd(total, CanCallAssumption(e.Index, etran));
        total = BplAnd(total, CanCallAssumption(e.Value, etran));
        return total;
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        // check well-formedness of receiver
        Bpl.Expr r = CanCallAssumption(e.Receiver, etran);
        // check well-formedness of the other parameters
        r = BplAnd(r, CanCallAssumption(e.Args, etran));
        // get to assume canCall
        Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullName + "#canCall", Bpl.Type.Bool);
        ExprSeq args = etran.FunctionInvocationArguments(e);
        Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
        r = BplAnd(r, canCallFuncAppl);
        return r;
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        return CanCallAssumption(dtv.Arguments, etran);
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        return CanCallAssumption(e.E, etran.Old);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is AllocatedExpr) {
        AllocatedExpr e = (AllocatedExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        Bpl.Expr t = CanCallAssumption(e.E, etran);
        return t;
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        Bpl.Expr t0 = CanCallAssumption(e.E0, etran);
        Bpl.Expr t1 = CanCallAssumption(e.E1, etran);
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp:
            t1 = Bpl.Expr.Imp(etran.TrExpr(e.E0), t1);
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            t1 = Bpl.Expr.Imp(Bpl.Expr.Not(etran.TrExpr(e.E0)), t1);
            break;
          default:
            break;
        }
        return BplAnd(t0, t1);
      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        Bpl.Expr canCall = Bpl.Expr.True;
        foreach (var rhs in e.RHSs) {
          canCall = BplAnd(canCall, CanCallAssumption(rhs, etran));
        }
        return BplAnd(canCall, CanCallAssumption(etran.GetSubstitutedBody(e), etran));

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var total = CanCallAssumption(e.Term, etran);
        if (e.Range != null) {
          total = BplAnd(CanCallAssumption(e.Range, etran), BplImp(etran.TrExpr(e.Range), total));
        }
        if (total != Bpl.Expr.True) {
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars);
          total = new Bpl.ForallExpr(expr.tok, bvars, Bpl.Expr.Imp(typeAntecedent, total));
        }
        return total;
      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        Bpl.Expr gCanCall = CanCallAssumption(e.Guard, etran);
        Bpl.Expr bCanCall = CanCallAssumption(e.Body, etran);
        if (e is AssertExpr || DafnyOptions.O.DisallowSoundnessCheating) {
          return BplAnd(gCanCall, bCanCall);
        } else {
          Bpl.Expr g = etran.TrExpr(e.Guard);
          return BplAnd(gCanCall, Bpl.Expr.Imp(g, bCanCall));
        }
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Bpl.Expr total = CanCallAssumption(e.Test, etran);
        Bpl.Expr test = etran.TrExpr(e.Test);
        total = BplAnd(total, Bpl.Expr.Imp(test, CanCallAssumption(e.Thn, etran)));
        total = BplAnd(total, Bpl.Expr.Imp(Bpl.Expr.Not(test), CanCallAssumption(e.Els, etran)));
        return total;
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return CanCallAssumption(e.ResolvedExpression, etran);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    Bpl.Expr/*!*/ CanCallAssumption(List<Expression/*!*/>/*!*/ exprs, ExpressionTranslator/*!*/ etran) {
      Contract.Requires(etran != null);
      Contract.Requires(exprs != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      Bpl.Expr total = Bpl.Expr.True;
      foreach (Expression e in exprs) {
        Contract.Assert(e != null);
        total = BplAnd(total, CanCallAssumption(e, etran));
      }
      return total;
    }

    Expression DafnyAnd(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      if (LiteralExpr.IsTrue(a)) {
        return b;
      } else if (LiteralExpr.IsTrue(b)) {
        return a;
      } else {
        BinaryExpr and = new BinaryExpr(a.tok, BinaryExpr.Opcode.And, a, b);
        and.ResolvedOp = BinaryExpr.ResolvedOpcode.And;  // resolve here
        and.Type = Type.Bool;  // resolve here
        return and;
      }
    }

    Bpl.Expr BplAnd(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True) {
        return b;
      } else if (b == Bpl.Expr.True) {
        return a;
      } else {
        return Bpl.Expr.And(a, b);
      }
    }

    Bpl.Expr BplImp(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True || b == Bpl.Expr.True) {
        return b;
      } else {
        return Bpl.Expr.Imp(a, b);
      }
    }

    void CheckNonNull(IToken tok, Expression e, Bpl.StmtListBuilder builder, ExpressionTranslator etran, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (e is ThisExpr) {
        // already known to be non-null
      } else {
        builder.Add(Assert(tok, Bpl.Expr.Neq(etran.TrExpr(e), predef.Null), "target object may be null", kv));
      }
    }

    /// <summary>
    /// Instances of WFContext are used as an argument to CheckWellformed, supplying options for the
    /// checks to be performed.
    /// If non-null, "Decr" gives the caller to be used for termination checks.  If it is null, no
    /// termination checks are performed.
    /// If "SelfCallsAllowance" is non-null, termination checks will be omitted for calls that look
    /// like it.  This is useful in function postconditions, where the result of the function is
    /// syntactically given as what looks like a recursive call with the same arguments.
    /// "DoReadsChecks" indicates whether or not to perform reads checks.  If so, the generated code
    /// will make references to $_Frame.
    /// </summary>
    class WFOptions
    {
      public readonly Function Decr;
      public readonly Function SelfCallsAllowance;
      public readonly bool DoReadsChecks;
      public readonly Bpl.QKeyValue AssertKv;
      public WFOptions() { }
      public WFOptions(Function decr, Function selfCallsAllowance, bool doReadsChecks) {
        Decr = decr;
        SelfCallsAllowance = selfCallsAllowance;
        DoReadsChecks = doReadsChecks;
      }
      public WFOptions(Bpl.QKeyValue kv) {
        AssertKv = kv;
      }
    }

    void TrStmt_CheckWellformed(Expression expr, Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran, bool subsumption) {
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      Bpl.QKeyValue kv;
      if (subsumption) {
        kv = null;  // this is the default behavior of Boogie's assert
      } else {
        List<object> args = new List<object>();
        // {:subsumption 0}
        args.Add(Bpl.Expr.Literal(0));
        kv = new Bpl.QKeyValue(expr.tok, "subsumption", args, null);
      }
      CheckWellformed(expr, new WFOptions(kv), locals, builder, etran);
      builder.Add(new Bpl.AssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
    }

    void CheckWellformed(Expression expr, WFOptions options, Bpl.VariableSeq locals, Bpl.StmtListBuilder builder, ExpressionTranslator etran) {
      CheckWellformedWithResult(expr, options, null, null, locals, builder, etran);
    }

    /// <summary>
    /// Adds to "builder" code that checks the well-formedness of "expr".  Any local variables introduced
    /// in this code are added to "locals".
    /// If "result" is non-null, then after checking the well-formedness of "expr", the generated code will
    /// assume the equivalent of "result == expr".
    /// See class WFOptions for descriptions of the specified options.
    /// </summary>
    void CheckWellformedWithResult(Expression expr, WFOptions options, Bpl.Expr result, Type resultType,
                                   Bpl.VariableSeq locals, Bpl.StmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Contract.Requires((result == null) == (resultType == null));
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (expr is LiteralExpr || expr is ThisExpr || expr is IdentifierExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        // always allowed
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        foreach (Expression el in e.Elements) {
          CheckWellformed(el, options, locals, builder, etran);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        foreach (ExpressionPair p in e.Elements) {
          CheckWellformed(p.A, options, locals, builder, etran);
          CheckWellformed(p.B, options, locals, builder, etran);
        }
      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr e = (FieldSelectExpr)expr;
        CheckWellformed(e.Obj, options, locals, builder, etran);
        if (e.Obj.Type.IsRefType) {
          CheckNonNull(expr.tok, e.Obj, builder, etran, options.AssertKv);
        } else if (e.Field is DatatypeDestructor) {
          var dtor = (DatatypeDestructor)e.Field;
          var correctConstructor = FunctionCall(e.tok, dtor.EnclosingCtor.QueryField.FullName, Bpl.Type.Bool, etran.TrExpr(e.Obj));
          if (dtor.EnclosingCtor.EnclosingDatatype.Ctors.Count == 1) {
            // There is only one constructor, so the value must be been constructed by it; might as well assume that here.
            builder.Add(new Bpl.AssumeCmd(expr.tok, correctConstructor));
          } else {
            builder.Add(Assert(expr.tok, correctConstructor,
              string.Format("destructor '{0}' can only be applied to datatype values constructed by '{1}'", dtor.Name, dtor.EnclosingCtor.Name)));
          }
        }
        if (options.DoReadsChecks && e.Field.IsMutable) {
          builder.Add(Assert(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), etran.TrExpr(e.Obj), GetField(e)), "insufficient reads clause to read field", options.AssertKv));
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        bool isSequence = e.Seq.Type is SeqType;
        CheckWellformed(e.Seq, options, locals, builder, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        if (e.Seq.Type.IsArrayType) {
          builder.Add(Assert(e.Seq.tok, Bpl.Expr.Neq(seq, predef.Null), "array may be null"));
        }
        Bpl.Expr e0 = null;
        if (e.Seq.Type is MapType) {
          e0 = etran.TrExpr(e.E0);
          CheckWellformed(e.E0, options, locals, builder, etran);
          Bpl.Expr inDomain = FunctionCall(expr.tok, BuiltinFunction.MapDomain, predef.MapType(e.tok, predef.BoxType, predef.BoxType), seq);
          inDomain = Bpl.Expr.Select(inDomain, etran.BoxIfNecessary(e.tok, e0, e.E0.Type));
          builder.Add(Assert(expr.tok, inDomain, "element may not be in domain", options.AssertKv));
          
        } else {
          if (e.E0 != null) {
            e0 = etran.TrExpr(e.E0);
            CheckWellformed(e.E0, options, locals, builder, etran);
            builder.Add(Assert(expr.tok, InSeqRange(expr.tok, e0, seq, isSequence, null, !e.SelectOne), e.SelectOne ? "index out of range" : "lower bound out of range", options.AssertKv));
          }
          if (e.E1 != null) {
            CheckWellformed(e.E1, options, locals, builder, etran);
            builder.Add(Assert(expr.tok, InSeqRange(expr.tok, etran.TrExpr(e.E1), seq, isSequence, e0, true), "upper bound " + (e.E0 == null ? "" : "below lower bound or ") + "above length of " + (isSequence ? "sequence" : "array"), options.AssertKv));
          }
        }
        if (options.DoReadsChecks && cce.NonNull(e.Seq.Type).IsArrayType) {
          if (e.SelectOne) {
            Contract.Assert(e.E0 != null);
            Bpl.Expr fieldName = FunctionCall(expr.tok, BuiltinFunction.IndexField, null, etran.TrExpr(e.E0));
            builder.Add(Assert(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), seq, fieldName), "insufficient reads clause to read array element", options.AssertKv));
          } else {
            Bpl.Expr lowerBound = e.E0 == null ? Bpl.Expr.Literal(0) : etran.TrExpr(e.E0);
            Contract.Assert((e.Seq.Type).AsArrayType.Dims == 1);
            Bpl.Expr upperBound = e.E1 == null ? ArrayLength(e.tok, seq, 1, 0) : etran.TrExpr(e.E1);
            // check that, for all i in lowerBound..upperBound, a[i] is in the frame
            Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.tok, new Bpl.TypedIdent(e.tok, "$i", Bpl.Type.Int));
            Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.tok, iVar);
            var range = BplAnd(Bpl.Expr.Le(lowerBound, i), Bpl.Expr.Lt(i, upperBound));
            var fieldName = FunctionCall(e.tok, BuiltinFunction.IndexField, null, i);
            var allowedToRead = Bpl.Expr.SelectTok(e.tok, etran.TheFrame(e.tok), seq, fieldName);
            var qq = new Bpl.ForallExpr(e.tok, new Bpl.VariableSeq(iVar), Bpl.Expr.Imp(range, allowedToRead));
            builder.Add(Assert(expr.tok, qq, "insufficient reads clause to read the indicated range of array elements", options.AssertKv));
          }
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        CheckWellformed(e.Array, options, locals, builder, etran);
        Bpl.Expr array = etran.TrExpr(e.Array);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          CheckWellformed(idx, options, locals, builder, etran);

          Bpl.Expr index = etran.TrExpr(idx);
          Bpl.Expr lower = Bpl.Expr.Le(Bpl.Expr.Literal(0), index);
          Bpl.Expr length = ArrayLength(idx.tok, array, e.Indices.Count, i);
          Bpl.Expr upper = Bpl.Expr.Lt(index, length);
          builder.Add(Assert(idx.tok, Bpl.Expr.And(lower, upper), "index " + i + " out of range", options.AssertKv));
          i++;
        }
      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        CheckWellformed(e.Seq, options, locals, builder, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr index = etran.TrExpr(e.Index);
        CheckWellformed(e.Index, options, locals, builder, etran);
        if (e.Seq.Type is SeqType) {
          builder.Add(Assert(expr.tok, InSeqRange(expr.tok, index, seq, true, null, false), "index out of range", options.AssertKv));
        } else {
          Contract.Assert(e.Seq.Type is MapType);
          // updates add to maps, so are always valid if the values are well formed.
        }
        CheckWellformed(e.Value, options, locals, builder, etran);
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        // check well-formedness of receiver
        CheckWellformed(e.Receiver, options, locals, builder, etran);
        if (!e.Function.IsStatic && !(e.Receiver is ThisExpr)) {
          CheckNonNull(expr.tok, e.Receiver, builder, etran, options.AssertKv);
        }
        // check well-formedness of the other parameters
        foreach (Expression arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }
        // create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          Formal p = e.Function.Formals[i];
          VarDecl local = new VarDecl(p.tok, p.Name, p.Type, p.IsGhost);
          local.type = local.OptionalType;  // resolve local here
          IdentifierExpr ie = new IdentifierExpr(local.Tok, local.UniqueName);
          ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(p, ie);
          locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.UniqueName, TrType(local.Type))));
          Bpl.IdentifierExpr lhs = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
          Expression ee = e.Args[i];
          CheckSubrange(ee.tok, etran.TrExpr(ee), p.Type, builder);
          Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.tok, lhs, etran.CondApplyBox(p.tok, etran.TrExpr(ee), cce.NonNull(ee.Type), p.Type));
          builder.Add(cmd);
        }
        // Check that every parameter is available in the state in which the function is invoked; this means checking that it has
        // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
        // access to expressions of the appropriate type and that are allocated in the current state.  However, if the function is
        // invoked in the 'old' state, then we need to check that its arguments were all available at that time as well.
        if (etran.UsesOldHeap) {
          if (!e.Function.IsStatic) {
            Bpl.Expr wh = GetWhereClause(e.Receiver.tok, etran.TrExpr(e.Receiver), e.Receiver.Type, etran);
            if (wh != null) {
              builder.Add(Assert(e.Receiver.tok, wh, "receiver argument must be allocated in the state in which the function is invoked"));
            }
          }
          for (int i = 0; i < e.Args.Count; i++) {
            Expression ee = e.Args[i];
            Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran);
            if (wh != null) {
              builder.Add(Assert(ee.tok, wh, "argument must be allocated in the state in which the function is invoked"));
            }
          }
        }
        // check that the preconditions for the call hold
        foreach (Expression p in e.Function.Req) {
          Expression precond = Substitute(p, e.Receiver, substMap);
          builder.Add(Assert(expr.tok, etran.TrExpr(precond), "possible violation of function precondition", options.AssertKv));
        }
        Bpl.Expr allowance = null;
        if (options.Decr != null || options.DoReadsChecks) {
          if (options.DoReadsChecks) {
            // check that the callee reads only what the caller is already allowed to read
            CheckFrameSubset(expr.tok, e.Function.Reads, e.Receiver, substMap, etran, builder, "insufficient reads clause to invoke function", options.AssertKv);
          }

          if (options.Decr != null && e.CoCall != FunctionCallExpr.CoCallResolution.Yes) {
            // check that the decreases measure goes down
            ModuleDecl module = cce.NonNull(e.Function.EnclosingClass).Module;
            if (module == cce.NonNull(options.Decr.EnclosingClass).Module) {
              if (module.CallGraph.GetSCCRepresentative(e.Function) == module.CallGraph.GetSCCRepresentative(options.Decr)) {
                bool contextDecrInferred, calleeDecrInferred;
                List<Expression> contextDecreases = FunctionDecreasesWithDefault(options.Decr, out contextDecrInferred);
                List<Expression> calleeDecreases = FunctionDecreasesWithDefault(e.Function, out calleeDecrInferred);
                if (e.Function == options.SelfCallsAllowance) {
                  allowance = Bpl.Expr.True;
                  if (!e.Function.IsStatic) {
                    allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(e.Receiver), new Bpl.IdentifierExpr(e.tok, etran.This, predef.RefType)));
                  }
                  for (int i = 0; i < e.Args.Count; i++) {
                    Expression ee = e.Args[i];
                    Formal ff = e.Function.Formals[i];
                    allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(ee), new Bpl.IdentifierExpr(e.tok, ff.UniqueName, TrType(ff.Type))));
                  }
                }
                string hint;
                switch (e.CoCall) {
                  case FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects:
                    hint = "note that only functions without side effects can called co-recursively";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded:
                    hint = "note that the call is not sufficiently guarded to be used co-recursively";
                    break;
                  case FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext:
                    hint = "note that calls cannot be co-recursive in this context";
                    break;
                  case FunctionCallExpr.CoCallResolution.No:
                    hint = null;
                    break;
                  default:
                    Contract.Assert(false);  // unexpected CoCallResolution
                    goto case FunctionCallExpr.CoCallResolution.No;  // please the compiler
                }
                CheckCallTermination(expr.tok, contextDecreases, calleeDecreases, allowance, e.Receiver, substMap, etran, builder,
                  contextDecrInferred, hint);
              }
            }
          }
        }
        // all is okay, so allow this function application access to the function's axiom, except if it was okay because of the self-call allowance.
        Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullName + "#canCall", Bpl.Type.Bool);
        ExprSeq args = etran.FunctionInvocationArguments(e);
        Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
        builder.Add(new Bpl.AssumeCmd(expr.tok, allowance == null ? canCallFuncAppl : Bpl.Expr.Or(allowance, canCallFuncAppl)));

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          var arg = dtv.Arguments[i];
          CheckWellformed(arg, options, locals, builder, etran);
          CheckSubrange(arg.tok, etran.TrExpr(arg), formal.Type, builder);
        }
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran.Old);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is AllocatedExpr) {
        AllocatedExpr e = (AllocatedExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
        if (e.Op == UnaryExpr.Opcode.SetChoose) {
          Bpl.Expr emptySet = FunctionCall(expr.tok, BuiltinFunction.SetEmpty, predef.BoxType);
          builder.Add(Assert(expr.tok, Bpl.Expr.Neq(etran.TrExpr(e.E), emptySet), "choose is defined only on nonempty sets"));
        } else if (e.Op == UnaryExpr.Opcode.SeqLength && !(e.E.Type is SeqType)) {
          CheckNonNull(expr.tok, e.E, builder, etran, options.AssertKv);
        }
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        CheckWellformed(e.E0, options, locals, builder, etran);
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp: {
              Bpl.StmtListBuilder b = new Bpl.StmtListBuilder();
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.E0), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Or: {
              Bpl.StmtListBuilder b = new Bpl.StmtListBuilder();
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.E0)), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Div:
          case BinaryExpr.ResolvedOpcode.Mod:
            CheckWellformed(e.E1, options, locals, builder, etran);
            builder.Add(Assert(expr.tok, Bpl.Expr.Neq(etran.TrExpr(e.E1), Bpl.Expr.Literal(0)), "possible division by zero", options.AssertKv));
            break;
          default:
            CheckWellformed(e.E1, options, locals, builder, etran);
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;

        var substMap = new Dictionary<IVariable, Expression>();
        Contract.Assert(e.Vars.Count == e.RHSs.Count);  // checked by resolution
        for (int i = 0; i < e.Vars.Count; i++) {
          var vr = e.Vars[i];
          var tp = TrType(vr.Type);
          var v = new Bpl.LocalVariable(vr.tok, new Bpl.TypedIdent(vr.tok, vr.UniqueName, tp));
          locals.Add(v);
          var lhs = new Bpl.IdentifierExpr(vr.tok, vr.UniqueName, tp);

          CheckWellformedWithResult(e.RHSs[i], options, lhs, vr.Type, locals, builder, etran);
          substMap.Add(vr, new BoogieWrapper(lhs, vr.Type));
        }
        CheckWellformedWithResult(Substitute(e.Body, null, substMap), options, result, resultType, locals, builder, etran);
        result = null;

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var substMap = SetupBoundVarsAsLocals(e.BoundVars, builder, locals, etran);
        Expression body = Substitute(e.Term, null, substMap);
        if (e.Range == null) {
          CheckWellformed(body, options, locals, builder, etran);
        } else {
          Expression range = Substitute(e.Range, null, substMap);
          CheckWellformed(range, options, locals, builder, etran);

          Bpl.StmtListBuilder b = new Bpl.StmtListBuilder();
          CheckWellformed(body, options, locals, b, etran);
          builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(range), b.Collect(expr.tok), null, null));
        }

      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        CheckWellformed(e.Guard, options, locals, builder, etran);
        if (e is AssertExpr || DafnyOptions.O.DisallowSoundnessCheating) {
          bool splitHappened;
          var ss = TrSplitExpr(e.Guard, etran, out splitHappened);
          if (!splitHappened) {
            builder.Add(Assert(e.Guard.tok, etran.TrExpr(e.Guard), "condition in assert expression might not hold"));
          } else {
            foreach (var split in ss) {
              if (!split.IsFree) {
                builder.Add(AssertNS(split.E.tok, split.E, "condition in assert expression might not hold"));
              }
            }
            builder.Add(new Bpl.AssumeCmd(e.tok, etran.TrExpr(e.Guard)));
          }
        } else {
          builder.Add(new Bpl.AssumeCmd(e.tok, etran.TrExpr(e.Guard)));
        }
        CheckWellformed(e.Body, options, locals, builder, etran);

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        CheckWellformed(e.Test, options, locals, builder, etran);
        Bpl.StmtListBuilder bThen = new Bpl.StmtListBuilder();
        Bpl.StmtListBuilder bElse = new Bpl.StmtListBuilder();
        CheckWellformed(e.Thn, options, locals, bThen, etran);
        CheckWellformed(e.Els, options, locals, bElse, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.Test), bThen.Collect(expr.tok), null, bElse.Collect(expr.tok)));

      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        CheckWellformed(me.Source, options, locals, builder, etran);
        Bpl.Expr src = etran.TrExpr(me.Source);
        Bpl.IfCmd ifCmd = null;
        StmtListBuilder elsBldr = new StmtListBuilder();
        elsBldr.Add(new Bpl.AssumeCmd(expr.tok, Bpl.Expr.False));
        StmtList els = elsBldr.Collect(expr.tok);
        foreach (var missingCtor in me.MissingCases) {
          // havoc all bound variables
          var b = new Bpl.StmtListBuilder();
          VariableSeq newLocals = new VariableSeq();
          Bpl.Expr r = CtorInvocation(me.tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Length != 0) {
            Bpl.IdentifierExprSeq havocIds = new Bpl.IdentifierExprSeq();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(me.tok, havocIds));
          }
          b.Add(Assert(me.tok, Bpl.Expr.False, "missing case in case statement: " + missingCtor.Name));

          Bpl.Expr guard = Bpl.Expr.Eq(src, r);
          ifCmd = new Bpl.IfCmd(me.tok, guard, b.Collect(me.tok), ifCmd, els);
          els = null;
        }
        for (int i = me.Cases.Count; 0 <= --i; ) {
          MatchCaseExpr mc = me.Cases[i];
          Bpl.StmtListBuilder b = new Bpl.StmtListBuilder();
          Bpl.Expr ct = CtorInvocation(mc, etran, locals, b);
          // generate:  if (src == ctor(args)) { assume args-is-well-typed; mc.Body is well-formed; assume Result == TrExpr(case); } else ...
          CheckWellformedWithResult(mc.Body, options, result, resultType, locals, b, etran);
          ifCmd = new Bpl.IfCmd(mc.tok, Bpl.Expr.Eq(src, ct), b.Collect(mc.tok), ifCmd, els);
          els = null;
        }
        builder.Add(ifCmd);
        result = null;

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        CheckWellformedWithResult(e.ResolvedExpression, options, result, resultType, locals, builder, etran);
        result = null;

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (result != null) {
        Contract.Assert(resultType != null);
        var bResult = etran.TrExpr(expr);
        CheckSubrange(expr.tok, bResult, resultType, builder);
        builder.Add(new Bpl.AssumeCmd(expr.tok, Bpl.Expr.Eq(result, bResult)));
        builder.Add(new Bpl.AssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
      }
    }

    /// <summary>
    /// Returns true if it is known how to meaningfully compare the type's inhabitants.
    /// </summary>
    bool IsOrdered(Type t) {
      return !t.IsTypeParameter && !t.IsCoDatatype;
    }

    List<Expression> MethodDecreasesWithDefault(Method m, out bool inferredDecreases) {
      Contract.Requires(m != null);

      inferredDecreases = false;
      List<Expression> decr = m.Decreases.Expressions;
      if (decr.Count == 0) {
        decr = new List<Expression>();
        foreach (Formal p in m.Ins) {
          if (IsOrdered(p.Type)) {
            IdentifierExpr ie = new IdentifierExpr(p.tok, p.UniqueName);
            ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
            decr.Add(ie);  // use the method's first parameter instead
          }
        }
        inferredDecreases = true;
      }
      return decr;
    }

    List<Expression> FunctionDecreasesWithDefault(Function f, out bool inferredDecreases) {
      Contract.Requires(f != null);

      inferredDecreases = false;
      List<Expression> decr = f.Decreases.Expressions;
      if (decr.Count == 0) {
        decr = new List<Expression>();
        if (f.Reads.Count == 0) {
          foreach (Formal p in f.Formals) {
            if (IsOrdered(p.Type)) {
              IdentifierExpr ie = new IdentifierExpr(p.tok, p.UniqueName);
              ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
              decr.Add(ie);  // use the function's first parameter instead
            }
          }
          inferredDecreases = true;
        } else {
          decr.Add(FrameToObjectSet(f.Reads));  // use its reads clause instead
        }
      }
      return decr;
    }

    List<Expression> LoopDecreasesWithDefault(IToken tok, Expression Guard, List<Expression> Decreases, out bool inferredDecreases) {
      Contract.Requires(tok != null);
      Contract.Requires(Decreases != null);

      List<Expression> theDecreases = Decreases;
      inferredDecreases = false;
      if (theDecreases.Count == 0 && Guard != null) {
        theDecreases = new List<Expression>();
        Expression prefix = null;
        foreach (Expression guardConjunct in Conjuncts(Guard)) {
          Expression guess = null;
          BinaryExpr bin = guardConjunct as BinaryExpr;
          if (bin != null) {
            switch (bin.ResolvedOp) {
              case BinaryExpr.ResolvedOpcode.Lt:
              case BinaryExpr.ResolvedOpcode.Le:
                // for A < B and A <= B, use the decreases B - A
                guess = CreateIntSub(tok, bin.E1, bin.E0);
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
              case BinaryExpr.ResolvedOpcode.Gt:
                // for A >= B and A > B, use the decreases A - B
                guess = CreateIntSub(tok, bin.E0, bin.E1);
                break;
              case BinaryExpr.ResolvedOpcode.NeqCommon:
                if (bin.E0.Type is IntType) {
                  // for A != B where A and B are integers, use the absolute difference between A and B (that is: if 0 <= A-B then A-B else B-A)
                  Expression AminusB = CreateIntSub(tok, bin.E0, bin.E1);
                  Expression BminusA = CreateIntSub(tok, bin.E1, bin.E0);
                  Expression zero = CreateIntLiteral(tok, 0);
                  BinaryExpr test = new BinaryExpr(tok, BinaryExpr.Opcode.Le, zero, AminusB);
                  test.ResolvedOp = BinaryExpr.ResolvedOpcode.Le;  // resolve here
                  test.Type = Type.Bool;  // resolve here
                  guess = CreateIntITE(tok, test, AminusB, BminusA);
                }
                break;
              default:
                break;
            }
          }
          if (guess != null) {
            if (prefix != null) {
              // Make the following guess:  if prefix then guess else -1
              Expression negativeOne = CreateIntLiteral(tok, -1);
              guess = CreateIntITE(tok, prefix, guess, negativeOne);
            }
            theDecreases.Add(guess);
            inferredDecreases = true;
            break;  // ignore any further conjuncts
          }
          if (prefix == null) {
            prefix = guardConjunct;
          } else {
            prefix = DafnyAnd(prefix, guardConjunct);
          }
        }
      }
      return theDecreases;
    }

    Expression FrameToObjectSet(List<FrameExpression> fexprs) {
      Contract.Requires(fexprs != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      List<Expression> sets = new List<Expression>();
      List<Expression> singletons = null;
      foreach (FrameExpression fe in fexprs) {
        Contract.Assert(fe != null);
        if (fe.E is WildcardExpr) {
          // drop wildcards altogether
        } else {
          Expression e = fe.E;  // keep only fe.E, drop any fe.Field designation
          Contract.Assert(e.Type != null);  // should have been resolved already
          if (e.Type.IsRefType) {
            // e represents a singleton set
            if (singletons == null) {
              singletons = new List<Expression>();
            }
            singletons.Add(e);
          } else if (e.Type is SeqType) {
            // e represents a sequence
            // Add:  set x :: x in e
            var bv = new BoundVar(e.tok, "_s2s_" + otherTmpVarCount, ((SeqType)e.Type).Arg);
            otherTmpVarCount++;  // use this counter, but for a Dafny name (the idea being that the number and the initial "_" in the name might avoid name conflicts)
            var bvIE = new IdentifierExpr(e.tok, bv.Name);
            bvIE.Var = bv;  // resolve here
            bvIE.Type = bv.Type;  // resolve here
            var sInE = new BinaryExpr(e.tok, BinaryExpr.Opcode.In, bvIE, e);
            sInE.ResolvedOp = BinaryExpr.ResolvedOpcode.InSeq;  // resolve here
            sInE.Type = Type.Bool;  // resolve here
            var s = new SetComprehension(e.tok, new List<BoundVar>() { bv }, sInE, bvIE);
            s.Type = new SetType(new ObjectType());  // resolve here
            sets.Add(s);
          } else {
            // e is already a set
            Contract.Assert(e.Type is SetType);
            sets.Add(e);
          }
        }
      }
      if (singletons != null) {
        Expression display = new SetDisplayExpr(singletons[0].tok, singletons);
        display.Type = new SetType(new ObjectType());  // resolve here
        sets.Add(display);
      }
      if (sets.Count == 0) {
        Expression emptyset = new SetDisplayExpr(Token.NoToken, new List<Expression>());
        emptyset.Type = new SetType(new ObjectType());  // resolve here
        return emptyset;
      } else {
        Expression s = sets[0];
        for (int i = 1; i < sets.Count; i++) {
          BinaryExpr union = new BinaryExpr(s.tok, BinaryExpr.Opcode.Add, s, sets[i]);
          union.ResolvedOp = BinaryExpr.ResolvedOpcode.Union;  // resolve here
          union.Type = new SetType(new ObjectType());  // resolve here
          s = union;
        }
        return s;
      }
    }

    void CloneVariableAsBoundVar(IToken tok, IVariable iv, string prefix, out BoundVar bv, out IdentifierExpr ie) {
      Contract.Requires(tok != null);
      Contract.Requires(iv != null);
      Contract.Requires(prefix != null);
      Contract.Ensures(Contract.ValueAtReturn(out bv) != null);
      Contract.Ensures(Contract.ValueAtReturn(out ie) != null);

      bv = new BoundVar(tok, prefix + otherTmpVarCount, iv.Type);
      otherTmpVarCount++;  // use this counter, but for a Dafny name (the idea being that the number and the initial "_" in the name might avoid name conflicts)
      ie = new IdentifierExpr(tok, bv.Name);
      ie.Var = bv;  // resolve here
      ie.Type = bv.Type;  // resolve here
    }

    Bpl.Constant GetClass(TopLevelDecl cl)
    {
      Contract.Requires(cl != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      Bpl.Constant cc;
      if (classes.TryGetValue(cl, out cc)) {
        Contract.Assert(cc != null);
      } else {
        cc = new Bpl.Constant(cl.tok, new Bpl.TypedIdent(cl.tok, "class." + cl.FullName, predef.ClassNameType), true);
        classes.Add(cl, cc);
      }
      return cc;
    }

    Bpl.Expr GetTypeExpr(IToken tok, Type type)
    {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(predef != null);
      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy
          // TODO: what to do here?
          return null;
        } else {
          type = tp.T;
        }
      }

      if (type is BoolType) {
        return new Bpl.IdentifierExpr(tok, "class._System.bool", predef.ClassNameType);
      } else if (type is IntType) {
        return new Bpl.IdentifierExpr(tok, "class._System.int", predef.ClassNameType);
      } else if (type is ObjectType) {
        return new Bpl.IdentifierExpr(tok, "class._System.object", predef.ClassNameType);
      } else if (type is CollectionType) {
        CollectionType ct = (CollectionType)type;
        Bpl.Expr a = GetTypeExpr(tok, ct.Arg);
        if (a == null) {
         return null;
        }
        Bpl.Expr t = new Bpl.IdentifierExpr(tok, ct is SetType ? "class._System.set" : (ct is SeqType ? "class._System.seq" : "class._System.multiset"), predef.ClassNameType); // ^^^ todo: this needs to talk about multisets too.
        return FunctionCall(tok, BuiltinFunction.TypeTuple, null, t, a);
      } else {
        UserDefinedType ct = (UserDefinedType)type;
        if (ct.ResolvedClass == null) {
         return null;  // TODO: what to do here?
        }
        Bpl.Expr t = new Bpl.IdentifierExpr(tok, GetClass(ct.ResolvedClass));
        foreach (Type arg in ct.TypeArgs) {
          Bpl.Expr a = GetTypeExpr(tok, arg);
          if (a == null) {
            return null;
          }
          t = FunctionCall(tok, BuiltinFunction.TypeTuple, null, t, a);
        }
        return t;
      }
    }

    Bpl.Constant GetField(Field f)
    {
      Contract.Requires(f != null && f.IsMutable);
      Contract.Requires(sink != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      Bpl.Constant fc;
      if (fields.TryGetValue(f, out fc)) {
        Contract.Assert(fc != null);
      } else {
        // const unique f: Field ty;
        Bpl.Type ty = predef.FieldName(f.tok, TrType(f.Type));
        fc = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, f.FullName, ty), true);
        fields.Add(f, fc);
        // axiom FDim(f) == 0 && DeclType(f) == C;
        Bpl.Expr fdim = Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.FDim, ty, Bpl.Expr.Ident(fc)), Bpl.Expr.Literal(0));
        Bpl.Expr declType = Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.DeclType, ty, Bpl.Expr.Ident(fc)), new Bpl.IdentifierExpr(f.tok, GetClass(cce.NonNull(f.EnclosingClass))));
        Bpl.Axiom ax = new Bpl.Axiom(f.tok, Bpl.Expr.And(fdim, declType));
        sink.TopLevelDeclarations.Add(ax);
      }
      return fc;
    }

    Bpl.Function GetReadonlyField(Field f)
    {
      Contract.Requires(f != null && !f.IsMutable);
      Contract.Requires(sink != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.Function>() != null);

      Bpl.Function ff;
      if (fieldFunctions.TryGetValue(f, out ff)) {
        Contract.Assert(ff != null);
      } else {
        if (f.EnclosingClass is ArrayClassDecl && f.Name == "Length") { // link directly to the function in the prelude.
          fieldFunctions.Add(f, predef.ArrayLength);
          return predef.ArrayLength;
        }
        // function f(Ref): ty;
        Bpl.Type ty = TrType(f.Type);
        Bpl.VariableSeq args = new Bpl.VariableSeq();
        Bpl.Type receiverType = f.EnclosingClass is ClassDecl ? predef.RefType : predef.DatatypeType;
        args.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", receiverType), true));
        Bpl.Formal result = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, ty), false);
        ff = new Bpl.Function(f.tok, f.FullName, args, result);
        fieldFunctions.Add(f, ff);
        // treat certain fields specially
        if (f.EnclosingClass is ArrayClassDecl) {
          // add non-negative-range axioms for array Length fields
          // axiom (forall o: Ref :: 0 <= array.Length(o));
          Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "o", predef.RefType));
          Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(f.tok, oVar);
          Bpl.Expr body = Bpl.Expr.Le(Bpl.Expr.Literal(0), new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(ff), new Bpl.ExprSeq(o)));
          Bpl.Expr qq = new Bpl.ForallExpr(f.tok, new Bpl.VariableSeq(oVar), body);
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, qq));
        }
      }
      return ff;
    }

    Bpl.Expr GetField(FieldSelectExpr fse)
    {
      Contract.Requires(fse != null);
      Contract.Requires(fse.Field != null && fse.Field.IsMutable);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return new Bpl.IdentifierExpr(fse.tok, GetField(fse.Field));
    }

    /// <summary>
    /// This method is expected to be called just once for each function in the program.
    /// </summary>
    void AddFunction(Function f)
    {
      Contract.Requires(f != null);
      Contract.Requires(predef != null && sink != null);
      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(f.TypeArgs);
      Bpl.VariableSeq args = new Bpl.VariableSeq();
      args.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
      if (!f.IsStatic) {
        args.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType), true));
      }
      foreach (Formal p in f.Formals) {
        args.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, TrType(p.Type)), true));
      }
      Bpl.Formal res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
      Bpl.Function func = new Bpl.Function(f.tok, f.FullName, typeParams, args, res);
      sink.TopLevelDeclarations.Add(func);

      if (f.IsRecursive) {
        sink.TopLevelDeclarations.Add(new Bpl.Function(f.tok, FunctionName(f, 0), args, res));
        sink.TopLevelDeclarations.Add(new Bpl.Function(f.tok, FunctionName(f, 2), args, res));
      }

      res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
      Bpl.Function canCallF = new Bpl.Function(f.tok, f.FullName + "#canCall", args, res);
      sink.TopLevelDeclarations.Add(canCallF);
    }

    /// <summary>
    /// This method is expected to be called at most 4 times for each procedure in the program:
    /// *  once with kind==0, which says to create a procedure for the wellformedness check of the
    ///    method's specification
    /// *  once with kind==1, which says to create the ordinary procedure for the method, always
    ///    suitable for inter-module callers, and for non-refinement methods also suitable for
    ///    the implementation and intra-module callers of the method
    /// *  possibly once with kind==2 (allowed only if isRefinementMethod), which says to create
    ///    a procedure suitable for intra-module callers of a refinement method
    /// *  possibly once with kind==3 (allowed only if isRefinementMethod), which says to create
    ///    a procedure suitable for the implementation of a refinement method
    /// </summary>
    Bpl.Procedure AddMethod(Method m, int kind, bool isRefinementMethod)
    {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(0 <= kind && kind < 4);
      Contract.Requires(isRefinementMethod || kind < 2);
      Contract.Requires(predef != null);
      Contract.Requires(currentModule == null && currentMethod == null);
      Contract.Ensures(currentModule == null && currentMethod == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);

      currentModule = m.EnclosingClass.Module;
      currentMethod = m;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);

      Bpl.VariableSeq inParams = new Bpl.VariableSeq();
      Bpl.VariableSeq outParams = new Bpl.VariableSeq();
      if (!m.IsStatic) {
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(new Bpl.IdentifierExpr(m.tok, "this", predef.RefType), predef.Null),
          etran.GoodRef(m.tok, new Bpl.IdentifierExpr(m.tok, "this", predef.RefType), Resolver.GetReceiverType(m.tok, m)));
        Bpl.Formal thVar = new Bpl.Formal(m.tok, new Bpl.TypedIdent(m.tok, "this", predef.RefType, wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in m.Ins) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.UniqueName, varType), p.Type, etran);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, varType, wh), true));
      }
      foreach (Formal p in m.Outs) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.UniqueName, varType), p.Type, etran);
        outParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.UniqueName, varType, wh), false));
      }

      Bpl.RequiresSeq req = new Bpl.RequiresSeq();
      Bpl.IdentifierExprSeq mod = new Bpl.IdentifierExprSeq();
      Bpl.EnsuresSeq ens = new Bpl.EnsuresSeq();
      if (kind == 0 || (kind == 1 && !isRefinementMethod) || kind == 3) {  // the other cases have no need for a free precondition
        // free requires mh == ModuleContextHeight && InMethodContext;
        Bpl.Expr context = Bpl.Expr.And(
          Bpl.Expr.Eq(Bpl.Expr.Literal(m.EnclosingClass.Module.Height), etran.ModuleContextHeight()),
          etran.InMethodContext());
        req.Add(Requires(m.tok, true, context, null, null));
      }
      mod.Add((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr);
      mod.Add(etran.Tick());

      if (kind != 0) {
        string comment = "user-defined preconditions";
        foreach (MaybeFreeExpression p in m.Req) {
          if ((p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) || kind == 3) {  // kind==3 never has callers, so no reason to bother splitting
            req.Add(Requires(p.E.tok, true, etran.TrExpr(p.E), null, comment));
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, out splitHappened)) {
              if (kind == 2 && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this precondition was inherited into this module, so just ignore it
              } else {
                req.Add(Requires(s.E.tok, s.IsFree, s.E, null, null));
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
          comment = null;
        }
        comment = "user-defined postconditions";
        foreach (MaybeFreeExpression p in m.Ens) {
          if ((p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) || (kind == 1 && isRefinementMethod) || kind == 2) {  // for refinement methods, kind==1 has no implementations, and kind==2 never has implementations
            ens.Add(Ensures(p.E.tok, true, etran.TrExpr(p.E), null, comment));
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, out splitHappened)) {
              if (kind == 3 && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this postcondition was inherited into this module, so just ignore it
              } else {
                ens.Add(Ensures(s.E.tok, s.IsFree, s.E, null, null));
              }
            }
          }
          comment = null;
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, etran.Old, etran, etran.Old)) {
          ens.Add(Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
        }
      }

      Bpl.TypeVariableSeq typeParams = TrTypeParamDecls(m.TypeArgs);
      string name;
      switch (kind) {
        case 0: name = "CheckWellformed$$" + m.FullName; break;
        case 1: name = m.FullName; break;
        case 2: name = string.Format("RefinementCall_{0}$${1}", m.EnclosingClass.Module.Name, m.FullName); break;
        case 3: name = string.Format("RefinementImpl_{0}$${1}", m.EnclosingClass.Module.Name, m.FullName); break;
        default: Contract.Assert(false); throw new cce.UnreachableException();  // unexpected kind
      }
      Bpl.Procedure proc = new Bpl.Procedure(m.tok, name, typeParams, inParams, outParams, req, mod, ens);

      currentModule = null;
      currentMethod = null;

      return proc;
    }

    class BoilerplateTriple {  // a triple that is now a quintuple
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(tok != null);
        Contract.Invariant(Expr != null);
        Contract.Invariant(IsFree || ErrorMessage != null);
      }

      public readonly IToken tok;
      public readonly bool IsFree;
      public readonly Bpl.Expr Expr;
      public readonly string ErrorMessage;
      public readonly string Comment;


      public BoilerplateTriple(IToken tok, bool isFree, Bpl.Expr expr, string errorMessage, string comment)
       {
        Contract.Requires(tok != null);
        Contract.Requires(expr != null);
        Contract.Requires(isFree || errorMessage != null);
        this.tok = tok;
        IsFree = isFree;
        Expr = expr;
        ErrorMessage = errorMessage;
        Comment = comment;
      }
    }

    /// <summary>
    /// There are 3 states of interest when generating two-state boilerplate:
    ///  S0. the beginning of the method or loop, which is where the modifies clause is interpreted
    ///  S1. the pre-state of the two-state interval
    ///  S2. the post-state of the two-state interval
    /// This method assumes that etranPre denotes S1, etran denotes S2, and that etranMod denotes S0.
    /// </summary>
    List<BoilerplateTriple/*!*/>/*!*/ GetTwoStateBoilerplate(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ modifiesClause, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
    {
      Contract.Requires(tok != null);
      Contract.Requires(modifiesClause != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(etran != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<BoilerplateTriple>>()));

      List<BoilerplateTriple> boilerplate = new List<BoilerplateTriple>();

      // the frame condition, which is free since it is checked with every heap update and call
      boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, etranPre, etran, etranMod), null, "frame condition"));

      // HeapSucc(S1, S2)
      Bpl.Expr heapSucc = FunctionCall(tok, BuiltinFunction.HeapSucc, null, etranPre.HeapExpr, etran.HeapExpr);
      boilerplate.Add(new BoilerplateTriple(tok, true, heapSucc, null, "boilerplate"));

      return boilerplate;
    }

    /// <summary>
    /// There are 3 states of interest when generating a frame condition:
    ///  S0. the beginning of the method/loop, which is where the modifies clause is interpreted
    ///  S1. the pre-state of the two-state interval
    ///  S2. the post-state of the two-state interval
    /// This method assumes that etranPre denotes S1, etran denotes S2, and that etranMod denotes S0.
    /// </summary>
    Bpl.Expr/*!*/ FrameCondition(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ modifiesClause, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
    {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(cce.NonNullElements(modifiesClause));
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // generate:
      //  (forall<alpha> o: ref, f: Field alpha :: { $Heap[o,f] }
      //      o != null && old($Heap)[o,alloc] ==>
      //        $Heap[o,f] == PreHeap[o,f] ||
      //        (o,f) in modifiesClause)
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);

      Bpl.Expr heapOF = ExpressionTranslator.ReadHeap(tok, etran.HeapExpr, o, f);
      Bpl.Expr preHeapOF = ExpressionTranslator.ReadHeap(tok, etranPre.HeapExpr, o, f);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etranMod.IsAlloced(tok, o));
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = Bpl.Expr.Or(consequent, InRWClause(tok, o, f, modifiesClause, etranMod, null, null));

      Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(heapOF));
      return new Bpl.ForallExpr(tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fVar), null, tr, Bpl.Expr.Imp(ante, consequent));
    }
    Bpl.Expr/*!*/ FrameConditionUsingDefinedFrame(IToken/*!*/ tok, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
    {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // generate:
      //  (forall<alpha> o: ref, f: Field alpha :: { $Heap[o,f] }
      //      o != null && old($Heap)[o,alloc] ==>
      //        $Heap[o,f] == PreHeap[o,f] ||
      //        $_Frame[o,f])
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);

      Bpl.Expr heapOF = ExpressionTranslator.ReadHeap(tok, etran.HeapExpr, o, f);
      Bpl.Expr preHeapOF = ExpressionTranslator.ReadHeap(tok, etranPre.HeapExpr, o, f);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etranPre.IsAlloced(tok, o));
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = Bpl.Expr.Or(consequent, Bpl.Expr.SelectTok(tok, etranMod.TheFrame(tok), o, f));

      Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(heapOF));
      return new Bpl.ForallExpr(tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fVar), null, tr, Bpl.Expr.Imp(ante, consequent));
    }
    // ----- Type ---------------------------------------------------------------------------------

    Bpl.Type TrType(Type type)
     {
      Contract.Requires(type != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Type>() != null);

      while (true) {
        TypeProxy tp = type as TypeProxy;
        if (tp == null) {
          break;
        } else if (tp.T == null) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return predef.RefType;
        } else {
          type = tp.T;
        }
      }

      if (type is BoolType) {
        return Bpl.Type.Bool;
      } else if (type is IntType) {
        return Bpl.Type.Int;
      } else if (type.IsTypeParameter) {
        return predef.BoxType;
      } else if (type.IsRefType) {
        // object and class types translate to ref
        return predef.RefType;
      } else if (type.IsDatatype || type is DatatypeProxy) {
        return predef.DatatypeType;
      } else if (type is SetType) {
        return predef.SetType(Token.NoToken, predef.BoxType);
      } else if (type is MultiSetType) {
        return predef.MultiSetType(Token.NoToken, predef.BoxType);
      } else if (type is MapType) {
        return predef.MapType(Token.NoToken, predef.BoxType, predef.BoxType);
      } else if (type is SeqType) {
        return predef.SeqType(Token.NoToken, predef.BoxType);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    Bpl.TypeVariableSeq TrTypeParamDecls(List<TypeParameter/*!*/>/*!*/ tps)
    {
      Contract.Requires(cce.NonNullElements(tps));
      Contract.Ensures(Contract.Result<Bpl.TypeVariableSeq>() != null);

      Bpl.TypeVariableSeq typeParams = new Bpl.TypeVariableSeq();
      return typeParams;
    }

    // ----- Statement ----------------------------------------------------------------------------

    /// <summary>
    /// A ForceCheckToken is a token wrapper whose purpose is to hide inheritance.
    /// </summary>
    public class ForceCheckToken : TokenWrapper
    {
      public ForceCheckToken(IToken tok)
        : base(tok) {
        Contract.Requires(tok != null);
      }
      public static IToken Unwrap(IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<IToken>() != null);
        var ftok = tok as ForceCheckToken;
        return ftok != null ? ftok.WrappedToken : tok;
      }
    }

    Bpl.PredicateCmd Assert(Bpl.IToken tok, Bpl.Expr condition, string errorMessage)
    {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Requires(errorMessage != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (RefinementToken.IsInherited(tok, currentModule)) {
        // produce an assume instead
        return new Bpl.AssumeCmd(tok, condition);
      } else {
        var cmd = new Bpl.AssertCmd(ForceCheckToken.Unwrap(tok), condition);
        cmd.ErrorData = "Error: " + errorMessage;
        return cmd;
      }
    }

    Bpl.PredicateCmd AssertNS(Bpl.IToken tok, Bpl.Expr condition, string errorMessage)
    {
      Contract.Requires(tok != null);
      Contract.Requires(errorMessage != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (RefinementToken.IsInherited(tok, currentModule)) {
        // produce a "skip" instead
        return new Bpl.AssumeCmd(tok, Bpl.Expr.True);
      } else {
        tok = ForceCheckToken.Unwrap(tok);
        var args = new List<object>();
        args.Add(Bpl.Expr.Literal(0));
        Bpl.QKeyValue kv = new Bpl.QKeyValue(tok, "subsumption", args, null);
        Bpl.AssertCmd cmd = new Bpl.AssertCmd(tok, condition, kv);
        cmd.ErrorData = "Error: " + errorMessage;
        return cmd;
      }
    }

    Bpl.PredicateCmd Assert(Bpl.IToken tok, Bpl.Expr condition, string errorMessage, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(errorMessage != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (RefinementToken.IsInherited(tok, currentModule)) {
        // produce an assume instead
        return new Bpl.AssumeCmd(tok, condition, kv);
      } else {
        var cmd = new Bpl.AssertCmd(ForceCheckToken.Unwrap(tok), condition, kv);
        cmd.ErrorData = "Error: " + errorMessage;
        return cmd;
      }
    }

    Bpl.Ensures Ensures(IToken tok, bool free, Bpl.Expr condition, string errorMessage, string comment)
    {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      Bpl.Ensures ens = new Bpl.Ensures(ForceCheckToken.Unwrap(tok), free, condition, comment);
      if (errorMessage != null) {
        ens.ErrorData = errorMessage;
      }
      return ens;
    }

    Bpl.Requires Requires(IToken tok, bool free, Bpl.Expr condition, string errorMessage, string comment)
    {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Bpl.Requires req = new Bpl.Requires(ForceCheckToken.Unwrap(tok), free, condition, comment);
      if (errorMessage != null) {
        req.ErrorData = errorMessage;
      }
      return req;
    }

    Bpl.StmtList TrStmt2StmtList(Statement block, Bpl.VariableSeq locals, ExpressionTranslator etran)
    {
      Contract.Requires(block != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(currentMethod != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.StmtList>() != null);

      return TrStmt2StmtList(new Bpl.StmtListBuilder(), block, locals, etran);
    }

    Bpl.StmtList TrStmt2StmtList(Bpl.StmtListBuilder builder, Statement block, Bpl.VariableSeq locals, ExpressionTranslator etran)
    {
      Contract.Requires(builder != null);
      Contract.Requires(block != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(currentMethod != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.StmtList>() != null);

      TrStmt(block, builder, locals, etran);
      return builder.Collect(block.Tok);  // TODO: would be nice to have an end-curly location for "block"
    }

    void TrStmt(Statement stmt, Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(currentMethod != null && predef != null);
      if (stmt is PredicateStmt) {
        if (stmt is AssertStmt || DafnyOptions.O.DisallowSoundnessCheating) {
          AddComment(builder, stmt, "assert statement");
          PredicateStmt s = (PredicateStmt)stmt;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
          IToken enclosingToken = null;
          if (Attributes.Contains(stmt.Attributes, "prependAssertToken")) {
            enclosingToken = stmt.Tok;
          }
          bool splitHappened;
          var ss = TrSplitExpr(s.Expr, etran, out splitHappened);
          if (!splitHappened) {
            var tok = enclosingToken == null ? s.Expr.tok : new NestedToken(enclosingToken, s.Expr.tok);
            builder.Add(Assert(tok, etran.TrExpr(s.Expr), "assertion violation"));
          } else {
            foreach (var split in ss) {
              if (!split.IsFree) {
                var tok = enclosingToken == null ? split.E.tok : new NestedToken(enclosingToken, split.E.tok);
                builder.Add(AssertNS(tok, split.E, "assertion violation"));
              }
            }
            builder.Add(new Bpl.AssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
          }
        } else if (stmt is AssumeStmt) {
          AddComment(builder, stmt, "assume statement");
          AssumeStmt s = (AssumeStmt)stmt;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
          builder.Add(new Bpl.AssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
        }
      } else if (stmt is PrintStmt) {
        AddComment(builder, stmt, "print statement");
        PrintStmt s = (PrintStmt)stmt;
        foreach (Attributes.Argument arg in s.Args) {
          if (arg.E != null) {
            TrStmt_CheckWellformed(arg.E, builder, locals, etran, false);
          }
        }

      } else if (stmt is BreakStmt) {
        AddComment(builder, stmt, "break statement");
        var s = (BreakStmt)stmt;
        builder.Add(new GotoCmd(s.Tok, new StringSeq("after_" + s.TargetStmt.Labels.Data.UniqueId)));
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        AddComment(builder, stmt, "return statement");
        if (s.hiddenUpdate != null) {
          TrStmt(s.hiddenUpdate, builder, locals, etran);
        }
        builder.Add(new Bpl.ReturnCmd(stmt.Tok));
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        AddComment(builder, s, "assign-such-that statement");
        // Essentially, treat like an assert, a parallel havoc, and an assume.  However, we also need to check
        // the well-formedness of the expression, which is easiest to do after the havoc.  So, we do the havoc
        // first, then the well-formedness check, then the assert (unless the whole statement is an assume), and
        // finally the assume.

        // Here comes the havoc part
        var lhss = new List<Expression>();
        var havocRhss = new List<AssignmentRhs>();
        foreach (var lhs in s.Lhss) {
          lhss.Add(lhs.Resolved);
          havocRhss.Add(new HavocRhs(lhs.tok));  // note, a HavocRhs is constructed as already resolved
        }
        List<AssignToLhs> lhsBuilder;
        List<Bpl.IdentifierExpr> bLhss;
        Bpl.Expr[] ignore1, ignore2;
        string[] ignore3;
        ProcessLhss(lhss, false, true, builder, locals, etran, out lhsBuilder, out bLhss, out ignore1, out ignore2, out ignore3);
        ProcessRhss(lhsBuilder, bLhss, lhss, havocRhss, builder, locals, etran);
        // Here comes the well-formedness check
        TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
        // Here comes the assert part
        if (s.AssumeToken == null) {
          var substMap = new Dictionary<IVariable, Expression>();
          var bvars = new List<BoundVar>();
          foreach (var lhs in s.Lhss) {
            var l = lhs.Resolved;
            if (l is IdentifierExpr) {
              var x = (IdentifierExpr)l;
              BoundVar bv;
              IdentifierExpr ie;
              CloneVariableAsBoundVar(x.tok, x.Var, "$as#" + x.Name, out bv, out ie);
              bvars.Add(bv);
              substMap.Add(x.Var, ie);
            } else {
              // other forms of LHSs have been ruled out by the resolver (it would be possible to
              // handle them, but it would involve heap-update expressions--the translation would take
              // effort, and it's not certain that the existential would be successful in verification).
              Contract.Assume(false);  // unexpected case
            }
          }
          var bvs = new VariableSeq();
          var typeAntecedent = etran.TrBoundVariables(bvars, bvs);
          var substE = etran.TrExpr(Substitute(s.Expr, null, substMap));
          var ex = new Bpl.ExistsExpr(s.Tok, bvs, BplAnd(typeAntecedent, substE));
          builder.Add(Assert(s.Tok, ex, "cannot establish the existence of LHS values that satisfy the such-that predicate"));
        }
        // End by doing the assume
        builder.Add(new Bpl.AssumeCmd(s.Tok, etran.TrExpr(s.Expr)));
        builder.Add(CaptureState(s.Tok));  // just do one capture state--here, at the very end (that is, don't do one before the assume)

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        // This UpdateStmt can be single-target assignment, a multi-assignment, a call statement, or
        // an array-range update.  Handle the multi-assignment here and handle the others as for .ResolvedStatements.
        var resolved = s.ResolvedStatements;
        if (resolved.Count == 1) {
          TrStmt(resolved[0], builder, locals, etran);
        } else {
          AddComment(builder, s, "update statement");
          var lhss = new List<Expression>();
          foreach (var lhs in s.Lhss) {
            lhss.Add(lhs.Resolved);
          }
          List<AssignToLhs> lhsBuilder;
          List<Bpl.IdentifierExpr> bLhss;
          // note: because we have more than one expression, we always must assign to Boogie locals in a two
          // phase operation. Thus rhssCanAffectPreviouslyKnownExpressions is just true.
          Contract.Assert(1 < lhss.Count);

          Bpl.Expr[] lhsObjs, lhsFields;
          string[] lhsNames;
          ProcessLhss(lhss, true, false, builder, locals, etran, out lhsBuilder, out bLhss, out lhsObjs, out lhsFields, out lhsNames);
          // We know that, because the translation saves to a local variable, that the RHS always need to
          // generate a new local, i.e. bLhss is just all nulls.
          Contract.Assert(Contract.ForAll(bLhss, lhs => lhs == null));
          // This generates the assignments, and gives them to us as finalRhss.
          var finalRhss = ProcessUpdateAssignRhss(lhss, s.Rhss, builder, locals, etran);
          // ProcessLhss has laid down framing conditions and the ProcessUpdateAssignRhss will check subranges (nats),
          // but we need to generate the distinctness condition (two LHS are equal only when the RHS is also
          // equal). We need both the LHS and the RHS to do this, which is why we need to do it here.
          CheckLhssDistinctness(finalRhss, lhss, builder, etran, lhsObjs, lhsFields, lhsNames);
          // Now actually perform the assignments to the LHS.
          for (int i = 0; i < lhss.Count; i++) {
            lhsBuilder[i](finalRhss[i], builder, etran);
          }
          builder.Add(CaptureState(s.Tok));
        }

      } else if (stmt is AssignStmt) {
        AddComment(builder, stmt, "assignment statement");
        AssignStmt s = (AssignStmt)stmt;
        TrAssignment(stmt.Tok, s.Lhs.Resolved, s.Rhs, builder, locals, etran);
      } else if (stmt is VarDecl) {
        AddComment(builder, stmt, "var-declaration statement");
        VarDecl s = (VarDecl)stmt;
        Bpl.Type varType = TrType(s.Type);
        Bpl.Expr wh = GetWhereClause(stmt.Tok, new Bpl.IdentifierExpr(stmt.Tok, s.UniqueName, varType), s.Type, etran);
        Bpl.LocalVariable var = new Bpl.LocalVariable(stmt.Tok, new Bpl.TypedIdent(stmt.Tok, s.UniqueName, varType, wh));
        locals.Add(var);

      } else if (stmt is CallStmt) {
        AddComment(builder, stmt, "call statement");
        TrCallStmt((CallStmt)stmt, builder, locals, etran, null);

      } else if (stmt is BlockStmt) {
        foreach (Statement ss in ((BlockStmt)stmt).Body) {
          TrStmt(ss, builder, locals, etran);
          if (ss.Labels != null) {
            builder.AddLabelCmd("after_" + ss.Labels.Data.UniqueId);
          }
        }
      } else if (stmt is IfStmt) {
        AddComment(builder, stmt, "if statement");
        IfStmt s = (IfStmt)stmt;
        Bpl.Expr guard;
        if (s.Guard == null) {
          guard = null;
        } else {
          TrStmt_CheckWellformed(s.Guard, builder, locals, etran, true);
          guard = etran.TrExpr(s.Guard);
        }
        Bpl.StmtListBuilder b = new Bpl.StmtListBuilder();
        Bpl.StmtList thn = TrStmt2StmtList(b, s.Thn, locals, etran);
        Bpl.StmtList els;
        Bpl.IfCmd elsIf = null;
        if (s.Els == null) {
          b = new Bpl.StmtListBuilder();
          els = b.Collect(s.Tok);
        } else {
          b = new Bpl.StmtListBuilder();
          els = TrStmt2StmtList(b, s.Els, locals, etran);
          if (els.BigBlocks.Count == 1) {
            Bpl.BigBlock bb = els.BigBlocks[0];
            if (bb.LabelName == null && bb.simpleCmds.Length == 0 && bb.ec is Bpl.IfCmd) {
              elsIf = (Bpl.IfCmd)bb.ec;
              els = null;
            }
          }
        }
        builder.Add(new Bpl.IfCmd(stmt.Tok, guard, thn, elsIf, els));

      } else if (stmt is AlternativeStmt) {
        AddComment(builder, stmt, "alternative statement");
        var s = (AlternativeStmt)stmt;
        var elseCase = Assert(s.Tok, Bpl.Expr.False, "alternative cases fail to cover all possibilties");
        TrAlternatives(s.Alternatives, elseCase, null, builder, locals, etran);

      } else if (stmt is WhileStmt) {
        AddComment(builder, stmt, "while statement");
        var s = (WhileStmt)stmt;
        TrLoop(s, s.Guard,
          delegate(Bpl.StmtListBuilder bld, ExpressionTranslator e) { TrStmt(s.Body, bld, locals, e); },
          builder, locals, etran);

      } else if (stmt is AlternativeLoopStmt) {
        AddComment(builder, stmt, "alternative loop statement");
        var s = (AlternativeLoopStmt)stmt;
        var tru = new LiteralExpr(s.Tok, true);
        tru.Type = Type.Bool;  // resolve here
        TrLoop(s, tru,
          delegate(Bpl.StmtListBuilder bld, ExpressionTranslator e) { TrAlternatives(s.Alternatives, null, new Bpl.BreakCmd(s.Tok, null), bld, locals, e); },
          builder, locals, etran);

      } else if (stmt is ParallelStmt) {
        AddComment(builder, stmt, "parallel statement");
        var s = (ParallelStmt)stmt;
        if (s.Kind == ParallelStmt.ParBodyKind.Assign) {
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (AssignStmt)s.S0;
            var definedness = new Bpl.StmtListBuilder();
            var updater = new Bpl.StmtListBuilder();
            TrParallelAssign(s, s0, definedness, updater, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, updater.Collect(s.Tok)));
            builder.Add(CaptureState(stmt.Tok));
          }

        } else if (s.Kind == ParallelStmt.ParBodyKind.Call) {
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (CallStmt)s.S0;
            var definedness = new Bpl.StmtListBuilder();
            var exporter = new Bpl.StmtListBuilder();
            TrParallelCall(s.Tok, s.BoundVars, s.Range, null, s0, definedness, exporter, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
            builder.Add(CaptureState(stmt.Tok));
          }

        } else if (s.Kind == ParallelStmt.ParBodyKind.Proof) {
          var definedness = new Bpl.StmtListBuilder();
          var exporter = new Bpl.StmtListBuilder();
          TrParallelProof(s, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
          builder.Add(CaptureState(stmt.Tok));

        } else {
          Contract.Assert(false);  // unexpected kind
        }

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        TrStmt_CheckWellformed(s.Source, builder, locals, etran, true);
        Bpl.Expr source = etran.TrExpr(s.Source);

        var b = new Bpl.StmtListBuilder();
        b.Add(new Bpl.AssumeCmd(stmt.Tok, Bpl.Expr.False));
        Bpl.StmtList els = b.Collect(stmt.Tok);
        Bpl.IfCmd ifCmd = null;
        foreach (var missingCtor in s.MissingCases) {
          // havoc all bound variables
          b = new Bpl.StmtListBuilder();
          VariableSeq newLocals = new VariableSeq();
          Bpl.Expr r = CtorInvocation(s.Tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Length != 0) {
            Bpl.IdentifierExprSeq havocIds = new Bpl.IdentifierExprSeq();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(s.Tok, havocIds));
          }
          b.Add(Assert(s.Tok, Bpl.Expr.False, "missing case in case statement: " + missingCtor.Name));

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(s.Tok, guard, b.Collect(s.Tok), ifCmd, els);
          els = null;
        }
        for (int i = s.Cases.Count; 0 <= --i; ) {
          var mc = (MatchCaseStmt)s.Cases[i];
          // havoc all bound variables
          b = new Bpl.StmtListBuilder();
          VariableSeq newLocals = new VariableSeq();
          Bpl.Expr r = CtorInvocation(mc, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Length != 0) {
            Bpl.IdentifierExprSeq havocIds = new Bpl.IdentifierExprSeq();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(mc.tok, havocIds));
          }

          // translate the body into b
          foreach (Statement ss in mc.Body) {
            TrStmt(ss, b, locals, etran);
          }

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(mc.tok, guard, b.Collect(mc.tok), ifCmd, els);
          els = null;
        }
        Contract.Assert(ifCmd != null);  // follows from the fact that s.Cases.Count + s.MissingCases.Count != 0.
        builder.Add(ifCmd);

      } else if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement)stmt;
        foreach (var ss in s.ResolvedStatements) {
          TrStmt(ss, builder, locals, etran);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    void TrParallelAssign(ParallelStmt s, AssignStmt s0,
      Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder updater, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      // The statement:
      //   parallel (x,y | Range(x,y)) {
      //     (a)   E(x,y) . f :=  G(x,y);
      //     (b)   A(x,y) [ I0(x,y), I1(x,y), ... ] :=  G(x,y);
      //   }
      // translate into:
      //   if (*) {
      //     // check definedness of Range
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range;
      //     // check definedness of the other expressions
      //     (a)
      //       CheckWellformed( E.F );
      //       check that E.f is in the modifies frame;
      //       CheckWellformed( G );
      //       check nat restrictions for the RHS
      //     (b)
      //       CheckWellformed( A[I0,I1,...] );
      //       check that A[I0,I1,...] is in the modifies frame;
      //       CheckWellformed( G );
      //       check nat restrictions for the RHS
      //     // check for duplicate LHSs
      //     var x', y';
      //     havoc x', y';
      //     assume Range[x,y := x',y'];
      //     assume !(x == x' && y == y');
      //     (a)
      //       assert E(x,y) != E(x',y');
      //     (b)
      //       assert !( A(x,y)==A(x',y') && I0(x,y)==I0(x',y') && I1(x,y)==I1(x',y') && ... );
      //
      //     assume false;
      //
      //   } else {
      //     var oldHeap := $Heap;
      //     havoc $Heap;
      //     assume $HeapSucc(oldHeap, $Heap);
      //     (a)
      //       assume (forall<alpha> o: ref, F: Field alpha ::
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == E(x,y) && F = f));
      //       assume (forall x,y ::  Range ==> $Heap[ E[$Heap:=oldHeap], F] == G[$Heap:=oldHeap]);
      //     (b)
      //       assume (forall<alpha> o: ref, F: Field alpha ::
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == A(x,y) && F = Index(I0,I1,...)));
      //       assume (forall x,y ::  Range ==> $Heap[ A[$Heap:=oldHeap], Index(I0,I1,...)] == G[$Heap:=oldHeap]);
      //   }

      var substMap = SetupBoundVarsAsLocals(s.BoundVars, definedness, locals, etran);
      Expression range = Substitute(s.Range, null, substMap);
      TrStmt_CheckWellformed(range, definedness, locals, etran, false);
      definedness.Add(new Bpl.AssumeCmd(s.Range.tok, etran.TrExpr(range)));

      var lhs = Substitute(s0.Lhs.Resolved, null, substMap);
      TrStmt_CheckWellformed(lhs, definedness, locals, etran, false);
      Bpl.Expr obj, F;
      string description = GetObjFieldDetails(lhs, etran, out obj, out F);
      definedness.Add(Assert(lhs.tok, Bpl.Expr.SelectTok(lhs.tok, etran.TheFrame(lhs.tok), obj, F),
        "assignment may update " + description + " not in the enclosing context's modifies clause"));
      if (s0.Rhs is ExprRhs) {
        var r = (ExprRhs)s0.Rhs;
        var rhs = Substitute(r.Expr, null, substMap);
        TrStmt_CheckWellformed(rhs, definedness, locals, etran, false);
        // check nat restrictions for the RHS
        Type lhsType;
        if (lhs is FieldSelectExpr) {
          lhsType = ((FieldSelectExpr)lhs).Type;
        } else if (lhs is SeqSelectExpr) {
          lhsType = ((SeqSelectExpr)lhs).Type;
        } else {
          lhsType = ((MultiSelectExpr)lhs).Type;
        }
        CheckSubrange(r.Tok, etran.TrExpr(rhs), lhsType, definedness);
      }

      // check for duplicate LHSs
      var substMapPrime = SetupBoundVarsAsLocals(s.BoundVars, definedness, locals, etran);
      var lhsPrime = Substitute(s0.Lhs.Resolved, null, substMapPrime);
      range = Substitute(s.Range, null, substMapPrime);
      definedness.Add(new Bpl.AssumeCmd(range.tok, etran.TrExpr(range)));
      // assume !(x == x' && y == y');
      Bpl.Expr eqs = Bpl.Expr.True;
      foreach (var bv in s.BoundVars) {
        var x = substMap[bv];
        var xPrime = substMapPrime[bv];
        // TODO: in the following line, is the term equality okay, or does it have to include things like Set#Equal sometimes too?
        eqs = BplAnd(eqs, Bpl.Expr.Eq(etran.TrExpr(x), etran.TrExpr(xPrime)));
      }
      definedness.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.Not(eqs)));
      Bpl.Expr objPrime, FPrime;
      GetObjFieldDetails(lhsPrime, etran, out objPrime, out FPrime);
      definedness.Add(Assert(s0.Tok,
        Bpl.Expr.Or(Bpl.Expr.Neq(obj, objPrime), Bpl.Expr.Neq(F, FPrime)),
        "left-hand sides for different parallel-statement bound variables may refer to the same location"));

      definedness.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the translation of the update itself

      Bpl.IdentifierExpr prevHeap = GetPrevHeapVar_IdExpr(s.Tok, locals);
      var prevEtran = new ExpressionTranslator(this, predef, prevHeap);
      updater.Add(Bpl.Cmd.SimpleAssign(s.Tok, prevHeap, etran.HeapExpr));
      updater.Add(new Bpl.HavocCmd(s.Tok, new Bpl.IdentifierExprSeq((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr)));
      updater.Add(new Bpl.AssumeCmd(s.Tok, FunctionCall(s.Tok, BuiltinFunction.HeapSucc, null, prevHeap, etran.HeapExpr)));

      // Here comes:
      //   assume (forall<alpha> o: ref, f: Field alpha ::
      //     $Heap[o,f] = oldHeap[o,f] ||
      //     (exists x,y :: Range(x,y)[$Heap:=oldHeap] &&
      //                    o == Object(x,y)[$Heap:=oldHeap] && f == Field(x,y)[$Heap:=oldHeap]));
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(s.Tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(s.Tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$f", predef.FieldName(s.Tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(s.Tok, fVar);
      Bpl.Expr heapOF = ExpressionTranslator.ReadHeap(s.Tok, etran.HeapExpr, o, f);
      Bpl.Expr oldHeapOF = ExpressionTranslator.ReadHeap(s.Tok, prevHeap, o, f);
      Bpl.VariableSeq xBvars = new Bpl.VariableSeq();
      var xBody = etran.TrBoundVariables(s.BoundVars, xBvars);
      xBody = BplAnd(xBody, prevEtran.TrExpr(s.Range));
      Bpl.Expr xObj, xField;
      GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out xObj, out xField);
      xBody = BplAnd(xBody, Bpl.Expr.Eq(o, xObj));
      xBody = BplAnd(xBody, Bpl.Expr.Eq(f, xField));
      Bpl.Expr xObjField = new Bpl.ExistsExpr(s.Tok, xBvars, xBody);
      Bpl.Expr body = Bpl.Expr.Or(Bpl.Expr.Eq(heapOF, oldHeapOF), xObjField);
      Bpl.Expr qq = new Bpl.ForallExpr(s.Tok, new Bpl.TypeVariableSeq(alpha), new Bpl.VariableSeq(oVar, fVar), body);
      updater.Add(new Bpl.AssumeCmd(s.Tok, qq));

      if (s0.Rhs is ExprRhs) {
        //   assume (forall x,y :: Range(x,y)[$Heap:=oldHeap] ==>
        //                         $Heap[ Object(x,y)[$Heap:=oldHeap], Field(x,y)[$Heap:=oldHeap] ] == G[$Heap:=oldHeap] ));
        xBvars = new Bpl.VariableSeq();
        Bpl.Expr xAnte = etran.TrBoundVariables(s.BoundVars, xBvars);
        xAnte = BplAnd(xAnte, prevEtran.TrExpr(s.Range));
        var rhs = ((ExprRhs)s0.Rhs).Expr;
        var g = prevEtran.TrExpr(rhs);
        GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out xObj, out xField);
        var xHeapOF = ExpressionTranslator.ReadHeap(s.Tok, etran.HeapExpr, xObj, xField);

        Type lhsType;
        if (lhs is FieldSelectExpr) {
          lhsType = ((FieldSelectExpr)lhs).Type;
        } else {
          lhsType = null;
        }
        g = etran.CondApplyBox(rhs.tok, g, rhs.Type, lhsType);

        qq = new Bpl.ForallExpr(s.Tok, xBvars, Bpl.Expr.Imp(xAnte, Bpl.Expr.Eq(xHeapOF, g)));
        updater.Add(new Bpl.AssumeCmd(s.Tok, qq));
      }
    }

    delegate Bpl.Expr ExpressionConverter(Dictionary<IVariable, Expression> substMap, ExpressionTranslator etran);

    void TrParallelCall(IToken tok, List<BoundVar> boundVars, Expression range, ExpressionConverter additionalRange, CallStmt s0,
      Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder exporter, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(range != null);
      // additionalRange is allowed to be null
      Contract.Requires(s0 != null);
      // definedness is allowed to be null
      Contract.Requires(exporter != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      // Translate:
      //   parallel (x,y | Range(x,y)) {
      //     E(x,y) . M( Args(x,y) );
      //   }
      // as:
      //   if (*) {
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range(x,y);
      //     assume additionalRange;
      //     Tr( Call );
      //     assume false;
      //   } else {
      //     initHeap := $Heap;
      //     advance $Heap, Tick;
      //     assume (forall x,y :: (Range(x,y) && additionalRange)[INIT] &&
      //                           ==> Post[old($Heap) := initHeap]( E(x,y)[INIT], Args(x,y)[INIT] ));
      //   }
      // where Post(this,args) is the postcondition of method M and
      // INIT is the substitution [old($Heap),$Heap := old($Heap),initHeap].

      if (definedness != null) {
        // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
        // here (rather than a TrBoundVariables).  However, there is currently no way to apply
        // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
        Bpl.VariableSeq bvars = new Bpl.VariableSeq();
        var ante = etran.TrBoundVariables(boundVars, bvars, true);
        locals.AddRange(bvars);
        var havocIds = new Bpl.IdentifierExprSeq();
        foreach (Bpl.Variable bv in bvars) {
          havocIds.Add(new Bpl.IdentifierExpr(tok, bv));
        }
        definedness.Add(new Bpl.HavocCmd(tok, havocIds));
        definedness.Add(new Bpl.AssumeCmd(tok, ante));
        TrStmt_CheckWellformed(range, definedness, locals, etran, false);
        definedness.Add(new Bpl.AssumeCmd(range.tok, etran.TrExpr(range)));
        if (additionalRange != null) {
          var es = additionalRange(new Dictionary<IVariable, Expression>(), etran);
          definedness.Add(new Bpl.AssumeCmd(es.tok, es));
        }

        TrStmt(s0, definedness, locals, etran);

        definedness.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.False));
      }

      // Now for the other branch, where the postcondition of the call is exported.
      {
        var initHeapVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, "$initHeapParallelStmt#" + otherTmpVarCount, predef.HeapType));
        otherTmpVarCount++;
        locals.Add(initHeapVar);
        var initHeap = new Bpl.IdentifierExpr(tok, initHeapVar);
        var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr);
        // initHeap := $Heap;
        exporter.Add(Bpl.Cmd.SimpleAssign(tok, initHeap, etran.HeapExpr));
        if (s0.Method.Ens.Exists(ens => MentionsOldState(ens.E))) {
          // advance $Heap, Tick;
          exporter.Add(new Bpl.HavocCmd(tok, new Bpl.IdentifierExprSeq((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr, etran.Tick())));
          foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(tok, new List<FrameExpression>(), initEtran, etran, initEtran)) {
            if (tri.IsFree) {
              exporter.Add(new Bpl.AssumeCmd(tok, tri.Expr));
            }
          }
        } else {
          // As an optimization, create the illusion that the $Heap is unchanged by the parallel body.
          exporter.Add(new Bpl.HavocCmd(tok, new Bpl.IdentifierExprSeq(etran.Tick())));
        }

        var bvars = new Bpl.VariableSeq();
        Dictionary<IVariable, Expression> substMap;
        var ante = initEtran.TrBoundVariablesRename(boundVars, bvars, out substMap);
        ante = BplAnd(ante, initEtran.TrExpr(Substitute(range, null, substMap)));
        if (additionalRange != null) {
          ante = BplAnd(ante, additionalRange(substMap, initEtran));
        }

        // Note, in the following, we need to do a bit of a song and dance.  The actual arguements of the
        // call should be translated using "initEtran", whereas the method postcondition should be translated
        // using "callEtran".  To accomplish this, we translate the argument and then tuck the resulting
        // Boogie expressions into BoogieExprWrappers that are used in the DafnyExpr-to-DafnyExpr substitution.
        // TODO
        var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
        Contract.Assert(s0.Method.Ins.Count == s0.Args.Count);
        for (int i = 0; i < s0.Method.Ins.Count; i++) {
          var arg = Substitute(s0.Args[i], null, substMap);  // substitute the renamed bound variables for the declared ones
          argsSubstMap.Add(s0.Method.Ins[i], new BoogieWrapper(initEtran.TrExpr(arg), s0.Args[i].Type));
        }
        var receiver = new BoogieWrapper(initEtran.TrExpr(Substitute(s0.Receiver, null, substMap)), s0.Receiver.Type);
        var callEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, initHeap);
        Bpl.Expr post = Bpl.Expr.True;
        foreach (var ens in s0.Method.Ens) {
          var p = Substitute(ens.E, receiver, argsSubstMap);  // substitute the call's actuals for the method's formals
          post = BplAnd(post, callEtran.TrExpr(p));
        }

        Bpl.Expr qq = new Bpl.ForallExpr(tok, bvars, Bpl.Expr.Imp(ante, post));
        exporter.Add(new Bpl.AssumeCmd(tok, qq));
      }
    }

    void TrParallelProof(ParallelStmt s, Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder exporter, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      // Translate:
      //   parallel (x,y | Range(x,y))
      //     ensures Post(x,y);
      //   {
      //     Body;
      //   }
      // as:
      //   if (*) {
      //     var x,y;
      //     havoc x,y;
      //     CheckWellformed( Range );
      //     assume Range(x,y);
      //     Tr( Body );
      //     CheckWellformed( Post );
      //     assert Post;
      //     assume false;
      //   } else {
      //     initHeap := $Heap;
      //     advance $Heap, Tick;
      //     assume (forall x,y :: Range(x,y)[old($Heap),$Heap := old($Heap),initHeap] ==> Post(x,y));
      //   }

      // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
      // here (rather than a TrBoundVariables).  However, there is currently no way to apply
      // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
      Bpl.VariableSeq bvars = new Bpl.VariableSeq();
      var ante = etran.TrBoundVariables(s.BoundVars, bvars, true);
      locals.AddRange(bvars);
      var havocIds = new Bpl.IdentifierExprSeq();
      foreach (Bpl.Variable bv in bvars) {
        havocIds.Add(new Bpl.IdentifierExpr(s.Tok, bv));
      }
      definedness.Add(new Bpl.HavocCmd(s.Tok, havocIds));
      definedness.Add(new Bpl.AssumeCmd(s.Tok, ante));
      TrStmt_CheckWellformed(s.Range, definedness, locals, etran, false);
      definedness.Add(new Bpl.AssumeCmd(s.Range.tok, etran.TrExpr(s.Range)));

      TrStmt(s.Body, definedness, locals, etran);

      // check that postconditions hold
      foreach (var ens in s.Ens) {
        TrStmt_CheckWellformed(ens.E, definedness, locals, etran, false);
        if (!ens.IsFree) {
          bool splitHappened;  // we actually don't care
          foreach (var split in TrSplitExpr(ens.E, etran, out splitHappened)) {
            if (!split.IsFree) {
              definedness.Add(Assert(split.E.tok, split.E, "possible violation of postcondition of parallel statement"));
            }
          }
        }
      }

      definedness.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the other branch, where the ensures clauses are exported.

      var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$initHeapParallelStmt#" + otherTmpVarCount, predef.HeapType));
      otherTmpVarCount++;
      locals.Add(initHeapVar);
      var initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
      var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr);
      // initHeap := $Heap;
      exporter.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
      if (s.Ens.Exists(ens => MentionsOldState(ens.E))) {
        // advance $Heap;
        exporter.Add(new Bpl.HavocCmd(s.Tok, new Bpl.IdentifierExprSeq((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr, etran.Tick())));
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, new List<FrameExpression>(), initEtran, etran, initEtran)) {
          if (tri.IsFree) {
            exporter.Add(new Bpl.AssumeCmd(s.Tok, tri.Expr));
          }
        }
      } else {
        // As an optimization, create the illusion that the $Heap is unchanged by the parallel body.
        exporter.Add(new Bpl.HavocCmd(s.Tok, new Bpl.IdentifierExprSeq(etran.Tick())));
      }

      bvars = new Bpl.VariableSeq();
      Dictionary<IVariable, Expression> substMap;
      ante = initEtran.TrBoundVariablesRename(s.BoundVars, bvars, out substMap);
      var range = Substitute(s.Range, null, substMap);
      ante = BplAnd(ante, initEtran.TrExpr(range));

      Bpl.Expr post = Bpl.Expr.True;
      foreach (var ens in s.Ens) {
        var p = Substitute(ens.E, null, substMap);
        post = BplAnd(post, etran.TrExpr(p));
      }

      Bpl.Expr qq = Bpl.Expr.Imp(ante, post);
      if (bvars.Length != 0) {
        qq = new Bpl.ForallExpr(s.Tok, bvars, qq);
      }
      exporter.Add(new Bpl.AssumeCmd(s.Tok, qq));
    }

    private string GetObjFieldDetails(Expression lhs, ExpressionTranslator etran, out Bpl.Expr obj, out Bpl.Expr F) {
      string description;
      if (lhs is FieldSelectExpr) {
        var fse = (FieldSelectExpr)lhs;
        obj = etran.TrExpr(fse.Obj);
        F = GetField(fse);
        description = "an object field";
      } else if (lhs is SeqSelectExpr) {
        var sel = (SeqSelectExpr)lhs;
        obj = etran.TrExpr(sel.Seq);
        F = FunctionCall(sel.tok, BuiltinFunction.IndexField, null, etran.TrExpr(sel.E0));
        description = "an array element";
      } else {
        MultiSelectExpr mse = (MultiSelectExpr)lhs;
        obj = etran.TrExpr(mse.Array);
        F = etran.GetArrayIndexFieldName(mse.tok, mse.Indices);
        description = "an array element";
      }
      return description;
    }


    delegate void BodyTranslator(Bpl.StmtListBuilder builder, ExpressionTranslator etran);


    void TrLoop(LoopStmt s, Expression Guard, BodyTranslator bodyTr,
                Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(s != null);
      Contract.Requires(bodyTr != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      int loopId = loopHeapVarCount;
      loopHeapVarCount++;

      // use simple heuristics to create a default decreases clause, if none is given
      bool inferredDecreases;
      List<Expression> theDecreases = LoopDecreasesWithDefault(s.Tok, Guard, s.Decreases.Expressions, out inferredDecreases);

      Bpl.LocalVariable preLoopHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreLoopHeap" + loopId, predef.HeapType));
      locals.Add(preLoopHeapVar);
      Bpl.IdentifierExpr preLoopHeap = new Bpl.IdentifierExpr(s.Tok, preLoopHeapVar);
      ExpressionTranslator etranPreLoop = new ExpressionTranslator(this, predef, preLoopHeap);
      ExpressionTranslator updatedFrameEtran;
      string loopFrameName = "#_Frame#" + loopId;
      if(s.Mod.Expressions != null)
        updatedFrameEtran = new ExpressionTranslator(etran, loopFrameName);
      else
        updatedFrameEtran = etran;

      if (s.Mod.Expressions != null) { // check that the modifies is a strict subset
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, "loop modifies clause may violate context's modifies clause", null);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, loopFrameName);
      }
      builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preLoopHeap, etran.HeapExpr));

      List<Bpl.Expr> initDecr = null;
      if (!Contract.Exists(theDecreases, e => e is WildcardExpr)) {
        initDecr = RecordDecreasesValue(theDecreases, builder, locals, etran, "$decr" + loopId + "$init$");
      }

      // the variable w is used to coordinate the definedness checking of the loop invariant
      Bpl.LocalVariable wVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$w" + loopId, Bpl.Type.Bool));
      Bpl.IdentifierExpr w = new Bpl.IdentifierExpr(s.Tok, wVar);
      locals.Add(wVar);
      // havoc w;
      builder.Add(new Bpl.HavocCmd(s.Tok, new Bpl.IdentifierExprSeq(w)));

      List<Bpl.PredicateCmd> invariants = new List<Bpl.PredicateCmd>();
      Bpl.StmtListBuilder invDefinednessBuilder = new Bpl.StmtListBuilder();
      foreach (MaybeFreeExpression loopInv in s.Invariants) {
        TrStmt_CheckWellformed(loopInv.E, invDefinednessBuilder, locals, etran, false);
        invDefinednessBuilder.Add(new Bpl.AssumeCmd(loopInv.E.tok, etran.TrExpr(loopInv.E)));

        invariants.Add(new Bpl.AssumeCmd(loopInv.E.tok, Bpl.Expr.Imp(w, CanCallAssumption(loopInv.E, etran))));
        if (loopInv.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
          invariants.Add(new Bpl.AssumeCmd(loopInv.E.tok, Bpl.Expr.Imp(w, etran.TrExpr(loopInv.E))));
        } else {
          bool splitHappened;
          var ss = TrSplitExpr(loopInv.E, etran, out splitHappened);
          if (!splitHappened) {
            var wInv = Bpl.Expr.Imp(w, etran.TrExpr(loopInv.E));
            invariants.Add(Assert(loopInv.E.tok, wInv, "loop invariant violation"));
          } else {
            foreach (var split in ss) {
              var wInv = Bpl.Expr.Binary(split.E.tok, BinaryOperator.Opcode.Imp, w, split.E);
              if (split.IsFree) {
                invariants.Add(new Bpl.AssumeCmd(split.E.tok, wInv));
              } else {
                invariants.Add(Assert(split.E.tok, wInv, "loop invariant violation"));  // TODO: it would be fine to have this use {:subsumption 0}
              }
            }
          }
        }
      }
      // check definedness of decreases clause
      // TODO: can this check be omitted if the decreases clause is inferred?
      foreach (Expression e in theDecreases) {
        TrStmt_CheckWellformed(e, invDefinednessBuilder, locals, etran, true);
      }
      // include boilerplate invariants
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, currentMethod.Mod.Expressions, etranPreLoop, etran, etran.Old))
      {
          if (tri.IsFree) {
              invariants.Add(new Bpl.AssumeCmd(s.Tok, tri.Expr));
          }
          else {
              Contract.Assert(tri.ErrorMessage != null);  // follows from BoilerplateTriple invariant
              invariants.Add(Assert(s.Tok, tri.Expr, tri.ErrorMessage));
          }
      }
      // add a free invariant which says that the heap hasn't changed outside of the modifies clause.
      invariants.Add(new Bpl.AssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));

      // include a free invariant that says that all completed iterations so far have only decreased the termination metric
      if (initDecr != null) {
        List<IToken> toks = new List<IToken>();
        List<Type> types = new List<Type>();
        List<Bpl.Expr> decrs = new List<Bpl.Expr>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          types.Add(cce.NonNull(e.Type));
          decrs.Add(etran.TrExpr(e));
        }
        Bpl.Expr decrCheck = DecreasesCheck(toks, types, decrs, initDecr, etran, null, null, true, false);
        invariants.Add(new Bpl.AssumeCmd(s.Tok, decrCheck));
      }

      Bpl.StmtListBuilder loopBodyBuilder = new Bpl.StmtListBuilder();
      // as the first thing inside the loop, generate:  if (!w) { assert IsTotal(inv); assume false; }
      invDefinednessBuilder.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, Bpl.Expr.Not(w), invDefinednessBuilder.Collect(s.Tok), null, null));
      // generate:  assert IsTotal(guard); if (!guard) { break; }
      Bpl.Expr guard = null;
      if (Guard != null) {
        TrStmt_CheckWellformed(Guard, loopBodyBuilder, locals, etran, true);
        guard = Bpl.Expr.Not(etran.TrExpr(Guard));
      }
      Bpl.StmtListBuilder guardBreak = new Bpl.StmtListBuilder();
      guardBreak.Add(new Bpl.BreakCmd(s.Tok, null));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, guard, guardBreak.Collect(s.Tok), null, null));

      loopBodyBuilder.Add(CaptureState(s.Tok, "loop entered"));
      // termination checking
      if (Contract.Exists(theDecreases, e => e is WildcardExpr)) {
        // omit termination checking for this loop
        bodyTr(loopBodyBuilder, updatedFrameEtran);
      } else {
        List<Bpl.Expr> oldBfs = RecordDecreasesValue(theDecreases, loopBodyBuilder, locals, etran, "$decr" + loopId + "$");
        // time for the actual loop body
        bodyTr(loopBodyBuilder, updatedFrameEtran);
        // check definedness of decreases expressions
        List<IToken> toks = new List<IToken>();
        List<Type> types = new List<Type>();
        List<Bpl.Expr> decrs = new List<Bpl.Expr>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          types.Add(cce.NonNull(e.Type));
          decrs.Add(etran.TrExpr(e));
        }
        Bpl.Expr decrCheck = DecreasesCheck(toks, types, decrs, oldBfs, etran, loopBodyBuilder, " at end of loop iteration", false, false);
        string msg;
        if (inferredDecreases) {
          msg = "cannot prove termination; try supplying a decreases clause for the loop";
          if (s is RefinedWhileStmt) {
            msg += " (note that a refined loop does not inherit 'decreases *' from the refined loop)";
          }
        } else {
          msg = "decreases expression might not decrease";
        }
        loopBodyBuilder.Add(Assert(s.Tok, decrCheck, msg));
      }
      // Finally, assume the well-formedness of the invariant (which has been checked once and for all above), so that the check
      // of invariant-maintenance can use the appropriate canCall predicates.
      foreach (MaybeFreeExpression loopInv in s.Invariants) {
        loopBodyBuilder.Add(new Bpl.AssumeCmd(loopInv.E.tok, CanCallAssumption(loopInv.E, etran)));
      }
      Bpl.StmtList body = loopBodyBuilder.Collect(s.Tok);

      builder.Add(new Bpl.WhileCmd(s.Tok, Bpl.Expr.True, invariants, body));
      builder.Add(CaptureState(s.Tok, "loop exit"));
    }

    void TrAlternatives(List<GuardedAlternative> alternatives, Bpl.Cmd elseCase0, Bpl.StructuredCmd elseCase1,
                        Bpl.StmtListBuilder builder, VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(alternatives != null);
      Contract.Requires((elseCase0 != null) == (elseCase1 == null));  // ugly way of doing a type union
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      if (alternatives.Count == 0) {
        if (elseCase0 != null) {
          builder.Add(elseCase0);
        } else {
          builder.Add(elseCase1);
        }
        return;
      }

      // build the negation of the disjunction of all guards (that is, the conjunction of their negations)
      Bpl.Expr noGuard = Bpl.Expr.True;
      foreach (var alternative in alternatives) {
        noGuard = BplAnd(noGuard, Bpl.Expr.Not(etran.TrExpr(alternative.Guard)));
      }

      var b = new Bpl.StmtListBuilder();
      var elseTok = elseCase0 != null ? elseCase0.tok : elseCase1.tok;
      b.Add(new Bpl.AssumeCmd(elseTok, noGuard));
      if (elseCase0 != null) {
        b.Add(elseCase0);
      } else {
        b.Add(elseCase1);
      }
      Bpl.StmtList els = b.Collect(elseTok);

      Bpl.IfCmd elsIf = null;
      for (int i = alternatives.Count; 0 <= --i; ) {
        Contract.Assert(elsIf == null || els == null);  // loop invariant
        var alternative = alternatives[i];
        b = new Bpl.StmtListBuilder();
        TrStmt_CheckWellformed(alternative.Guard, b, locals, etran, true);
        b.Add(new AssumeCmd(alternative.Guard.tok, etran.TrExpr(alternative.Guard)));
        foreach (var s in alternative.Body) {
          TrStmt(s, b, locals, etran);
        }
        Bpl.StmtList thn = b.Collect(alternative.Tok);
        elsIf = new Bpl.IfCmd(alternative.Tok, null, thn, elsIf, els);
        els = null;
      }
      Contract.Assert(elsIf != null && els == null); // follows from loop invariant and the fact that there's more than one alternative
      builder.Add(elsIf);
    }

    void TrCallStmt(CallStmt s, Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran, Bpl.Expr actualReceiver) {
      List<AssignToLhs> lhsBuilders;
      List<Bpl.IdentifierExpr> bLhss;
      Bpl.Expr[] ignore1, ignore2;
      string[] ignore3;
      ProcessLhss(s.Lhs, true, true, builder, locals, etran, out lhsBuilders, out bLhss, out ignore1, out ignore2, out ignore3);
      Contract.Assert(s.Lhs.Count == lhsBuilders.Count);
      Contract.Assert(s.Lhs.Count == bLhss.Count);
      var lhsTypes = new List<Type>();
      for (int i = 0; i < s.Lhs.Count; i++) {
        var lhs = s.Lhs[i];
        lhsTypes.Add(lhs.Type);
        if (bLhss[i] == null) {  // (in the current implementation, the second parameter "true" to ProcessLhss implies that all bLhss[*] will be null)
          // create temporary local and assign it to bLhss[i]
          string nm = "$rhs##" + otherTmpVarCount;
          otherTmpVarCount++;
          var ty = TrType(lhs.Type);
          Bpl.Expr wh = GetWhereClause(lhs.tok, new Bpl.IdentifierExpr(lhs.tok, nm, ty), lhs.Type, etran);
          Bpl.LocalVariable var = new Bpl.LocalVariable(lhs.tok, new Bpl.TypedIdent(lhs.tok, nm, ty, wh));
          locals.Add(var);
          bLhss[i] = new Bpl.IdentifierExpr(lhs.tok, var.Name, ty);
        }
      }
      ProcessCallStmt(s.Tok, s.Receiver, actualReceiver, s.Method, s.Args, bLhss, lhsTypes, builder, locals, etran);
      for (int i = 0; i < lhsBuilders.Count; i++) {
        var lhs = s.Lhs[i];
        Type lhsType = null;
        if (lhs is IdentifierExpr) {
          lhsType = lhs.Type;
        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          lhsType = fse.Field.Type;
        }

        Bpl.Expr bRhs = bLhss[i];  // the RHS (bRhs) of the assignment to the actual call-LHS (lhs) was a LHS (bLhss[i]) in the Boogie call statement
        if (lhsType != null) {
          CheckSubrange(lhs.tok, bRhs, lhsType, builder);
        }
        bRhs = etran.CondApplyBox(lhs.tok, bRhs, lhs.Type, lhsType);

        lhsBuilders[i](bRhs, builder, etran);
      }
      builder.Add(CaptureState(s.Tok));
    }

    void ProcessCallStmt(IToken tok,
      Expression dafnyReceiver, Bpl.Expr bReceiver,
      Method method, List<Expression> Args,
      List<Bpl.IdentifierExpr> Lhss, List<Type> LhsTypes,
      Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {

      Contract.Requires(tok != null);
      Contract.Requires(dafnyReceiver != null || bReceiver != null);
      Contract.Requires(method != null);
      Contract.Requires(cce.NonNullElements(Args));
      Contract.Requires(cce.NonNullElements(Lhss));
      Contract.Requires(cce.NonNullElements(LhsTypes));
      Contract.Requires(method.Outs.Count == Lhss.Count);
      Contract.Requires(method.Outs.Count == LhsTypes.Count);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      Expression receiver = bReceiver == null ? dafnyReceiver : new BoogieWrapper(bReceiver, dafnyReceiver.Type);
      Bpl.ExprSeq ins = new Bpl.ExprSeq();
      if (!method.IsStatic) {
        if (bReceiver == null) {
          if (!(dafnyReceiver is ThisExpr)) {
            CheckNonNull(dafnyReceiver.tok, dafnyReceiver, builder, etran, null);
          }
        }
        ins.Add(etran.TrExpr(receiver));
      }

      // Ideally, the modifies and decreases checks would be done after the precondition check,
      // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
      // store the actual parameters.
      // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
      Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < method.Ins.Count; i++) {
        Formal p = method.Ins[i];
        VarDecl local = new VarDecl(p.tok, p.Name + "#", p.Type, p.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Tok, local.UniqueName);
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(p, ie);
        locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.UniqueName, TrType(local.Type))));

        Bpl.IdentifierExpr param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
        Expression actual = Args[i];
        TrStmt_CheckWellformed(actual, builder, locals, etran, true);
        var bActual = etran.TrExpr(actual);
        CheckSubrange(actual.tok, bActual, p.Type, builder);
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.tok, param, etran.CondApplyBox(actual.tok, bActual, cce.NonNull(actual.Type), method.Ins[i].Type));
        builder.Add(cmd);
        ins.Add(param);
      }

      // Check modifies clause of a subcall is a subset of the current frame.
      CheckFrameSubset(tok, method.Mod.Expressions, receiver, substMap, etran, builder, "call may violate context's modifies clause", null);

      // Check termination
      ModuleDecl module = method.EnclosingClass.Module;
      if (module == currentModule) {
        if (module.CallGraph.GetSCCRepresentative(method) == module.CallGraph.GetSCCRepresentative(currentMethod)) {
          bool contextDecrInferred, calleeDecrInferred;
          List<Expression> contextDecreases = MethodDecreasesWithDefault(currentMethod, out contextDecrInferred);
          List<Expression> calleeDecreases = MethodDecreasesWithDefault(method, out calleeDecrInferred);
          CheckCallTermination(tok, contextDecreases, calleeDecreases, null, receiver, substMap, etran, builder, contextDecrInferred, null);
        }
      }

      // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
      Bpl.IdentifierExprSeq outs = new Bpl.IdentifierExprSeq();
      List<Bpl.IdentifierExpr> tmpOuts = new List<Bpl.IdentifierExpr>();
      for (int i = 0; i < Lhss.Count; i++) {
        var bLhs = Lhss[i];
        if (ExpressionTranslator.ModeledAsBoxType(method.Outs[i].Type) && !ExpressionTranslator.ModeledAsBoxType(LhsTypes[i])) {
          // we need an Unbox
          Bpl.LocalVariable var = new Bpl.LocalVariable(bLhs.tok, new Bpl.TypedIdent(bLhs.tok, "$tmp##" + otherTmpVarCount, predef.BoxType));
          otherTmpVarCount++;
          locals.Add(var);
          Bpl.IdentifierExpr varIdE = new Bpl.IdentifierExpr(bLhs.tok, var.Name, predef.BoxType);
          tmpOuts.Add(varIdE);
          outs.Add(varIdE);
        } else {
          tmpOuts.Add(null);
          outs.Add(bLhs);
        }
      }

      // Make the call
      string name;
      if (RefinementToken.IsInherited(method.tok, currentModule)) {
        name = string.Format("RefinementCall_{0}$${1}", currentModule.Name, method.FullName);
      } else {
        name = method.FullName;
      }
      Bpl.CallCmd call = new Bpl.CallCmd(tok, name, ins, outs);
      builder.Add(call);

      // Unbox results as needed
      for (int i = 0; i < Lhss.Count; i++) {
        Bpl.IdentifierExpr bLhs = Lhss[i];
        Bpl.IdentifierExpr tmpVarIdE = tmpOuts[i];
        if (tmpVarIdE != null) {
          // Instead of an assignment:
          //    e := UnBox(tmpVar);
          // we use:
          //    havoc e; assume e == UnBox(tmpVar);
          // because that will reap the benefits of e's where clause, so that some additional type information will be known about
          // the out-parameter.
          Bpl.Cmd cmd = new Bpl.HavocCmd(bLhs.tok, new IdentifierExprSeq(bLhs));
          builder.Add(cmd);
          cmd = new Bpl.AssumeCmd(bLhs.tok, Bpl.Expr.Eq(bLhs, FunctionCall(bLhs.tok, BuiltinFunction.Unbox, TrType(LhsTypes[i]), tmpVarIdE)));
          builder.Add(cmd);
        }
      }
    }

    static Expression CreateIntLiteral(IToken tok, int n)
    {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      if (0 <= n) {
        Expression lit = new LiteralExpr(tok, n);
        lit.Type = Type.Int;  // resolve here
        return lit;
      } else {
        return CreateIntSub(tok, CreateIntLiteral(tok, 0), CreateIntLiteral(tok, -n));
      }
    }

    static Expression CreateIntSub(IToken tok, Expression e0, Expression e1)
     {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);


      Contract.Requires(e0.Type is IntType && e1.Type is IntType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      BinaryExpr s = new BinaryExpr(tok, BinaryExpr.Opcode.Sub, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;  // resolve here
      s.Type = Type.Int;  // resolve here
      return s;
    }

    static Expression CreateIntITE(IToken tok, Expression test, Expression e0, Expression e1)
     {
      Contract.Requires(tok != null);
      Contract.Requires(test != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(test.Type is BoolType && e0.Type is IntType && e1.Type is IntType);
      Contract.Ensures(Contract.Result<Expression>() != null);

      ITEExpr ite = new ITEExpr(tok, test, e0, e1);
      ite.Type = Type.Int;  // resolve here
      return ite;
    }

    public IEnumerable<Expression> Conjuncts(Expression expr)
     {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type is BoolType);
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

      var bin = expr as BinaryExpr;
      if (bin != null && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return e;
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      }
      yield return expr;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);

      var substMap = new Dictionary<IVariable, Expression>();
      foreach (BoundVar bv in boundVars) {
        VarDecl local = new VarDecl(bv.tok, bv.Name, bv.Type, bv.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Tok, local.UniqueName);
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(bv, ie);
        Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.UniqueName, TrType(local.Type)));
        locals.Add(bvar);
        var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
        builder.Add(new Bpl.HavocCmd(bv.tok, new IdentifierExprSeq(bIe)));
        Bpl.Expr wh = GetWhereClause(bv.tok, bIe, local.Type, etran);
        if (wh != null) {
          builder.Add(new Bpl.AssumeCmd(bv.tok, wh));
        }
      }
      return substMap;
    }

    List<Bpl.Expr> RecordDecreasesValue(List<Expression> decreases, Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran, string varPrefix)
    {
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(varPrefix != null);
      Contract.Requires(builder != null);
      Contract.Requires(decreases != null);
      List<Bpl.Expr> oldBfs = new List<Bpl.Expr>();
      int c = 0;
      foreach (Expression e in decreases) {
        Contract.Assert(e != null);
        Bpl.LocalVariable bfVar = new Bpl.LocalVariable(e.tok, new Bpl.TypedIdent(e.tok, varPrefix + c, TrType(cce.NonNull(e.Type))));
        locals.Add(bfVar);
        Bpl.IdentifierExpr bf = new Bpl.IdentifierExpr(e.tok, bfVar);
        oldBfs.Add(bf);
        // record value of each decreases expression at beginning of the loop iteration
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(e.tok, bf, etran.TrExpr(e));
        builder.Add(cmd);

        c++;
      }
      return oldBfs;
    }

    /// <summary>
    /// Emit to "builder" a check that calleeDecreases is less than contextDecreases.  More precisely,
    /// the check is:
    ///     allowance || (calleeDecreases LESS contextDecreases).
    /// </summary>
    void CheckCallTermination(IToken/*!*/ tok, List<Expression/*!*/>/*!*/ contextDecreases, List<Expression/*!*/>/*!*/ calleeDecreases,
                              Bpl.Expr allowance,
                              Expression receiverReplacement, Dictionary<IVariable,Expression/*!*/>/*!*/ substMap,
                              ExpressionTranslator/*!*/ etran, Bpl.StmtListBuilder/*!*/ builder, bool inferredDecreases, string hint) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(contextDecreases));
      Contract.Requires(cce.NonNullElements(calleeDecreases));
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(etran != null);
      Contract.Requires(builder != null);

      // The interpretation of the given decreases-clause expression tuples is as a lexicographic tuple, extended into
      // an infinite tuple by appending TOP elements.  The TOP element is strictly larger than any other value given
      // by a Dafny expression.  Each Dafny types has its own ordering, and these orderings are combined into a partial
      // order where elements from different Dafny types are incomparable.  Thus, as an optimization below, if two
      // components from different types are compared, the answer is taken to be false.

      int N = Math.Min(contextDecreases.Count, calleeDecreases.Count);
      List<IToken> toks = new List<IToken>();
      List<Type> types = new List<Type>();
      List<Bpl.Expr> callee = new List<Bpl.Expr>();
      List<Bpl.Expr> caller = new List<Bpl.Expr>();
      for (int i = 0; i < N; i++) {
        Expression e0 = Substitute(calleeDecreases[i], receiverReplacement, substMap);
        Expression e1 = contextDecreases[i];
        if (!CompatibleDecreasesTypes(cce.NonNull(e0.Type), cce.NonNull(e1.Type))) {
          N = i;
          break;
        }
        toks.Add(tok);
        types.Add(e0.Type);
        callee.Add(etran.TrExpr(e0));
        caller.Add(etran.TrExpr(e1));
      }
      bool endsWithWinningTopComparison = N == contextDecreases.Count && N < calleeDecreases.Count;
      Bpl.Expr decrExpr = DecreasesCheck(toks, types, callee, caller, etran, builder, "", endsWithWinningTopComparison, false);
      if (allowance != null) {
        decrExpr = Bpl.Expr.Or(allowance, decrExpr);
      }
      string msg = inferredDecreases ? "cannot prove termination; try supplying a decreases clause" : "failure to decrease termination measure";
      if (hint != null) {
        msg += " (" + hint + ")";
      }
      builder.Add(Assert(tok, decrExpr, msg));
    }

    /// <summary>
    /// Returns the expression that says whether or not the decreases function has gone down (if !allowNoChange)
    /// or has gone down or stayed the same (if allowNoChange).
    /// ee0 represents the new values and ee1 represents old values.
    /// If builder is non-null, then the check '0 ATMOST decr' is generated to builder.
    /// </summary>
    Bpl.Expr DecreasesCheck(List<IToken/*!*/>/*!*/ toks, List<Type/*!*/>/*!*/ types, List<Bpl.Expr/*!*/>/*!*/ ee0, List<Bpl.Expr/*!*/>/*!*/ ee1,
                             ExpressionTranslator/*!*/ etran, Bpl.StmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound)
    {
      Contract.Requires(cce.NonNullElements(toks));
      Contract.Requires(cce.NonNullElements(types));
      Contract.Requires(cce.NonNullElements(ee0));
      Contract.Requires(cce.NonNullElements(ee1));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Requires(types.Count == ee0.Count && ee0.Count == ee1.Count);
      Contract.Requires(builder == null || suffixMsg != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      int N = types.Count;

      // compute eq and less for each component of the lexicographic pair
      List<Bpl.Expr> Eq = new List<Bpl.Expr>(N);
      List<Bpl.Expr> Less = new List<Bpl.Expr>(N);
      for (int i = 0; i < N; i++) {
        Bpl.Expr less, atmost, eq;
        ComputeLessEq(toks[i], types[i], ee0[i], ee1[i], out less, out atmost, out eq, etran, includeLowerBound);
        Eq.Add(eq);
        Less.Add(allowNoChange ? atmost : less);
      }
      if (builder != null) {
        // check: 0 <= ee1
        // more precisely, for component k of the lexicographic decreases function, check:
        //   ee0[0] < ee1[0] || ee0[1] < ee1[1] || ... || ee0[k-1] < ee1[k-1] || ee0[k] == ee1[k] || 0 <= ee1[k]
        for (int k = 0; k < N; k++) {
          // we only need to check lower bound for integers--sets, sequences, booleans, references, and datatypes all have natural lower bounds
          Bpl.Expr prefixIsLess = Bpl.Expr.False;
          for (int i = 0; i < k; i++) {
            prefixIsLess = Bpl.Expr.Or(prefixIsLess, Less[i]);
          }
          if (types[k] is IntType) {
            Bpl.Expr bounded = Bpl.Expr.Le(Bpl.Expr.Literal(0), ee1[k]);
            for (int i = 0; i < k; i++) {
              bounded = Bpl.Expr.Or(bounded, Less[i]);
            }
            string component = N == 1 ? "" : " (component " + k + ")";
            Bpl.Cmd cmd = Assert(toks[k], Bpl.Expr.Or(bounded, Eq[k]), "decreases expression" + component + " must be bounded below by 0" + suffixMsg);
            builder.Add(cmd);
          }
        }
      }
      // check: ee0 < ee1 (or ee0 <= ee1, if allowNoChange)
      Bpl.Expr decrCheck = allowNoChange ? Bpl.Expr.True : Bpl.Expr.False;
      for (int i = N; 0 <= --i; ) {
        Bpl.Expr less = Less[i];
        Bpl.Expr eq = Eq[i];
        if (allowNoChange) {
          // decrCheck = atmost && (eq ==> decrCheck)
          decrCheck = Bpl.Expr.And(less, Bpl.Expr.Imp(eq, decrCheck));
        } else {
          // decrCheck = less || (eq && decrCheck)
          decrCheck = Bpl.Expr.Or(less, Bpl.Expr.And(eq, decrCheck));
        }
      }
      return decrCheck;
    }

    bool CompatibleDecreasesTypes(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      if (t is BoolType) {
        return u is BoolType;
      } else if (t is IntType) {
        return u is IntType;
      } else if (t is SetType) {
        return u is SetType;
      } else if (t is SeqType) {
        return u is SeqType;
      } else if (t.IsDatatype) {
        return u.IsDatatype;
      } else if (t.IsRefType) {
        return u.IsRefType;
      } else if (t is MapType) {
        return false;
      } else {
        Contract.Assert(t.IsTypeParameter);
        return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
      }
    }

    void ComputeLessEq(IToken/*!*/ tok, Type/*!*/ ty, Bpl.Expr/*!*/ e0, Bpl.Expr/*!*/ e1, out Bpl.Expr/*!*/ less, out Bpl.Expr/*!*/ atmost, out Bpl.Expr/*!*/ eq,
                       ExpressionTranslator/*!*/ etran, bool includeLowerBound)
     {
      Contract.Requires(tok != null);
      Contract.Requires(ty != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ValueAtReturn(out less)!=null);
      Contract.Ensures(Contract.ValueAtReturn(out atmost)!=null);
      Contract.Ensures(Contract.ValueAtReturn(out eq)!=null);

      if (ty is BoolType) {
        eq = Bpl.Expr.Iff(e0, e1);
        less = Bpl.Expr.And(Bpl.Expr.Not(e0), e1);
        atmost = Bpl.Expr.Imp(e0, e1);
      } else if (ty is IntType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.Lt(e0, e1);
        atmost = Bpl.Expr.Le(e0, e1);
        if (includeLowerBound) {
          less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), e0), less);
          atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), e0), atmost);
        }
      } else if (ty is SetType) {
        eq = FunctionCall(tok, BuiltinFunction.SetEqual, null, e0, e1);
        less = etran.ProperSubset(tok, e0, e1);
        atmost = FunctionCall(tok, BuiltinFunction.SetSubset, null, e0, e1);
      } else if (ty is SeqType) {
        Bpl.Expr b0 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e0);
        Bpl.Expr b1 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e1);
        eq = Bpl.Expr.Eq(b0, b1);
        less = Bpl.Expr.Lt(b0, b1);
        atmost = Bpl.Expr.Le(b0, b1);
      } else if (ty.IsDatatype) {
        Bpl.Expr b0 = FunctionCall(tok, BuiltinFunction.DtRank, null, e0);
        Bpl.Expr b1 = FunctionCall(tok, BuiltinFunction.DtRank, null, e1);
        eq = Bpl.Expr.Eq(b0, b1);
        less = Bpl.Expr.Lt(b0, b1);
        atmost = Bpl.Expr.Le(b0, b1);

      } else {
        // reference type
        Bpl.Expr b0 = Bpl.Expr.Neq(e0, predef.Null);
        Bpl.Expr b1 = Bpl.Expr.Neq(e1, predef.Null);
        eq = Bpl.Expr.Iff(b0, b1);
        less = Bpl.Expr.And(Bpl.Expr.Not(b0), b1);
        atmost = Bpl.Expr.Imp(b0, b1);
      }
    }

    void AddComment(Bpl.StmtListBuilder builder, Statement stmt, string comment) {
      Contract.Requires(builder != null);
      Contract.Requires(stmt != null);
      Contract.Requires(comment != null);
      builder.Add(new Bpl.CommentCmd(string.Format("----- {0} ----- {1}({2},{3})", comment, stmt.Tok.filename, stmt.Tok.line, stmt.Tok.col)));
    }

    Bpl.Expr GetWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran)
    {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      while (true) {
        TypeProxy proxy = type as TypeProxy;
        if (proxy == null) {
          break;
        } else if (proxy.T == null) {
          // Unresolved proxy
          // Omit where clause (in other places, unresolved proxies are treated as a reference type; we could do that here too, but
          // we might as well leave out the where clause altogether).
          return null;
        } else {
          type = proxy.T;
        }
      }

      if (type is NatType) {
        // nat:
        // 0 <= x
        return Bpl.Expr.Le(Bpl.Expr.Literal(0), x);

      } else  if (type is BoolType || type is IntType) {
        // nothing todo

      } else if (type is SetType) {
        SetType st = (SetType)type;
        // (forall t: BoxType :: { x[t] } x[t] ==> Unbox(t)-has-the-expected-type)
        Bpl.BoundVariable tVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$t#" + otherTmpVarCount, predef.BoxType));
        otherTmpVarCount++;
        Bpl.Expr t = new Bpl.IdentifierExpr(tok, tVar);
        Bpl.Expr xSubT = Bpl.Expr.SelectTok(tok, x, t);
        Bpl.Expr unboxT = ExpressionTranslator.ModeledAsBoxType(st.Arg) ? t : FunctionCall(tok, BuiltinFunction.Unbox, TrType(st.Arg), t);

        Bpl.Expr wh = GetWhereClause(tok, unboxT, st.Arg, etran);
        if (wh != null) {
          Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(xSubT));
          return new Bpl.ForallExpr(tok, new Bpl.VariableSeq(tVar), tr, Bpl.Expr.Imp(xSubT, wh));
        }

      } else if (type is MultiSetType) {
        MultiSetType st = (MultiSetType)type;
        // $IsGoodMultiSet(x) && (forall t: BoxType :: { x[t] } 0 < x[t] ==> Unbox(t)-has-the-expected-type)
        Bpl.BoundVariable tVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$t#" + otherTmpVarCount, predef.BoxType));
        otherTmpVarCount++;
        Bpl.Expr t = new Bpl.IdentifierExpr(tok, tVar);
        Bpl.Expr xSubT = Bpl.Expr.Gt(Bpl.Expr.SelectTok(tok, x, t), Bpl.Expr.Literal(0));
        Bpl.Expr unboxT = ExpressionTranslator.ModeledAsBoxType(st.Arg) ? t : FunctionCall(tok, BuiltinFunction.Unbox, TrType(st.Arg), t);

        Bpl.Expr isGoodMultiset = FunctionCall(tok, BuiltinFunction.IsGoodMultiSet, null, x);
        Bpl.Expr wh = GetWhereClause(tok, unboxT, st.Arg, etran);
        if (wh != null) {
          Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(xSubT));
          var q = new Bpl.ForallExpr(tok, new Bpl.VariableSeq(tVar), tr, Bpl.Expr.Imp(xSubT, wh));
          isGoodMultiset = Bpl.Expr.And(isGoodMultiset, q);
        }
        return isGoodMultiset;
      } else if (type is SeqType) {
        SeqType st = (SeqType)type;
        // (forall i: int :: { Seq#Index(x,i) }
        //      0 <= i && i < Seq#Length(x) ==> Unbox(Seq#Index(x,i))-has-the-expected-type)
        Bpl.BoundVariable iVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$i#" + otherTmpVarCount, Bpl.Type.Int));
        otherTmpVarCount++;
        Bpl.Expr i = new Bpl.IdentifierExpr(tok, iVar);
        Bpl.Expr xSubI = FunctionCall(tok, BuiltinFunction.SeqIndex, predef.BoxType, x, i);
        Bpl.Expr unbox = ExpressionTranslator.ModeledAsBoxType(st.Arg) ? xSubI : FunctionCall(tok, BuiltinFunction.Unbox, TrType(st.Arg), xSubI);

        Bpl.Expr c = GetBoolBoxCondition(xSubI, st.Arg);
        Bpl.Expr wh = GetWhereClause(tok, unbox, st.Arg, etran);
        if (wh != null) {
          c = BplAnd(c, wh);
        }
        if (c != Bpl.Expr.True) {
          Bpl.Expr range = InSeqRange(tok, i, x, true, null, false);
          Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(xSubI));
          return new Bpl.ForallExpr(tok, new Bpl.VariableSeq(iVar), tr, Bpl.Expr.Imp(range, c));
        }

      } else if (type is MapType) {
        MapType mt = (MapType)type;
        Bpl.Type maptype = predef.MapType(tok, predef.BoxType, predef.BoxType);
        Bpl.Expr clause = null;
        // (forall i: BoxType :: { Map#Domain(x)[i] }
        //      Map#Domain(x)[i] ==> Unbox(i)-has-the-expected-type)
        // (forall i: BoxType :: { Map#Elements(x)[i] }
        //      Map#Domain(x)[i] ==> Unbox(Map#Elements(x)[i])-has-the-expected-type)
        Bpl.BoundVariable tVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$t#" + otherTmpVarCount, predef.BoxType));
        otherTmpVarCount++;
        Bpl.Expr t = new Bpl.IdentifierExpr(tok, tVar);
        Bpl.Expr xSubT = Bpl.Expr.SelectTok(tok, FunctionCall(tok, BuiltinFunction.MapDomain, maptype, x), t);
        Bpl.Expr xElemSubT = Bpl.Expr.SelectTok(tok, FunctionCall(tok, BuiltinFunction.MapElements, maptype, x), t);
        Bpl.Expr unboxT = ExpressionTranslator.ModeledAsBoxType(mt.Domain) ? t : FunctionCall(tok, BuiltinFunction.Unbox, TrType(mt.Domain), t);
        Bpl.Expr unboxElemT = ExpressionTranslator.ModeledAsBoxType(mt.Domain) ? xElemSubT : FunctionCall(tok, BuiltinFunction.Unbox, TrType(mt.Domain), xElemSubT);

        Bpl.Expr wh = GetWhereClause(tok, unboxT, mt.Domain, etran);
        if (wh != null) {
          Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(xSubT));
          clause = new Bpl.ForallExpr(tok, new Bpl.VariableSeq(tVar), tr, Bpl.Expr.Imp(xSubT, wh));
        }

        Bpl.Expr wh2 = GetWhereClause(tok, xElemSubT, mt.Range, etran);
        if (wh2 != null) {
          Bpl.Trigger tr = new Bpl.Trigger(tok, true, new Bpl.ExprSeq(xElemSubT));
          Bpl.Expr forall = new Bpl.ForallExpr(tok, new Bpl.VariableSeq(tVar), tr, Bpl.Expr.Imp(xSubT, wh));
          if (clause == null) {
            clause = forall;
          } else {
            clause = Bpl.Expr.And(clause, forall);
          }
        }
        return clause;
      } else if (type.IsRefType) {
        // reference type:
        // x == null || ($Heap[x,alloc] && dtype(x) == ...)
        return Bpl.Expr.Or(Bpl.Expr.Eq(x, predef.Null), etran.GoodRef(tok, x, type));

      } else if (type.IsDatatype) {
        UserDefinedType udt = (UserDefinedType)type;

        // DtAlloc(e, heap) && e-has-the-expected-type
        Bpl.Expr alloc = FunctionCall(tok, BuiltinFunction.DtAlloc, null, x, etran.HeapExpr);
        Bpl.Expr goodType = etran.Good_Datatype(tok, x, udt.ResolvedClass, udt.TypeArgs);
        return Bpl.Expr.And(alloc, goodType);

      } else if (type.IsTypeParameter) {
        return FunctionCall(tok, BuiltinFunction.GenericAlloc, null, x, etran.HeapExpr);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }

      return null;
    }

    Bpl.Expr GetBoolBoxCondition(Expr box, Type type) {
      Contract.Requires(box != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (type.Normalize() is BoolType) {
        return FunctionCall(box.tok, BuiltinFunction.IsCanonicalBoolBox, null, box);
      } else {
        return Bpl.Expr.True;
      }
    }

    /// <summary>
    /// "lhs" is expected to be a resolved form of an expression, i.e., not a conrete-syntax expression.
    /// </summary>
    void TrAssignment(IToken tok, Expression lhs, AssignmentRhs rhs,
      Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran)
    {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(!(lhs is ConcreteSyntaxExpression));
      Contract.Requires(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // these were once allowed, but their functionality is now provided by 'parallel' statements
      Contract.Requires(rhs != null);
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      List<AssignToLhs> lhsBuilder;
      List<Bpl.IdentifierExpr> bLhss;
      var lhss = new List<Expression>() { lhs };
      Bpl.Expr[] ignore1, ignore2;
      string[] ignore3;
      ProcessLhss(lhss, rhs.CanAffectPreviouslyKnownExpressions, true, builder, locals, etran,
        out lhsBuilder, out bLhss, out ignore1, out ignore2, out ignore3);
      Contract.Assert(lhsBuilder.Count == 1 && bLhss.Count == 1);  // guaranteed by postcondition of ProcessLhss

      var rhss = new List<AssignmentRhs>() { rhs };
      ProcessRhss(lhsBuilder, bLhss, lhss, rhss, builder, locals, etran);
      builder.Add(CaptureState(tok));
    }

    void ProcessRhss(List<AssignToLhs> lhsBuilder, List<Bpl.IdentifierExpr/*may be null*/> bLhss,
      List<Expression> lhss, List<AssignmentRhs> rhss,
      Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(lhsBuilder != null);
      Contract.Requires(bLhss != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      var finalRhss = new List<Bpl.IdentifierExpr>();
      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        // the following assumes are part of the precondition, really
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

        Type lhsType = null;
        if (lhs is IdentifierExpr) {
          lhsType = lhs.Type;
        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          lhsType = fse.Field.Type;
        }
        var bRhs = TrAssignmentRhs(rhss[i].Tok, bLhss[i], lhsType, rhss[i], lhs.Type, builder, locals, etran);
        if (bRhs != bLhss[i]) {
          finalRhss.Add(bRhs);
        } else {
          // assignment has already been done by by TrAssignmentRhs
          finalRhss.Add(null);
        }
      }
      for (int i = 0; i < lhss.Count; i++) {
        if (finalRhss[i] != null) {
          lhsBuilder[i](finalRhss[i], builder, etran);
        }
      }
    }

    List<Bpl.IdentifierExpr> ProcessUpdateAssignRhss(List<Expression> lhss, List<AssignmentRhs> rhss,
      Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ForAll(Contract.Result<List<Bpl.IdentifierExpr>>(), i => i != null));

      var finalRhss = new List<Bpl.IdentifierExpr>();
      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        // the following assumes are part of the precondition, really
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

        Type lhsType = null;
        if (lhs is IdentifierExpr) {
          lhsType = lhs.Type;
        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          lhsType = fse.Field.Type;
        }
        var bRhs = TrAssignmentRhs(rhss[i].Tok, null, lhsType, rhss[i], lhs.Type, builder, locals, etran);
        finalRhss.Add(bRhs);
      }
      return finalRhss;
    }


    private void CheckLhssDistinctness(List<Bpl.IdentifierExpr> rhs, List<Expression> lhss, StmtListBuilder builder, ExpressionTranslator etran,
      Bpl.Expr[] objs, Bpl.Expr[] fields, string[] names) {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      
      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        IToken tok = lhs.tok;

        if (lhs is IdentifierExpr) {
          for (int j = 0; j < i; j++) {
            var prev = lhss[j] as IdentifierExpr;
            if (prev != null && names[i] == names[j]) {
              builder.Add(Assert(tok, Bpl.Expr.Imp(Bpl.Expr.True, Bpl.Expr.Eq(rhs[i],rhs[j])), string.Format("when left-hand sides {0} and {1} refer to the same location, they must have the same value", j, i)));
            }
          }
        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          // check that this LHS is not the same as any previous LHSs
          for (int j = 0; j < i; j++) {
            var prev = lhss[j] as FieldSelectExpr;
            if (prev != null && prev.Field == fse.Field) {
              builder.Add(Assert(tok, Bpl.Expr.Imp(Bpl.Expr.Eq(objs[j], objs[i]), Bpl.Expr.Eq(rhs[i], rhs[j])), string.Format("when left-hand sides {0} and {1} refer to the same location, they must have the same value", j, i)));
            }
          }
        } else if (lhs is SeqSelectExpr) {
          SeqSelectExpr sel = (SeqSelectExpr)lhs;
          // check that this LHS is not the same as any previous LHSs
          for (int j = 0; j < i; j++) {
            var prev = lhss[j] as SeqSelectExpr;
            if (prev != null) {
              builder.Add(Assert(tok,
                Bpl.Expr.Imp(Bpl.Expr.And(Bpl.Expr.Eq(objs[j], objs[i]), Bpl.Expr.Eq(fields[j], fields[i])), Bpl.Expr.Eq(rhs[i], rhs[j])),
                string.Format("when left-hand sides {0} and {1} may refer to the same location, they must have the same value", j, i)));
            }
          }
        } else {
          MultiSelectExpr mse = (MultiSelectExpr)lhs;
          // check that this LHS is not the same as any previous LHSs
          for (int j = 0; j < i; j++) {
            var prev = lhss[j] as MultiSelectExpr;
            if (prev != null) {
              builder.Add(Assert(tok,
                Bpl.Expr.Imp(Bpl.Expr.And(Bpl.Expr.Eq(objs[j], objs[i]), Bpl.Expr.Eq(fields[j], fields[i])), Bpl.Expr.Eq(rhs[i], rhs[j])),
                string.Format("when left-hand sides {0} and {1} refer to the same location, they must have the same value", j, i)));
            }
          }
          
        }
      }
    }

    delegate void AssignToLhs(Bpl.Expr rhs, Bpl.StmtListBuilder builder, ExpressionTranslator etran);

    /// <summary>
    /// Creates a list of protected Boogie LHSs for the given Dafny LHSs.  Along the way,
    /// builds code that checks that the LHSs are well-defined,
    /// and are allowed by the enclosing modifies clause.
    /// Checks that they denote different locations iff checkDistinctness is true.
    /// </summary>
    void ProcessLhss(List<Expression> lhss, bool rhsCanAffectPreviouslyKnownExpressions, bool checkDistinctness,
      Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran,
      out List<AssignToLhs> lhsBuilders, out List<Bpl.IdentifierExpr/*may be null*/> bLhss,
      out Bpl.Expr[] prevObj, out Bpl.Expr[] prevIndex, out string[] prevNames) {

      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ValueAtReturn(out lhsBuilders).Count == lhss.Count);
      Contract.Ensures(Contract.ValueAtReturn(out lhsBuilders).Count == Contract.ValueAtReturn(out bLhss).Count);

      rhsCanAffectPreviouslyKnownExpressions = rhsCanAffectPreviouslyKnownExpressions || lhss.Count != 1;

      // for each Dafny LHS, build a protected Boogie LHS for the eventual assignment
      lhsBuilders = new List<AssignToLhs>();
      bLhss = new List<Bpl.IdentifierExpr>();
      prevObj = new Bpl.Expr[lhss.Count];
      prevIndex = new Bpl.Expr[lhss.Count];
      prevNames = new string[lhss.Count];
      int i = 0;

      var lhsNameSet = new Dictionary<string, object>();
      
      foreach (var lhs in lhss) {
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        IToken tok = lhs.tok;
        TrStmt_CheckWellformed(lhs, builder, locals, etran, true);

        if (lhs is IdentifierExpr) {
          var ie = (IdentifierExpr)lhs;
          // Note, the resolver does not check for duplicate IdentifierExpr's in LHSs, so do it here.
          if (checkDistinctness) {
            for (int j = 0; j < i; j++) {
              var prev = lhss[j] as IdentifierExpr;
              if (prev != null && ie.Name == prev.Name) {
                builder.Add(Assert(tok, Bpl.Expr.False, string.Format("left-hand sides {0} and {1} refer to the same location", j, i)));
              }
            }
          }
          prevNames[i] = ie.Name;
          var bLhs = (Bpl.IdentifierExpr)etran.TrExpr(lhs);  // TODO: is this cast always justified?
          bLhss.Add(rhsCanAffectPreviouslyKnownExpressions ? null : bLhs);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, Bpl.StmtListBuilder bldr, ExpressionTranslator et) {
            builder.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, rhs));
          });

        } else if (lhs is FieldSelectExpr) {
          var fse = (FieldSelectExpr)lhs;
          Contract.Assert(fse.Field != null);
          var obj = SaveInTemp(etran.TrExpr(fse.Obj), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          prevObj[i] = obj;
          // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj]);
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, GetField(fse)), "assignment may update an object not in the enclosing context's modifies clause"));

          if (checkDistinctness) {
            // check that this LHS is not the same as any previous LHSs
            for (int j = 0; j < i; j++) {
              var prev = lhss[j] as FieldSelectExpr;
              if (prev != null && prev.Field == fse.Field) {
                builder.Add(Assert(tok, Bpl.Expr.Neq(prevObj[j], obj), string.Format("left-hand sides {0} and {1} may refer to the same location", j, i)));
              }
            }
          }

          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, Bpl.StmtListBuilder bldr, ExpressionTranslator et) {
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, new Bpl.IdentifierExpr(tok, GetField(fse.Field)), rhs));
            builder.Add(cmd);
            // assume $IsGoodHeap($Heap);
            builder.Add(AssumeGoodHeap(tok, et));
          });

        } else if (lhs is SeqSelectExpr) {
          SeqSelectExpr sel = (SeqSelectExpr)lhs;
          Contract.Assert(sel.SelectOne);  // array-range assignments are not allowed
          Contract.Assert(sel.Seq.Type != null && sel.Seq.Type.IsArrayType);
          Contract.Assert(sel.E0 != null);
          var obj = SaveInTemp(etran.TrExpr(sel.Seq), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          var fieldName = SaveInTemp(FunctionCall(tok, BuiltinFunction.IndexField, null, etran.TrExpr(sel.E0)), rhsCanAffectPreviouslyKnownExpressions,
            "$index" + i, predef.FieldName(tok, predef.BoxType), builder, locals);
          prevObj[i] = obj;
          prevIndex[i] = fieldName;
          // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj,index]);
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, fieldName), "assignment may update an array element not in the enclosing context's modifies clause"));

          if (checkDistinctness) {
            // check that this LHS is not the same as any previous LHSs
            for (int j = 0; j < i; j++) {
              var prev = lhss[j] as SeqSelectExpr;
              if (prev != null) {
                builder.Add(Assert(tok,
                  Bpl.Expr.Or(Bpl.Expr.Neq(prevObj[j], obj), Bpl.Expr.Neq(prevIndex[j], fieldName)),
                  string.Format("left-hand sides {0} and {1} may refer to the same location", j, i)));
              }
            }
          }
          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, Bpl.StmtListBuilder bldr, ExpressionTranslator et) {
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, fieldName, rhs));
            builder.Add(cmd);
            // assume $IsGoodHeap($Heap);
            builder.Add(AssumeGoodHeap(tok, et));
          });

        } else {
          MultiSelectExpr mse = (MultiSelectExpr)lhs;
          Contract.Assert(mse.Array.Type != null && mse.Array.Type.IsArrayType);

          var obj = SaveInTemp(etran.TrExpr(mse.Array), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          var fieldName = SaveInTemp(etran.GetArrayIndexFieldName(mse.tok, mse.Indices), rhsCanAffectPreviouslyKnownExpressions,
            "$index" + i, predef.FieldName(mse.tok, predef.BoxType), builder, locals);
          prevObj[i] = obj;
          prevIndex[i] = fieldName;
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, fieldName), "assignment may update an array element not in the enclosing context's modifies clause"));

          if (checkDistinctness) {
            // check that this LHS is not the same as any previous LHSs
            for (int j = 0; j < i; j++) {
              var prev = lhss[j] as MultiSelectExpr;
              if (prev != null) {
                builder.Add(Assert(tok,
                  Bpl.Expr.Or(Bpl.Expr.Neq(prevObj[j], obj), Bpl.Expr.Neq(prevIndex[j], fieldName)),
                  string.Format("left-hand sides {0} and {1} may refer to the same location", j, i)));
              }
            }
          }
          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, Bpl.StmtListBuilder bldr, ExpressionTranslator et) {
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, fieldName, rhs));
            builder.Add(cmd);
            // assume $IsGoodHeap($Heap);
            builder.Add(AssumeGoodHeap(tok, etran));
          });
        }

        i++;
      }
    }

    /// <summary>
    /// Generates an assignment of the translation of "rhs" to "bLhs" and then return "bLhs".  If "bLhs" is
    /// passed in as "null", this method will create a new temporary Boogie variable to hold the result.
    /// Before the assignment, the generated code will check that "rhs" obeys any subrange requirements
    /// entailed by "checkSubrangeType".
    /// </summary>
    Bpl.IdentifierExpr TrAssignmentRhs(IToken tok, Bpl.IdentifierExpr bLhs, Type lhsType, AssignmentRhs rhs, Type checkSubrangeType,
                                       Bpl.StmtListBuilder builder, Bpl.VariableSeq locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(rhs != null);
      Contract.Requires(!(rhs is CallRhs));  // calls are handled in a different translation method
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (bLhs == null) {
        var nm = string.Format("$rhs#{0}", otherTmpVarCount);
        otherTmpVarCount++;
        var v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, nm, lhsType == null ? predef.BoxType : TrType(lhsType)));
        locals.Add(v);
        bLhs = new Bpl.IdentifierExpr(tok, v);
      }

      if (rhs is ExprRhs) {
        var e = (ExprRhs)rhs;

        TrStmt_CheckWellformed(e.Expr, builder, locals, etran, true);

        Bpl.Expr bRhs = etran.TrExpr(e.Expr);
        CheckSubrange(tok, bRhs, checkSubrangeType, builder);
        bRhs = etran.CondApplyBox(tok, bRhs, e.Expr.Type, lhsType);

        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, bRhs);
        builder.Add(cmd);
        var ch = e.Expr as UnaryExpr;
        if (ch != null && ch.Op == UnaryExpr.Opcode.SetChoose) {
          // havoc $Tick;
          builder.Add(new Bpl.HavocCmd(ch.tok, new Bpl.IdentifierExprSeq(etran.Tick())));
        }

      } else if (rhs is HavocRhs) {
        builder.Add(new Bpl.HavocCmd(tok, new Bpl.IdentifierExprSeq(bLhs)));
        var isNat = CheckSubrange_Expr(tok, bLhs, checkSubrangeType);
        if (isNat != null) {
          builder.Add(new Bpl.AssumeCmd(tok, isNat));
        }
      } else {
        Contract.Assert(rhs is TypeRhs);  // otherwise, an unexpected AssignmentRhs
        TypeRhs tRhs = (TypeRhs)rhs;

        if (tRhs.ArrayDimensions != null) {
          int i = 0;
          foreach (Expression dim in tRhs.ArrayDimensions) {
            CheckWellformed(dim, new WFOptions(), locals, builder, etran);
            if (tRhs.ArrayDimensions.Count == 1) {
              builder.Add(Assert(tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(dim)),
                tRhs.ArrayDimensions.Count == 1 ? "array size might be negative" : string.Format("array size (dimension {0}) might be negative", i)));
            }
            i++;
          }
        }

        Bpl.IdentifierExpr nw = GetNewVar_IdExpr(tok, locals);
        builder.Add(new Bpl.HavocCmd(tok, new Bpl.IdentifierExprSeq(nw)));
        // assume $nw != null && !$Heap[$nw, alloc] && dtype($nw) == RHS;
        Bpl.Expr nwNotNull = Bpl.Expr.Neq(nw, predef.Null);
        Bpl.Expr rightType;
        if (tRhs.ArrayDimensions != null) {
          // array allocation
          List<Type> typeArgs = new List<Type>();
          typeArgs.Add(tRhs.EType);
          rightType = etran.GoodRef_Ref(tok, nw, new Bpl.IdentifierExpr(tok, "class._System." + BuiltIns.ArrayClassName(tRhs.ArrayDimensions.Count), predef.ClassNameType), typeArgs, true);
        } else if (tRhs.EType is ObjectType) {
          rightType = etran.GoodRef_Ref(tok, nw, new Bpl.IdentifierExpr(tok, "class._System.object", predef.ClassNameType), new List<Type>(), true);
        } else {
          rightType = etran.GoodRef_Class(tok, nw, (UserDefinedType)tRhs.EType, true);
        }
        builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.And(nwNotNull, rightType)));
        if (tRhs.ArrayDimensions != null) {
          int i = 0;
          foreach (Expression dim in tRhs.ArrayDimensions) {
            // assume Array#Length($nw, i) == arraySize;
            Bpl.Expr arrayLength = ArrayLength(tok, nw, tRhs.ArrayDimensions.Count, i);
            builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.Eq(arrayLength, etran.TrExpr(dim))));
            i++;
          }
        }
        // $Heap[$nw, alloc] := true;
        Bpl.Expr alloc = predef.Alloc(tok);
        Bpl.IdentifierExpr heap = (Bpl.IdentifierExpr/*TODO: this cast is dubious*/)etran.HeapExpr;
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, heap, ExpressionTranslator.UpdateHeap(tok, heap, nw, alloc, Bpl.Expr.True));
        builder.Add(cmd);
        // assume $IsGoodHeap($Heap);
        builder.Add(AssumeGoodHeap(tok, etran));
        if (tRhs.InitCall != null) {
          AddComment(builder, tRhs.InitCall, "init call statement");
          TrCallStmt(tRhs.InitCall, builder, locals, etran, nw);
        }
        // bLhs := $nw;
        builder.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, etran.CondApplyBox(tok, nw, tRhs.Type, lhsType)));
      }
      return bLhs;
    }

    void CheckSubrange(IToken tok, Expr bRhs, Type tp, StmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(bRhs != null);
      Contract.Requires(tp != null);
      Contract.Requires(builder != null);

      var isNat = CheckSubrange_Expr(tok, bRhs, tp);
      if (isNat != null) {
        builder.Add(Assert(tok, isNat, "value assigned to a nat must be non-negative"));
      }
    }

    Bpl.Expr CheckSubrange_Expr(IToken tok, Expr bRhs, Type tp) {
      Contract.Requires(tok != null);
      Contract.Requires(bRhs != null);
      Contract.Requires(tp != null);

      if (tp is NatType) {
        return Bpl.Expr.Le(Bpl.Expr.Literal(0), bRhs);
      }
      return null;
    }

    Bpl.AssumeCmd AssumeGoodHeap(IToken tok, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<AssumeCmd>() != null);

      return new Bpl.AssumeCmd(tok, FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr));
    }

    // ----- Expression ---------------------------------------------------------------------------

    /// <summary>
    /// This class gives a way to represent a Boogie translation target as if it were still a Dafny expression.
    /// </summary>
    internal class BoogieWrapper : Expression
    {
      public readonly Bpl.Expr Expr;
      public BoogieWrapper(Bpl.Expr expr, Type dafnyType)
        : base(expr.tok)
      {
        Contract.Requires(expr != null);
        Contract.Requires(dafnyType != null);
        Expr = expr;
        Type = dafnyType;  // resolve immediately
      }
    }

    internal class ExpressionTranslator
    {
      public readonly Bpl.Expr HeapExpr;
      public readonly PredefinedDecls predef;
      public readonly Translator translator;
      public readonly string This;
      public readonly string modifiesFrame; // the name of the context's frame variable.
      readonly Function applyLimited_CurrentFunction;
      public readonly int layerOffset = 0;
      public int Statistics_CustomLayerFunctionCount = 0;
      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(HeapExpr != null);
        Contract.Invariant(predef != null);
        Contract.Invariant(translator != null);
        Contract.Invariant(This != null);
        Contract.Invariant(modifiesFrame != null);
        Contract.Invariant(layerOffset == 0 || layerOffset == 1);
        Contract.Invariant(0 <= Statistics_CustomLayerFunctionCount);
      }

      /// <summary>
      /// This is the most general constructor.  It is private and takes all the parameters.  Whenever
      /// one ExpressionTranslator is constructed from another, unchanged parameters are just copied in.
      /// </summary>
      ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, int layerOffset, string modifiesFrame) {

        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(layerOffset == 0 || layerOffset == 1);
        Contract.Requires(modifiesFrame != null);

        this.translator = translator;
        this.predef = predef;
        this.HeapExpr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimited_CurrentFunction;
        this.layerOffset = layerOffset;
        this.modifiesFrame = modifiesFrame;
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, IToken heapToken)
        : this(translator, predef, new Bpl.IdentifierExpr(heapToken, predef.HeapVarName, predef.HeapType)) {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heapToken != null);
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap)
        : this(translator, predef, heap, "this") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, Bpl.Expr oldHeap)
        : this(translator, predef, heap, "this") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(oldHeap != null);

        var old = new ExpressionTranslator(translator, predef, oldHeap);
        old.oldEtran = old;
        this.oldEtran = old;

      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar)
        : this(translator, predef, heap, thisVar, null, 0, "$_Frame") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(thisVar != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, string modifiesFrame)
        : this(etran.translator, etran.predef, etran.HeapExpr, etran.This, etran.applyLimited_CurrentFunction, etran.layerOffset, modifiesFrame) {
        Contract.Requires(etran != null);
        Contract.Requires(modifiesFrame != null);
      }

      ExpressionTranslator oldEtran;
      public ExpressionTranslator Old {
        get {
          Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

          if (oldEtran == null) {
            oldEtran = new ExpressionTranslator(translator, predef, new Bpl.OldExpr(HeapExpr.tok, HeapExpr), This, applyLimited_CurrentFunction, layerOffset, modifiesFrame);
            oldEtran.oldEtran = oldEtran;
          }
          return oldEtran;
        }
      }

      public bool UsesOldHeap {
        get {
          return HeapExpr is Bpl.OldExpr;
        }
      }

      public ExpressionTranslator LimitedFunctions(Function applyLimited_CurrentFunction) {
        Contract.Requires(applyLimited_CurrentFunction != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return new ExpressionTranslator(translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerOffset, modifiesFrame);
      }

      public ExpressionTranslator LayerOffset(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Requires(layerOffset + offset <= 1);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return new ExpressionTranslator(translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerOffset + offset, modifiesFrame);
      }

      public Bpl.IdentifierExpr TheFrame(IToken tok)
      {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);

        Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "beta");
        Bpl.Type fieldAlpha = predef.FieldName(tok, alpha);
        Bpl.Type ty = new Bpl.MapType(tok, new Bpl.TypeVariableSeq(alpha), new Bpl.TypeSeq(predef.RefType, fieldAlpha), Bpl.Type.Bool);
        return new Bpl.IdentifierExpr(tok, this.modifiesFrame, ty);
      }

      public Bpl.IdentifierExpr Tick() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);

        return new Bpl.IdentifierExpr(Token.NoToken, "$Tick", predef.TickType);
      }

      public Bpl.IdentifierExpr ModuleContextHeight() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$ModuleContextHeight", Bpl.Type.Int);
      }

      public Bpl.IdentifierExpr FunctionContextHeight() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$FunctionContextHeight", Bpl.Type.Int);
      }

      public Bpl.IdentifierExpr InMethodContext() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$InMethodContext", Bpl.Type.Bool);
      }

      public Expression GetSubstitutedBody(LetExpr e) {
        Contract.Requires(e != null);
        var substMap = new Dictionary<IVariable, Expression>();
        Contract.Assert(e.Vars.Count == e.RHSs.Count);  // checked by resolution
        for (int i = 0; i < e.Vars.Count; i++) {
          Expression rhs = e.RHSs[i];
          substMap.Add(e.Vars[i], new BoogieWrapper(TrExpr(rhs), rhs.Type));
        }
        return Translator.Substitute(e.Body, null, substMap);
      }


      /// <summary>
      /// Translates Dafny expression "expr" into a Boogie expression.  If the type of "expr" can be a boolean, then the
      /// token (source location) of the resulting expression is filled in (it wouldn't hurt if the token were always
      /// filled in, but it is really necessary for anything that may show up in a Boogie assert, since that location may
      /// then show up in an error message).
      /// </summary>
      public Bpl.Expr TrExpr(Expression expr)
      {
        Contract.Requires(expr != null);
        Contract.Requires(predef != null);

        if (expr is LiteralExpr) {
          LiteralExpr e = (LiteralExpr)expr;
          if (e.Value == null) {
            return predef.Null;
          } else if (e.Value is bool) {
            return new Bpl.LiteralExpr(e.tok, (bool)e.Value);
          } else if (e.Value is BigInteger) {
            return Bpl.Expr.Literal(Microsoft.Basetypes.BigNum.FromBigInt((BigInteger)e.Value));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
          }

        } else if (expr is ThisExpr) {
          return new Bpl.IdentifierExpr(expr.tok, This, predef.RefType);

        } else if (expr is IdentifierExpr) {
          IdentifierExpr e = (IdentifierExpr)expr;
          return TrVar(expr.tok, cce.NonNull(e.Var));

        } else if (expr is BoogieWrapper) {
          var e = (BoogieWrapper)expr;
          return e.Expr;

        } else if (expr is SetDisplayExpr) {
          SetDisplayExpr e = (SetDisplayExpr)expr;
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.SetEmpty, predef.BoxType);
          foreach (Expression ee in e.Elements) {
            Bpl.Expr ss = BoxIfNecessary(expr.tok, TrExpr(ee), cce.NonNull(ee.Type));
            s = translator.FunctionCall(expr.tok, BuiltinFunction.SetUnionOne, predef.BoxType, s, ss);
          }
          return s;

        } else if (expr is MultiSetDisplayExpr) {
          MultiSetDisplayExpr e = (MultiSetDisplayExpr)expr;
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEmpty, predef.BoxType);
          foreach (Expression ee in e.Elements) {
            Bpl.Expr ss = BoxIfNecessary(expr.tok, TrExpr(ee), cce.NonNull(ee.Type));
            s = translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetUnionOne, predef.BoxType, s, ss);
          }
          return s;

        } else if (expr is SeqDisplayExpr) {
          SeqDisplayExpr e = (SeqDisplayExpr)expr;
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.SeqEmpty, predef.BoxType);
          foreach (Expression ee in e.Elements) {
            Bpl.Expr elt = BoxIfNecessary(expr.tok, TrExpr(ee), cce.NonNull(ee.Type));
            s = translator.FunctionCall(expr.tok, BuiltinFunction.SeqBuild, predef.BoxType, s, elt);
          }
          return s;

        } else if (expr is MapDisplayExpr) {
          MapDisplayExpr e = (MapDisplayExpr)expr;
          Bpl.Type maptype = predef.MapType(expr.tok, predef.BoxType, predef.BoxType);
          Bpl.Expr s = translator.FunctionCall(expr.tok, "Map#Empty", maptype);
          foreach (ExpressionPair p in e.Elements) {
            Bpl.Expr elt = BoxIfNecessary(expr.tok, TrExpr(p.A), cce.NonNull(p.A.Type));
            Bpl.Expr elt2 = BoxIfNecessary(expr.tok, TrExpr(p.B), cce.NonNull(p.B.Type));
            s = translator.FunctionCall(expr.tok, "Map#Build", maptype, s, elt, elt2);
          }
          return s;

        } else if (expr is FieldSelectExpr) {
          FieldSelectExpr e = (FieldSelectExpr)expr;
          Contract.Assert(e.Field != null);
          Bpl.Expr obj = TrExpr(e.Obj);
          Bpl.Expr result;
          if (e.Field.IsMutable) {
            result = ReadHeap(expr.tok, HeapExpr, obj, new Bpl.IdentifierExpr(expr.tok, translator.GetField(e.Field)));
          } else {
            result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(translator.GetReadonlyField(e.Field)), new Bpl.ExprSeq(obj));
          }
          return CondApplyUnbox(expr.tok, result, e.Field.Type, cce.NonNull(expr.Type));

        } else if (expr is SeqSelectExpr) {
          SeqSelectExpr e = (SeqSelectExpr)expr;
          Bpl.Expr seq = TrExpr(e.Seq);
          Type elmtType = null;
          Type domainType = null;
          Contract.Assert(e.Seq.Type != null);  // the expression has been successfully resolved
          if (e.Seq.Type.IsArrayType) {
            domainType = Type.Int;
            elmtType = UserDefinedType.ArrayElementType(e.Seq.Type);
          } else if (e.Seq.Type is SeqType) {
            domainType = Type.Int;
            elmtType = ((SeqType)e.Seq.Type).Arg;
          } else if (e.Seq.Type is MapType) {
            domainType = ((MapType)e.Seq.Type).Domain;
            elmtType = ((MapType)e.Seq.Type).Range;
          } else { Contract.Assert(false); }
          Bpl.Type elType = translator.TrType(elmtType);
          Bpl.Type dType = translator.TrType(domainType);
          Bpl.Expr e0 = e.E0 == null ? null : TrExpr(e.E0);
          Bpl.Expr e1 = e.E1 == null ? null : TrExpr(e.E1);
          if (e.SelectOne) {
            Contract.Assert(e1 == null);
            Bpl.Expr x;
            if (e.Seq.Type.IsArrayType) {
              Bpl.Expr fieldName = translator.FunctionCall(expr.tok, BuiltinFunction.IndexField, null, e0);
              x = ReadHeap(expr.tok, HeapExpr, TrExpr(e.Seq), fieldName);
            } else if(e.Seq.Type is SeqType) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.BoxType, seq, e0);
            } else if (e.Seq.Type is MapType) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.MapElements, predef.MapType(e.tok, predef.BoxType, predef.BoxType), seq);
              x = Bpl.Expr.Select(x, BoxIfNecessary(e.tok, e0, domainType));
            } else { Contract.Assert(false); x = null; }
            if (!ModeledAsBoxType(elmtType)) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, elType, x);
            }
            return x;
          } else {
            if (e.Seq.Type.IsArrayType) {
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqFromArray, elType, HeapExpr, seq);
            }
            if (e1 != null) {
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqTake, elType, seq, e1);
            }
            if (e0 != null) {
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqDrop, elType, seq, e0);
            }
            // if e0 == null && e1 == null, then we have the identity operation seq[..] == seq;
            return seq;
          }

        } else if (expr is SeqUpdateExpr) {
          SeqUpdateExpr e = (SeqUpdateExpr)expr;
          Bpl.Expr seq = TrExpr(e.Seq);
          if (e.Seq.Type is SeqType) {
            Type elmtType = cce.NonNull((SeqType)e.Seq.Type).Arg;
            Bpl.Expr index = TrExpr(e.Index);
            Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), elmtType);
            return translator.FunctionCall(expr.tok, BuiltinFunction.SeqUpdate, predef.BoxType, seq, index, val);
          } else {
            Contract.Assert(e.Seq.Type is MapType);
            MapType mt = (MapType)e.Seq.Type;
            Bpl.Type maptype = predef.MapType(expr.tok, predef.BoxType, predef.BoxType);
            Bpl.Expr index = BoxIfNecessary(expr.tok, TrExpr(e.Index), mt.Domain);
            Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), mt.Range);
            return translator.FunctionCall(expr.tok, "Map#Build", maptype, seq, index, val);
          }
        } else if (expr is MultiSelectExpr) {
          MultiSelectExpr e = (MultiSelectExpr)expr;
          Type elmtType = UserDefinedType.ArrayElementType(e.Array.Type);;
          Bpl.Type elType = translator.TrType(elmtType);

          Bpl.Expr fieldName = GetArrayIndexFieldName(expr.tok, e.Indices);
          Bpl.Expr x = ReadHeap(expr.tok, HeapExpr, TrExpr(e.Array), fieldName);
          if (!ModeledAsBoxType(elmtType)) {
            x = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, elType, x);
          }
          return x;

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          int offsetToUse = e.Function.IsRecursive ? this.layerOffset : 0;
          if (e.Function.IsRecursive) {
            Statistics_CustomLayerFunctionCount++;
          }
          string nm = FunctionName(e.Function, 1 + offsetToUse);
          if (this.applyLimited_CurrentFunction != null && e.Function.IsRecursive) {
            ModuleDecl module = cce.NonNull(e.Function.EnclosingClass).Module;
            if (module == cce.NonNull(applyLimited_CurrentFunction.EnclosingClass).Module) {
              if (module.CallGraph.GetSCCRepresentative(e.Function) == module.CallGraph.GetSCCRepresentative(applyLimited_CurrentFunction)) {
                nm = FunctionName(e.Function, 0 + offsetToUse);
              }
            }
          }
          Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(expr.tok, nm, translator.TrType(cce.NonNull(e.Type)));
          Bpl.ExprSeq args = FunctionInvocationArguments(e);
          Bpl.Expr result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(id), args);
          return CondApplyUnbox(expr.tok, result, e.Function.ResultType, expr.Type);

        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
          Bpl.ExprSeq args = new Bpl.ExprSeq();
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Expression arg = dtv.Arguments[i];
            Type t = dtv.Ctor.Formals[i].Type;
            var bArg = TrExpr(arg);
            args.Add(CondApplyBox(expr.tok, bArg, cce.NonNull(arg.Type), t));
          }
          Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(dtv.tok, dtv.Ctor.FullName, predef.DatatypeType);
          return new Bpl.NAryExpr(dtv.tok, new Bpl.FunctionCall(id), args);

        } else if (expr is OldExpr) {
          OldExpr e = (OldExpr)expr;
          return Old.TrExpr(e.E);

        } else if (expr is MultiSetFormingExpr) {
          MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
          if (e.E.Type is SetType) {
            return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetFromSet, translator.TrType(cce.NonNull((SetType)e.E.Type).Arg), TrExpr(e.E));
          } else if (e.E.Type is SeqType) {
            return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetFromSeq, translator.TrType(cce.NonNull((SeqType)e.E.Type).Arg), TrExpr(e.E));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }


        } else if (expr is FreshExpr) {
          FreshExpr e = (FreshExpr)expr;
          if (e.E.Type is SetType) {
            // generate:  (forall $o: ref :: $o != null && X[Box($o)] ==> !old($Heap)[$o,alloc])
            // TODO: trigger?
            Bpl.Variable oVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$o", predef.RefType));
            Bpl.Expr o = new Bpl.IdentifierExpr(expr.tok, oVar);
            Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
            Bpl.Expr oInSet = TrInSet(expr.tok, o, e.E, ((SetType)e.E.Type).Arg);
            Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, o));
            Bpl.Expr body = Bpl.Expr.Imp(Bpl.Expr.And(oNotNull, oInSet), oIsFresh);
            return new Bpl.ForallExpr(expr.tok, new Bpl.VariableSeq(oVar), body);
          } else if (e.E.Type is SeqType) {
            // generate:  (forall $i: int :: 0 <= $i && $i < Seq#Length(X) && Unbox(Seq#Index(X,$i)) != null ==> !old($Heap)[Seq#Index(X,$i),alloc])
            // TODO: trigger?
            Bpl.Variable iVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$i", Bpl.Type.Int));
            Bpl.Expr i = new Bpl.IdentifierExpr(expr.tok, iVar);
            Bpl.Expr iBounds = translator.InSeqRange(expr.tok, i, TrExpr(e.E), true, null, false);
            Bpl.Expr XsubI = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.RefType, TrExpr(e.E), i);
            Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, XsubI));
            Bpl.Expr xsubiNotNull = Bpl.Expr.Neq(translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, predef.RefType, XsubI), predef.Null);
            Bpl.Expr body = Bpl.Expr.Imp(Bpl.Expr.And(iBounds, xsubiNotNull), oIsFresh);
            return new Bpl.ForallExpr(expr.tok, new Bpl.VariableSeq(iVar), body);
          } else {
            // generate:  x == null || !old($Heap)[x]
            Bpl.Expr oNull = Bpl.Expr.Eq(TrExpr(e.E), predef.Null);
            Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, TrExpr(e.E)));
            return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.Or, oNull, oIsFresh);
          }

        } else if (expr is AllocatedExpr) {
          AllocatedExpr e = (AllocatedExpr)expr;
          Bpl.Expr wh = translator.GetWhereClause(e.tok, TrExpr(e.E), e.E.Type, this);
          return wh == null ? Bpl.Expr.True : wh;

        } else if (expr is UnaryExpr) {
          UnaryExpr e = (UnaryExpr)expr;
          Bpl.Expr arg = TrExpr(e.E);
          switch (e.Op) {
            case UnaryExpr.Opcode.Not:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
            case UnaryExpr.Opcode.SetChoose:
              var x = translator.FunctionCall(expr.tok, BuiltinFunction.SetChoose, predef.BoxType, arg, Tick());
              if (!ModeledAsBoxType(e.Type)) {
                x = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, translator.TrType(e.Type), x);
              }
              return x;
            case UnaryExpr.Opcode.SeqLength:
              if (e.E.Type is SeqType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, arg);
              } else {
                return translator.ArrayLength(expr.tok, arg, 1, 0);
              }
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
          }

        } else if (expr is BinaryExpr) {
          BinaryExpr e = (BinaryExpr)expr;
          Bpl.Expr e0 = TrExpr(e.E0);
          if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet) {
            return TrInSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type));  // let TrInSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet) {
            Bpl.Expr arg = TrInSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type));  // let TrInSet translate e.E1
            return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
            return TrInMultiSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type)); // let TrInMultiSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInMultiSet) {
            Bpl.Expr arg = TrInMultiSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type));  // let TrInMultiSet translate e.E1
            return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
          }
          Bpl.Expr e1 = TrExpr(e.E1);
          BinaryOperator.Opcode bOpcode;
          switch (e.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Iff:
              bOpcode = BinaryOperator.Opcode.Iff; break;
            case BinaryExpr.ResolvedOpcode.Imp:
              bOpcode = BinaryOperator.Opcode.Imp; break;
            case BinaryExpr.ResolvedOpcode.And:
              bOpcode = BinaryOperator.Opcode.And; break;
            case BinaryExpr.ResolvedOpcode.Or:
              bOpcode = BinaryOperator.Opcode.Or; break;

            case BinaryExpr.ResolvedOpcode.EqCommon:
              bOpcode = BinaryOperator.Opcode.Eq; break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
              bOpcode = BinaryOperator.Opcode.Neq; break;

            case BinaryExpr.ResolvedOpcode.Lt:
              bOpcode = BinaryOperator.Opcode.Lt; break;
            case BinaryExpr.ResolvedOpcode.Le:
              bOpcode = BinaryOperator.Opcode.Le; break;
            case BinaryExpr.ResolvedOpcode.Ge:
              bOpcode = BinaryOperator.Opcode.Ge; break;
            case BinaryExpr.ResolvedOpcode.Gt:
              bOpcode = BinaryOperator.Opcode.Gt; break;
            case BinaryExpr.ResolvedOpcode.Add:
              bOpcode = BinaryOperator.Opcode.Add; break;
            case BinaryExpr.ResolvedOpcode.Sub:
              bOpcode = BinaryOperator.Opcode.Sub; break;
            case BinaryExpr.ResolvedOpcode.Mul:
              bOpcode = BinaryOperator.Opcode.Mul; break;
            case BinaryExpr.ResolvedOpcode.Div:
              bOpcode = BinaryOperator.Opcode.Div; break;
            case BinaryExpr.ResolvedOpcode.Mod:
              bOpcode = BinaryOperator.Opcode.Mod; break;

            case BinaryExpr.ResolvedOpcode.SetEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.SetNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperSubset:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e0, e1),
                Bpl.Expr.Not(translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1)));
            case BinaryExpr.ResolvedOpcode.Subset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.Superset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e1, e0);
            case BinaryExpr.ResolvedOpcode.ProperSuperset:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e1, e0),
                Bpl.Expr.Not(translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1)));
            case BinaryExpr.ResolvedOpcode.Disjoint:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetDisjoint, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.InSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.Union:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetUnion, translator.TrType(cce.NonNull((SetType)expr.Type).Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.Intersection:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetIntersection, translator.TrType(cce.NonNull((SetType)expr.Type).Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetDifference, translator.TrType(cce.NonNull((SetType)expr.Type).Arg), e0, e1);

            case BinaryExpr.ResolvedOpcode.MultiSetEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.MapEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MapEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MapNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.MapEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e0, e1),
                Bpl.Expr.Not(translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1)));
            case BinaryExpr.ResolvedOpcode.MultiSubset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSuperset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e1, e0);
            case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e1, e0),
                Bpl.Expr.Not(translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1)));
            case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetDisjoint, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.InMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetUnion, translator.TrType(cce.NonNull((MultiSetType)expr.Type).Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetIntersection, translator.TrType(cce.NonNull((MultiSetType)expr.Type).Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetDifference:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetDifference, translator.TrType(cce.NonNull((MultiSetType)expr.Type).Arg), e0, e1);

            case BinaryExpr.ResolvedOpcode.SeqEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.SeqNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.SeqEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              return ProperPrefix(expr.tok, e0, e1);
            case BinaryExpr.ResolvedOpcode.Prefix:
              {
                Bpl.Expr len0 = translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, e0);
                Bpl.Expr len1 = translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, e1);
                return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                  Bpl.Expr.Le(len0, len1),
                  translator.FunctionCall(expr.tok, BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
              }
            case BinaryExpr.ResolvedOpcode.Concat:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqAppend, translator.TrType(cce.NonNull((SeqType)expr.Type).Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.InSeq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqContains, null, e1,
                       BoxIfNecessary(expr.tok, e0, cce.NonNull(e.E0.Type)));
            case BinaryExpr.ResolvedOpcode.NotInSeq:
              Bpl.Expr arg = translator.FunctionCall(expr.tok, BuiltinFunction.SeqContains, null, e1,
                       BoxIfNecessary(expr.tok, e0, cce.NonNull(e.E0.Type)));
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
            case BinaryExpr.ResolvedOpcode.InMap:
              return Bpl.Expr.Select(translator.FunctionCall(expr.tok, BuiltinFunction.MapDomain, predef.MapType(e.tok, predef.BoxType, predef.BoxType), e1),
                                     BoxIfNecessary(expr.tok, e0, e.E0.Type));
            case BinaryExpr.ResolvedOpcode.NotInMap:
              return Bpl.Expr.Not(Bpl.Expr.Select(translator.FunctionCall(expr.tok, BuiltinFunction.MapDomain, predef.MapType(e.tok, predef.BoxType, predef.BoxType), e1),
                                     BoxIfNecessary(expr.tok, e0, e.E0.Type)));
            case BinaryExpr.ResolvedOpcode.MapDisjoint:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MapDisjoint, null, e0, e1);
              
            case BinaryExpr.ResolvedOpcode.RankLt:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.Lt,
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e0),
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e1));
            case BinaryExpr.ResolvedOpcode.RankGt:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.Gt,
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e0),
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e1));

            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
          }
          return Bpl.Expr.Binary(expr.tok, bOpcode, e0, e1);

        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          return TrExpr(GetSubstitutedBody(e));

        } else if (expr is QuantifierExpr) {
          QuantifierExpr e = (QuantifierExpr)expr;
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          Bpl.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars);
          Bpl.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
          Bpl.Trigger tr = null;
          for (Attributes aa = e.Attributes; aa != null; aa = aa.Prev) {
            if (aa.Name == "trigger") {
              Bpl.ExprSeq tt = new Bpl.ExprSeq();
              foreach (var arg in aa.Args) {
                if (arg.E == null) {
                  Console.WriteLine("Warning: string argument to 'trigger' attribute ignored");
                } else {
                  tt.Add(TrExpr(arg.E));
                }
              }
              tr = new Bpl.Trigger(expr.tok, true, tt, tr);
            }
          }
          var antecedent = typeAntecedent;
          if (e.Range != null) {
            antecedent = Bpl.Expr.And(antecedent, TrExpr(e.Range));
          }
          Bpl.Expr body = TrExpr(e.Term);

          if (e is ForallExpr) {
            return new Bpl.ForallExpr(expr.tok, new Bpl.TypeVariableSeq(), bvars, kv, tr, Bpl.Expr.Imp(antecedent, body));
          } else {
            Contract.Assert(e is ExistsExpr);
            return new Bpl.ExistsExpr(expr.tok, new Bpl.TypeVariableSeq(), bvars, kv, tr, Bpl.Expr.And(antecedent, body));
          }

        } else if (expr is SetComprehension) {
          var e = (SetComprehension)expr;
          // Translate "set xs | R :: T" into "lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))".
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          Bpl.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars);
          Bpl.QKeyValue kv = TrAttributes(e.Attributes, null);

          var yVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$y#" + translator.otherTmpVarCount, predef.BoxType));
          translator.otherTmpVarCount++;
          Bpl.Expr y = new Bpl.IdentifierExpr(expr.tok, yVar);

          var eq = Bpl.Expr.Eq(y, BoxIfNecessary(expr.tok, TrExpr(e.Term), e.Term.Type));
          var ebody = Bpl.Expr.And(translator.BplAnd(typeAntecedent, TrExpr(e.Range)), eq);
          var exst = new Bpl.ExistsExpr(expr.tok, bvars, ebody);

          return new Bpl.LambdaExpr(expr.tok, new Bpl.TypeVariableSeq(), new VariableSeq(yVar), kv, exst);

        } else if (expr is MapComprehension) {
          var e = (MapComprehension)expr;
          // Translate "map x | R :: T" into
          // Map#Glue(lambda y: BoxType :: [unbox(y)/x]R,
          //          lambda y: BoxType :: [unbox(y)/x]T)".
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          var bv = e.BoundVars[0];
          TrBoundVariables(e.BoundVars, bvars);
          
          Bpl.QKeyValue kv = TrAttributes(e.Attributes, null);

          var yVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$y#" + translator.otherTmpVarCount, predef.BoxType));
          translator.otherTmpVarCount++;

          Bpl.Expr typeAntecedent = translator.GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, yVar), bv.Type, this);
          Bpl.Expr unboxy = !ModeledAsBoxType(bv.Type) ? translator.FunctionCall(e.tok, BuiltinFunction.Unbox, translator.TrType(bv.Type), new Bpl.IdentifierExpr(expr.tok, yVar))
            : (Bpl.Expr)(new Bpl.IdentifierExpr(expr.tok, yVar));


          Dictionary<IVariable, Expression> subst = new Dictionary<IVariable,Expression>();
          subst.Add(e.BoundVars[0], new BoogieWrapper(unboxy,e.BoundVars[0].Type));

          var ebody = translator.BplAnd(typeAntecedent ?? Bpl.Expr.True, TrExpr(Substitute(e.Range, null, subst)));
          Bpl.Expr l1 = new Bpl.LambdaExpr(e.tok, new Bpl.TypeVariableSeq(), new VariableSeq(yVar), kv, ebody);
          ebody = TrExpr(Substitute(e.Term, null, subst));
          Bpl.Expr l2 = new Bpl.LambdaExpr(e.tok, new Bpl.TypeVariableSeq(), new VariableSeq(yVar), kv, BoxIfNecessary(expr.tok, ebody, e.Term.Type));

          
          return translator.FunctionCall(e.tok, BuiltinFunction.MapGlue, null, l1, l2);

        } else if (expr is PredicateExpr) {
          var e = (PredicateExpr)expr;
          return TrExpr(e.Body);

        } else if (expr is ITEExpr) {
          ITEExpr e = (ITEExpr)expr;
          Bpl.Expr g = TrExpr(e.Test);
          Bpl.Expr thn = TrExpr(e.Thn);
          Bpl.Expr els = TrExpr(e.Els);
          return new NAryExpr(expr.tok, new IfThenElse(expr.tok), new ExprSeq(g, thn, els));

        } else if (expr is ConcreteSyntaxExpression) {
          var e = (ConcreteSyntaxExpression)expr;
          return TrExpr(e.ResolvedExpression);

        } else if (expr is BoxingCastExpr) {
          BoxingCastExpr e = (BoxingCastExpr)expr;
          return CondApplyBox(e.tok, TrExpr(e.E), e.FromType, e.ToType);

        } else if (expr is UnboxingCastExpr) {
          UnboxingCastExpr e = (UnboxingCastExpr)expr;
          return CondApplyUnbox(e.tok, TrExpr(e.E), e.FromType, e.ToType);

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
        }
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, Bpl.VariableSeq bvars) {
        return TrBoundVariables(boundVars, bvars, false);
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, Bpl.VariableSeq bvars, bool translateAsLocals) {
        Contract.Requires(boundVars != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var tid = new Bpl.TypedIdent(bv.tok, bv.UniqueName, translator.TrType(bv.Type));
          Bpl.Variable bvar;
          if (translateAsLocals) {
            bvar = new Bpl.LocalVariable(bv.tok, tid);
          } else {
            bvar = new Bpl.BoundVariable(bv.tok, tid);
          }
          bvars.Add(bvar);
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, bvar), bv.Type, this);
          if (wh != null) {
            typeAntecedent = translator.BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public Bpl.Expr TrBoundVariablesRename(List<BoundVar> boundVars, Bpl.VariableSeq bvars, out Dictionary<IVariable, Expression> substMap) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);

        substMap = new Dictionary<IVariable, Expression>();
        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var newBoundVar = new BoundVar(bv.tok, bv.Name, bv.Type);
          IdentifierExpr ie = new IdentifierExpr(newBoundVar.tok, newBoundVar.UniqueName);
          ie.Var = newBoundVar; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(bv, ie);
          Bpl.Variable bvar = new Bpl.BoundVariable(newBoundVar.tok, new Bpl.TypedIdent(newBoundVar.tok, newBoundVar.UniqueName, translator.TrType(newBoundVar.Type)));
          bvars.Add(bvar);
          var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, bIe, newBoundVar.Type, this);
          if (wh != null) {
            typeAntecedent = translator.BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public ExprSeq FunctionInvocationArguments(FunctionCallExpr e) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<ExprSeq>() != null);

        Bpl.ExprSeq args = new Bpl.ExprSeq();
        args.Add(HeapExpr);
        if (!e.Function.IsStatic) {
          args.Add(TrExpr(e.Receiver));
        }
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Type t = e.Function.Formals[i].Type;
          args.Add(CondApplyBox(e.tok, TrExpr(ee), cce.NonNull(ee.Type), t));
        }
        return args;
      }

      public Bpl.Expr GetArrayIndexFieldName(IToken tok, List<Expression> indices) {
        Bpl.Expr fieldName = null;
        foreach (Expression idx in indices) {
          Bpl.Expr index = TrExpr(idx);
          if (fieldName == null) {
            // the index in dimension 0:  IndexField(index0)
            fieldName = translator.FunctionCall(tok, BuiltinFunction.IndexField, null, index);
          } else {
            // the index in dimension n:  MultiIndexField(...field name for first n indices..., index_n)
            fieldName = translator.FunctionCall(tok, BuiltinFunction.MultiIndexField, null, fieldName, index);
          }
        }
        return fieldName;
      }

      public Bpl.Expr ProperSubset(IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
        Contract.Requires(tok != null);
        Contract.Requires(e0 != null);
        Contract.Requires(e1 != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        return Bpl.Expr.And(
          translator.FunctionCall(tok, BuiltinFunction.SetSubset, null, e0, e1),
          Bpl.Expr.Not(translator.FunctionCall(tok, BuiltinFunction.SetSubset, null, e1, e0)));
      }
      public Bpl.Expr ProperPrefix(IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
        Contract.Requires(tok != null);
        Contract.Requires(e0 != null);
        Contract.Requires(e1 != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        Bpl.Expr len0 = translator.FunctionCall(tok, BuiltinFunction.SeqLength, null, e0);
        Bpl.Expr len1 = translator.FunctionCall(tok, BuiltinFunction.SeqLength, null, e1);
        return Bpl.Expr.And(
          Bpl.Expr.Lt(len0, len1),
          translator.FunctionCall(tok, BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
      }

      public Bpl.Expr CondApplyBox(IToken tok, Bpl.Expr e, Type fromType, Type toType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        if (!ModeledAsBoxType(fromType) && (toType == null || ModeledAsBoxType(toType))) {
          return translator.FunctionCall(tok, BuiltinFunction.Box, null, e);
        } else {
          return e;
        }
      }

      public Bpl.Expr BoxIfNecessary(IToken tok, Bpl.Expr e, Type fromType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        return CondApplyBox(tok, e, fromType, null);
      }

      public Bpl.Expr CondApplyUnbox(IToken tok, Bpl.Expr e, Type fromType, Type toType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Requires(toType != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        if (ModeledAsBoxType(fromType) && !ModeledAsBoxType(toType)) {
          return translator.FunctionCall(tok, BuiltinFunction.Unbox, translator.TrType(toType), e);
        } else {
          return e;
        }
      }

      public static bool ModeledAsBoxType(Type t) {
        Contract.Requires(t != null);
        while (true) {
          TypeProxy tp = t as TypeProxy;
          if (tp == null) {
            break;
          } else if (tp.T == null) {
            // unresolved proxy
            return false;
          } else {
            t = tp.T;
          }
        }
        return t.IsTypeParameter;
      }

      public Bpl.IdentifierExpr TrVar(IToken tok, IVariable var) {
        Contract.Requires(var != null);
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

        return new Bpl.IdentifierExpr(tok, var.UniqueName, translator.TrType(var.Type));
      }

      public static Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r, Expr f) {
        Contract.Requires(tok != null);
        Contract.Requires(heap != null);
        Contract.Requires(r != null);
        Contract.Requires(f != null);
        Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

        Bpl.ExprSeq args = new Bpl.ExprSeq();
        args.Add(heap);
        args.Add(r);
        args.Add(f);
        Bpl.Type t = (f.Type != null) ? f.Type : f.ShallowType;
        return new Bpl.NAryExpr(tok,
          new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "read", t.AsCtor.Arguments[0])),
          args);
      }

      public static Bpl.NAryExpr UpdateHeap(IToken tok, Expr heap, Expr r, Expr f, Expr v) {
        Contract.Requires(tok != null);
        Contract.Requires(heap != null);
        Contract.Requires(r != null);
        Contract.Requires(f != null);
        Contract.Requires(v != null);
        Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

        Bpl.ExprSeq args = new Bpl.ExprSeq();
        args.Add(heap);
        args.Add(r);
        args.Add(f);
        args.Add(v);
        return new Bpl.NAryExpr(tok,
          new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "update", heap.Type)),
          args);
      }

      /// <summary>
      /// Translate like s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// </summary>
      public Bpl.Expr TrInSet(IToken tok, Bpl.Expr elmt, Expression s, Type elmtType) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);

        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        if (s is BinaryExpr) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Union:
              return Bpl.Expr.Or(TrInSet(tok, elmt, bin.E0, elmtType), TrInSet(tok, elmt, bin.E1, elmtType));
            case BinaryExpr.ResolvedOpcode.Intersection:
              return Bpl.Expr.And(TrInSet(tok, elmt, bin.E0, elmtType), TrInSet(tok, elmt, bin.E1, elmtType));
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return Bpl.Expr.And(TrInSet(tok, elmt, bin.E0, elmtType), Bpl.Expr.Not(TrInSet(tok, elmt, bin.E1, elmtType)));
            default:
              break;
          }
        } else if (s is SetDisplayExpr) {
          SetDisplayExpr disp = (SetDisplayExpr)s;
          Bpl.Expr disjunction = null;
          foreach (Expression a in disp.Elements) {
            Bpl.Expr disjunct = Bpl.Expr.Eq(elmt, TrExpr(a));
            if (disjunction == null) {
              disjunction = disjunct;
            } else {
              disjunction = Bpl.Expr.Or(disjunction, disjunct);
            }
          }
          if (disjunction == null) {
            return Bpl.Expr.False;
          } else {
            return disjunction;
          }
        }
        return Bpl.Expr.SelectTok(tok, TrExpr(s), BoxIfNecessary(tok, elmt, elmtType));
      }

      /// <summary>
      /// Translate like 0 < s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// </summary>
      public Bpl.Expr TrInMultiSet(IToken tok, Bpl.Expr elmt, Expression s, Type elmtType) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);

        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        if (s is BinaryExpr) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return Bpl.Expr.Or(TrInMultiSet(tok, elmt, bin.E0, elmtType), TrInMultiSet(tok, elmt, bin.E1, elmtType));
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return Bpl.Expr.And(TrInMultiSet(tok, elmt, bin.E0, elmtType), TrInMultiSet(tok, elmt, bin.E1, elmtType));
            default:
              break;
          }
        } else if (s is MultiSetDisplayExpr) {
          MultiSetDisplayExpr disp = (MultiSetDisplayExpr)s;
          Bpl.Expr disjunction = null;
          foreach (Expression a in disp.Elements) {
            Bpl.Expr disjunct = Bpl.Expr.Eq(elmt, TrExpr(a));
            if (disjunction == null) {
              disjunction = disjunct;
            } else {
              disjunction = Bpl.Expr.Or(disjunction, disjunct);
            }
          }
          if (disjunction == null) {
            return Bpl.Expr.False;
          } else {
            return disjunction;
          }
        }
        return Bpl.Expr.Gt(Bpl.Expr.SelectTok(tok, TrExpr(s), BoxIfNecessary(tok, elmt, elmtType)), Bpl.Expr.Literal(0));
      }

      public Bpl.QKeyValue TrAttributes(Attributes attrs, string skipThisAttribute) {
        Bpl.QKeyValue kv = null;
        for ( ; attrs != null; attrs = attrs.Prev) {
          if (attrs.Name == skipThisAttribute) { continue; }
          List<object> parms = new List<object>();
          foreach (Attributes.Argument arg in attrs.Args) {
            if (arg.E != null) {
              parms.Add(TrExpr(arg.E));
            } else {
              parms.Add(cce.NonNull(arg.S));
            }
          }
          kv = new Bpl.QKeyValue(Token.NoToken, attrs.Name, parms, kv);
        }
        return kv;
      }

      // --------------- help routines ---------------

      public Bpl.Expr IsAlloced(IToken tok, Bpl.Expr e) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        return ReadHeap(tok, HeapExpr, e, predef.Alloc(tok));
      }

      public Bpl.Expr GoodRef(IToken tok, Bpl.Expr e, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        if (type is UserDefinedType && ((UserDefinedType)type).ResolvedClass != null) {
          // Heap[e, alloc] && dtype(e) == T
          return GoodRef_Class(tok, e, (UserDefinedType)type, false);
        } else {
          // Heap[e, alloc]
          return IsAlloced(tok, e);
        }
      }

      public Bpl.Expr GoodRef_Class(IToken tok, Bpl.Expr e, UserDefinedType type, bool isNew)
       {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Requires(type.ResolvedClass is ClassDecl);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return GoodRef_Ref(tok, e, new Bpl.IdentifierExpr(tok, translator.GetClass(type.ResolvedClass)), type.TypeArgs, isNew);
      }

      public Bpl.Expr GoodRef_Ref(IToken tok, Bpl.Expr e, Bpl.Expr type, List<Type/*!*/>/*!*/ typeArgs, bool isNew) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Requires(cce.NonNullElements(typeArgs));

        // Heap[e, alloc]
        Bpl.Expr r = IsAlloced(tok, e);
        if (isNew) {
          r = Bpl.Expr.Not(r);  // use the conjunct:  !Heap[e, alloc]
        }

        // dtype(e) == C
        Bpl.Expr dtypeFunc = translator.FunctionCall(tok, BuiltinFunction.DynamicType, null, e);
        Bpl.Expr dtype = Bpl.Expr.Eq(dtypeFunc, type);
        r = r == null ? dtype : Bpl.Expr.And(r, dtype);

        // TypeParams(e, #) == T
        int n = 0;
        foreach (Type arg in typeArgs) {
          Bpl.Expr tpFunc = translator.FunctionCall(tok, BuiltinFunction.TypeParams, null, e, Bpl.Expr.Literal(n));
          Bpl.Expr ta = translator.GetTypeExpr(tok, arg);
          if (ta != null) {
            r = Bpl.Expr.And(r, Bpl.Expr.Eq(tpFunc, ta));
          }
          n++;
        }

        return r;
      }

      public Bpl.Expr Good_Datatype(IToken tok, Bpl.Expr e, TopLevelDecl resolvedClass, List<Type> typeArgs) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(resolvedClass != null);
        Contract.Requires(typeArgs != null);

        // DtType(e) == C
        Bpl.Expr dttypeFunc = translator.FunctionCall(tok, BuiltinFunction.DtType, null, e);
        Bpl.Expr r = Bpl.Expr.Eq(dttypeFunc, new Bpl.IdentifierExpr(tok, translator.GetClass(resolvedClass)));

        // DtTypeParams(e, #) == T
        int n = 0;
        foreach (Type arg in typeArgs) {
          Bpl.Expr tpFunc = translator.FunctionCall(tok, BuiltinFunction.DtTypeParams, null, e, Bpl.Expr.Literal(n));
          Bpl.Expr ta = translator.GetTypeExpr(tok, arg);
          if (ta != null) {
            r = Bpl.Expr.And(r, Bpl.Expr.Eq(tpFunc, ta));
          }
          n++;
        }

        return r;
      }
    }

    enum BuiltinFunction
    {
      SetEmpty,
      SetUnionOne,
      SetUnion,
      SetIntersection,
      SetDifference,
      SetEqual,
      SetSubset,
      SetDisjoint,
      SetChoose,

      MultiSetEmpty,
      MultiSetUnionOne,
      MultiSetUnion,
      MultiSetIntersection,
      MultiSetDifference,
      MultiSetEqual,
      MultiSetSubset,
      MultiSetDisjoint,
      MultiSetFromSet,
      MultiSetFromSeq,
      IsGoodMultiSet,

      SeqLength,
      SeqEmpty,
      SeqBuild,
      SeqAppend,
      SeqIndex,
      SeqUpdate,
      SeqContains,
      SeqDrop,
      SeqTake,
      SeqEqual,
      SeqSameUntil,
      SeqFromArray,

      MapDomain,
      MapElements,
      MapEqual,
      MapBuild,
      MapDisjoint,
      MapUnion,
      MapGlue,

      IndexField,
      MultiIndexField,

      Box,
      Unbox,
      IsCanonicalBoolBox,

      IsGoodHeap,
      HeapSucc,

      DynamicType,  // allocated type (of object reference)
      DtType,       // type of datatype value
      TypeParams,   // type parameters of allocated type
      DtTypeParams, // type parameters of datatype
      TypeTuple,
      DeclType,
      FDim,  // field dimension (0 - named, 1 or more - indexed)

      DatatypeCtorId,
      DtRank,
      DtAlloc,

      GenericAlloc
    }

    // The "typeInstantiation" argument is passed in to help construct the result type of the function.
    Bpl.NAryExpr FunctionCall(IToken tok, BuiltinFunction f, Bpl.Type typeInstantiation, params Bpl.Expr[] args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      switch (f) {
        case BuiltinFunction.SetEmpty: {
          Contract.Assert(args.Length == 0);
          Contract.Assert(typeInstantiation != null);
          Bpl.Type resultType = predef.SetType(tok, typeInstantiation);
          return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Set#Empty", resultType, args), resultType);
        }
        case BuiltinFunction.SetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#UnionOne", predef.SetType(tok, typeInstantiation), args);
        case BuiltinFunction.SetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Union", predef.SetType(tok, typeInstantiation), args);
        case BuiltinFunction.SetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Intersection", predef.SetType(tok, typeInstantiation), args);
        case BuiltinFunction.SetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Difference", predef.SetType(tok, typeInstantiation), args);
        case BuiltinFunction.SetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.SetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.SetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.SetChoose:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Choose", typeInstantiation, args);


        case BuiltinFunction.MultiSetEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MultiSetType(tok, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "MultiSet#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.MultiSetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#UnionOne", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Union", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Intersection", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#Difference", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.MultiSetFromSet:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#FromSet", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.MultiSetFromSeq:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "MultiSet#FromSeq", predef.MultiSetType(tok, typeInstantiation), args);
        case BuiltinFunction.IsGoodMultiSet:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodMultiSet", Bpl.Type.Bool, args);
        // avoiding this for now
        /*case BuiltinFunction.SetChoose:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Choose", typeInstantiation, args);*/

        case BuiltinFunction.SeqLength:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Length", Bpl.Type.Int, args);
        case BuiltinFunction.SeqEmpty: {
          Contract.Assert(args.Length == 0);
          Contract.Assert(typeInstantiation != null);
          Bpl.Type resultType = predef.SeqType(tok, typeInstantiation);
          return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Seq#Empty", resultType, args), resultType);
        }
        case BuiltinFunction.SeqBuild:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Build", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqAppend:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Append", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqIndex:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Index", typeInstantiation, args);
        case BuiltinFunction.SeqUpdate:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Update", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqContains:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Contains", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqDrop:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Drop", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqTake:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#Take", predef.SeqType(tok, typeInstantiation), args);
        case BuiltinFunction.SeqEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqSameUntil:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#SameUntil", Bpl.Type.Bool, args);
        case BuiltinFunction.SeqFromArray:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Seq#FromArray", typeInstantiation, args);

        case BuiltinFunction.MapDomain:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "Map#Domain", typeInstantiation, args);
        case BuiltinFunction.MapElements:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "Map#Elements", typeInstantiation, args);
        case BuiltinFunction.MapGlue:
          Contract.Assert(args.Length == 2);
          return FunctionCall(tok, "Map#Glue", predef.MapType(tok, predef.BoxType, predef.BoxType), args);
        case BuiltinFunction.MapEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.MapDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Disjoint", Bpl.Type.Bool, args);
        case BuiltinFunction.MapUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Disjoint", typeInstantiation, args);

        case BuiltinFunction.IndexField:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IndexField", predef.FieldName(tok, predef.BoxType), args);
        case BuiltinFunction.MultiIndexField:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiIndexField", predef.FieldName(tok, predef.BoxType), args);

        case BuiltinFunction.Box:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$Box", predef.BoxType, args);
        case BuiltinFunction.Unbox:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "$Unbox", typeInstantiation, args), typeInstantiation);
        case BuiltinFunction.IsCanonicalBoolBox:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsCanonicalBoolBox", Bpl.Type.Bool, args);

        case BuiltinFunction.IsGoodHeap:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodHeap", Bpl.Type.Bool, args);
        case BuiltinFunction.HeapSucc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$HeapSucc", Bpl.Type.Bool, args);

        case BuiltinFunction.DynamicType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "dtype", predef.ClassNameType, args);
        case BuiltinFunction.DtType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtType", predef.ClassNameType, args);
        case BuiltinFunction.TypeParams:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "TypeParams", predef.ClassNameType, args);
        case BuiltinFunction.DtTypeParams:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtTypeParams", predef.ClassNameType, args);
        case BuiltinFunction.TypeTuple:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "TypeTuple", predef.ClassNameType, args);
        case BuiltinFunction.DeclType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "DeclType", predef.ClassNameType, args);
        case BuiltinFunction.FDim:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "FDim", Bpl.Type.Int, args);

        case BuiltinFunction.DatatypeCtorId:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DatatypeCtorId", predef.DtCtorId, args);
        case BuiltinFunction.DtRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtRank", Bpl.Type.Int, args);
        case BuiltinFunction.DtAlloc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtAlloc", Bpl.Type.Bool, args);

        case BuiltinFunction.GenericAlloc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "GenericAlloc", Bpl.Type.Bool, args);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected built-in function
      }
    }

    Bpl.NAryExpr FunctionCall(IToken tok, string function, Bpl.Type returnType, params Bpl.Expr[] args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), new Bpl.ExprSeq(args));
    }

    Bpl.NAryExpr FunctionCall(IToken tok, string function, Bpl.Type returnType, List<Bpl.Expr> args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(returnType != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      Bpl.ExprSeq aa = new Bpl.ExprSeq();
      foreach (Bpl.Expr arg in args) {
        aa.Add(arg);
      }
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), aa);
    }

    Bpl.Expr ArrayLength(IToken tok, Bpl.Expr arr, int totalDims, int dim) {
      Contract.Requires(tok != null);
      Contract.Requires(arr != null);
      Contract.Requires(1 <= totalDims);
      Contract.Requires(0 <= dim && dim < totalDims);

      string name = "_System." + BuiltIns.ArrayClassName(totalDims) + ".Length";
      if (totalDims != 1) {
        name += dim;
      }
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, name, Bpl.Type.Int)), new Bpl.ExprSeq(arr));
    }

    public class SplitExprInfo
    {
      public readonly bool IsFree;
      public readonly Bpl.Expr E;
      public SplitExprInfo(bool isFree, Bpl.Expr e) {
        Contract.Requires(e != null);
        IsFree = isFree;
        E = e;
      }
    }

    internal List<SplitExprInfo/*!*/>/*!*/ TrSplitExpr(Expression expr, ExpressionTranslator etran, out bool splitHappened) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, etran);
      return splits;
    }

    /// <summary>
    /// Tries to split the expression into tactical conjuncts (if "position") or disjuncts (if "!position").
    /// If a (necessarily boolean) function call appears as a top-level conjunct, then inline the function if
    /// if it declared in the current module and its height is less than "heightLimit".
    /// </summary>
    internal bool TrSplitExpr(Expression expr, List<SplitExprInfo/*!*/>/*!*/ splits, bool position, int heightLimit, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type is BoolType || (expr is BoxingCastExpr && ((BoxingCastExpr)expr).E.Type is BoolType));
      Contract.Requires(splits != null);
      Contract.Requires(etran != null);

      if (expr is BoxingCastExpr) {
        var bce = (BoxingCastExpr)expr;
        var ss = new List<SplitExprInfo>();
        if (TrSplitExpr(bce.E, ss, position, heightLimit, etran)) {
          foreach (var s in ss) {
            splits.Add(new SplitExprInfo(s.IsFree, etran.CondApplyBox(s.E.tok, s.E, bce.FromType, bce.ToType)));
          }
          return true;
        }

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return TrSplitExpr(e.ResolvedExpression, splits, position, heightLimit, etran);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return TrSplitExpr(etran.GetSubstitutedBody(e), splits, position, heightLimit, etran);

      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        if (e.Op == UnaryExpr.Opcode.Not) {
          var ss = new List<SplitExprInfo>();
          if (TrSplitExpr(e.E, ss, !position, heightLimit, etran)) {
            foreach (var s in ss) {
              splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Unary(s.E.tok, UnaryOperator.Opcode.Not, s.E)));
            }
            return true;
          }
        }

      } else if (expr is BinaryExpr) {
        var bin = (BinaryExpr)expr;
        if (position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, etran);
          return true;

        } else  if (!position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, etran);
          return true;

        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
          // non-conditionally split these, so we get the source location to point to a subexpression
          if (position) {
            var lhs = etran.TrExpr(bin.E0);
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E1, ss, position, heightLimit, etran);
            foreach (var s in ss) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, lhs, s.E)));
            }
          } else {
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E0, ss, !position, heightLimit, etran);
            var lhs = etran.TrExpr(bin.E1);
            foreach (var s in ss) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, lhs)));
            }
          }
          return true;
        }

      } else if (expr is ITEExpr) {
        var ite = (ITEExpr)expr;

        var ssThen = new List<SplitExprInfo>();
        var ssElse = new List<SplitExprInfo>();
        // Note: The following lines intentionally uses | instead of ||, because we need both calls to TrSplitExpr
        if (TrSplitExpr(ite.Thn, ssThen, position, heightLimit, etran) | TrSplitExpr(ite.Els, ssElse, position, heightLimit, etran)) {
          var op = position ? BinaryOperator.Opcode.Imp : BinaryOperator.Opcode.And;
          var test = etran.TrExpr(ite.Test);
          foreach (var s in ssThen) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, op, test, s.E)));
          }

          var negatedTest = Bpl.Expr.Not(test);
          foreach (var s in ssElse) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, op, negatedTest, s.E)));
          }

          return true;
        }

      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        // For a predicate expression in split position, the predicate can be used as an assumption.  Unfortunately,
        // this assumption is not generated in non-split positions (because I don't know how.)
        // So, treat "assert/assume P; E" like "P ==> E".
        if (position) {
          var guard = etran.TrExpr(e.Guard);
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.Body, ss, position, heightLimit, etran);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, guard, s.E)));
          }
        } else {
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.Guard, ss, !position, heightLimit, etran);
          var rhs = etran.TrExpr(e.Body);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.IsFree, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
          }
        }
        return true;

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return TrSplitExpr(e.E, splits, position, heightLimit, etran.Old);

      } else if (expr is FunctionCallExpr) {
        if (position) {
          var fexp = (FunctionCallExpr)expr;
          var f = fexp.Function;
          Contract.Assert(f != null);  // filled in during resolution
          var module = f.EnclosingClass.Module;
          var functionHeight = module.CallGraph.GetSCCRepresentativeId(f);

          if (module == currentModule && functionHeight < heightLimit) {
            if (f.Body != null && !(f.Body.Resolved is MatchExpr)) {
              // inline this body
              Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
              Contract.Assert(fexp.Args.Count == f.Formals.Count);
              for (int i = 0; i < f.Formals.Count; i++) {
                Formal p = f.Formals[i];
                Expression arg = fexp.Args[i];
                arg = new BoxingCastExpr(arg, cce.NonNull(arg.Type), p.Type);
                arg.Type = p.Type;  // resolve here
                substMap.Add(p, arg);
              }
              Expression body = Substitute(f.Body, fexp.Receiver, substMap);

              // Produce, for a "body" split into b0, b1, b2:
              //     free F#canCall(args) && F(args) && (b0 && b1 && b2)
              //     checked F#canCall(args) ==> F(args) || b0
              //     checked F#canCall(args) ==> F(args) || b1
              //     checked F#canCall(args) ==> F(args) || b2
              // Note that "body" does not contain limited calls.

              // F#canCall(args)
              Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, f.FullName + "#canCall", Bpl.Type.Bool);
              ExprSeq args = etran.FunctionInvocationArguments(fexp);
              Bpl.Expr canCall = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);

              // F(args)
              Bpl.Expr fargs = etran.TrExpr(fexp);

              // body
              Bpl.Expr trBody = etran.TrExpr(body);
              trBody = etran.CondApplyUnbox(trBody.tok, trBody, f.ResultType, expr.Type);

              // here goes the free piece:
              splits.Add(new SplitExprInfo(true, Bpl.Expr.Binary(trBody.tok, BinaryOperator.Opcode.And, canCall, BplAnd(fargs, trBody))));

              // recurse on body
              var ss = new List<SplitExprInfo>();
              TrSplitExpr(body, ss, position, functionHeight, etran);
              foreach (var s in ss) {
                var unboxedConjunct = etran.CondApplyUnbox(s.E.tok, s.E, f.ResultType, expr.Type);
                var bodyOrConjunct = Bpl.Expr.Or(fargs, unboxedConjunct);
                var p = Bpl.Expr.Binary(new NestedToken(fexp.tok, s.E.tok), BinaryOperator.Opcode.Imp, canCall, bodyOrConjunct);
                splits.Add(new SplitExprInfo(s.IsFree, p));
              }

              return true;
            }
          }
        }

      } else if ((position && expr is ForallExpr) || (!position && expr is ExistsExpr)) {
        var e = (QuantifierExpr)expr;
        var inductionVariables = ApplyInduction(e);
        if (2 <= DafnyOptions.O.Induction && inductionVariables.Count != 0) {
          // From the given quantifier (forall n :: P(n)), generate the seemingly weaker proof obligation
          //   (forall n :: (forall k :: k < n ==> P(k)) ==> P(n))
          // For an existential (exists n :: P(n)), it is
          //   (exists n :: (forall k :: k < n ==> !P(k)) && P(n))
          //    ^^^^^^                             ^      ^^        <--- note these 3 differences
          var kvars = new List<BoundVar>();
          var kk = new List<Bpl.Expr>();
          var nn = new List<Bpl.Expr>();
          var toks = new List<IToken>();
          var types = new List<Type>();
          var substMap = new Dictionary<IVariable, Expression>();
          foreach (var n in inductionVariables) {
            toks.Add(n.tok);
            types.Add(n.Type);
            BoundVar k = new BoundVar(n.tok, n.Name + "$ih#" + otherTmpVarCount, n.Type);
            otherTmpVarCount++;
            kvars.Add(k);

            IdentifierExpr ieK = new IdentifierExpr(k.tok, k.UniqueName);
            ieK.Var = k; ieK.Type = ieK.Var.Type;  // resolve it here
            kk.Add(etran.TrExpr(ieK));

            IdentifierExpr ieN = new IdentifierExpr(n.tok, n.UniqueName);
            ieN.Var = n; ieN.Type = ieN.Var.Type;  // resolve it here
            nn.Add(etran.TrExpr(ieN));

            substMap.Add(n, ieK);
          }
          Expression bodyK = Substitute(e.LogicalBody(), null, substMap);

          Bpl.Expr less = DecreasesCheck(toks, types, kk, nn, etran, null, null, false, true);

          Bpl.Expr ihBody = etran.TrExpr(bodyK);
          if (!position) {
            ihBody = Bpl.Expr.Not(ihBody);
          }
          ihBody = Bpl.Expr.Imp(less, ihBody);
          Bpl.VariableSeq bvars = new Bpl.VariableSeq();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(kvars, bvars);
          Bpl.Expr ih = new Bpl.ForallExpr(expr.tok, bvars, Bpl.Expr.Imp(typeAntecedent, ihBody));

          // More precisely now:
          //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case0(n)   ==> P(n))
          //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case...(n) ==> P(n))
          // or similar for existentials.
          var caseProduct = new List<Bpl.Expr>() { new Bpl.LiteralExpr(expr.tok, true) };  // make sure to include the correct token information
          var i = 0;
          foreach (var n in inductionVariables) {
            var newCases = new List<Bpl.Expr>();
            foreach (var kase in InductionCases(n.Type, nn[i], etran)) {
              foreach (var cs in caseProduct) {
                if (kase != Bpl.Expr.True) {  // if there's no case, don't add anything to the token
                  newCases.Add(Bpl.Expr.Binary(new NestedToken(cs.tok, kase.tok), Bpl.BinaryOperator.Opcode.And, cs, kase));
                } else {
                  newCases.Add(cs);
                }
              }
            }
            caseProduct = newCases;
            i++;
          }
          bvars = new Bpl.VariableSeq();
          typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars);
          foreach (var kase in caseProduct) {
            var ante = BplAnd(BplAnd(typeAntecedent, ih), kase);
            var bdy = etran.LayerOffset(1).TrExpr(e.LogicalBody());
            Bpl.Expr q;
            if (position) {
              q = new Bpl.ForallExpr(kase.tok, bvars, Bpl.Expr.Imp(ante, bdy));
            } else {
              q = new Bpl.ExistsExpr(kase.tok, bvars, Bpl.Expr.And(ante, bdy));
            }
            splits.Add(new SplitExprInfo(false, q));
          }

          // Finally, assume the original quantifier (forall/exists n :: P(n))
          splits.Add(new SplitExprInfo(true, etran.TrExpr(expr)));
          return true;
        }
      }

      Bpl.Expr translatedExpression;
      bool splitHappened;
      if ((position && expr is ExistsExpr) || (!position && expr is ForallExpr)) {
        translatedExpression = etran.TrExpr(expr);
        splitHappened = false;
      } else {
        etran = etran.LayerOffset(1);
        translatedExpression = etran.TrExpr(expr);
        splitHappened = etran.Statistics_CustomLayerFunctionCount != 0;  // return true if the LayerOffset(1) came into play
      }
      if (RefinementToken.IsInherited(expr.tok, currentModule) && RefinementTransformer.ContainsChange(expr, currentModule)) {
        // If "expr" contains a subexpression that has changed from the inherited expression, we'll destructively
        // change the token of the translated expression to make it look like it's not inherited.  This will cause "e" to
        // be verified again in the refining module.
        translatedExpression.tok = new ForceCheckToken(expr.tok);
        splitHappened = true;  // count this as a split, so this translated expression is not ignored
      }
      splits.Add(new SplitExprInfo(false, translatedExpression));
      return splitHappened;
    }

    List<BoundVar> ApplyInduction(QuantifierExpr e) {
      return ApplyInduction(e.BoundVars, e.Attributes, new List<Expression>() { e.LogicalBody() },
        delegate(System.IO.TextWriter wr) { new Printer(Console.Out).PrintExpression(e); });
    }

    delegate void TracePrinter(System.IO.TextWriter wr);

    /// <summary>
    /// Return a subset of "boundVars" (in the order giving in "boundVars") to which to apply induction to,
    /// according to :induction attributes in "attributes" and heuristically interesting subexpressions of
    /// "searchExprs".
    /// </summary>
    List<VarType> ApplyInduction<VarType>(List<VarType> boundVars, Attributes attributes, List<Expression> searchExprs, TracePrinter tracePrinter) where VarType : class, IVariable
    {
      Contract.Requires(boundVars != null);
      Contract.Requires(searchExprs != null);
      Contract.Requires(tracePrinter != null);
      Contract.Ensures(Contract.Result<List<VarType>>() != null);

      if (DafnyOptions.O.Induction == 0) {
        return new List<VarType>();  // don't apply induction
      }

      for (var a = attributes; a != null; a = a.Prev) {
        if (a.Name == "induction") {
          // Here are the supported forms of the :induction attribute.
          //    :induction           -- apply induction to all bound variables
          //    :induction false     -- suppress induction, that is, don't apply it to any bound variable
          //    :induction L       where L is a list consisting entirely of bound variables:
          //                         -- apply induction to the specified bound variables
          //    :induction X       where X is anything else
          //                         -- treat the same as {:induction}, that is, apply induction to all
          //                            bound variables

          // Handle {:induction false}
          if (a.Args.Count == 1) {
            var arg = a.Args[0].E as LiteralExpr;
            if (arg != null && arg.Value is bool && !(bool)arg.Value) {
              if (CommandLineOptions.Clo.Trace) {
                Console.Write("Suppressing automatic induction for: ");
                tracePrinter(Console.Out);
                Console.WriteLine();
              }
              return new List<VarType>();
            }
          }

          // Handle {:induction L}
          if (a.Args.Count != 0) {
            // check that all attribute arguments refer to bound variables; otherwise, go to default_form
            var argsAsVars = new List<VarType>();
            foreach (var arg in a.Args) {
              var theArg = arg.E.Resolved;
              if (theArg is ThisExpr) {
                foreach (var bv in boundVars) {
                  if (bv is ThisSurrogate) {
                    argsAsVars.Add(bv);
                    goto TRY_NEXT_ATTRIBUTE_ARGUMENT;
                  }
                }
              } else if (theArg is IdentifierExpr) {
                var id = (IdentifierExpr)theArg;
                var bv = id.Var as VarType;
                if (bv != null && boundVars.Contains(bv)) {
                  argsAsVars.Add(bv);
                  goto TRY_NEXT_ATTRIBUTE_ARGUMENT;
                }
              }
              // the attribute argument was not one of the possible induction variables
              goto USE_DEFAULT_FORM;
            TRY_NEXT_ATTRIBUTE_ARGUMENT:
              ;
            }
            // so, all attribute arguments are variables; add them to L in the order of the bound variables (not necessarily the order in the attribute)
            var L = new List<VarType>();
            foreach (var bv in boundVars) {
              if (argsAsVars.Contains(bv)) {
                L.Add(bv);
              }
            }
            if (CommandLineOptions.Clo.Trace) {
              string sep = "Applying requested induction on ";
              foreach (var bv in L) {
                Console.Write("{0}{1}", sep, bv.Name);
                sep = ", ";
              }
              Console.Write(" of: ");
              tracePrinter(Console.Out);
              Console.WriteLine();
            }
            return L;
          USE_DEFAULT_FORM: ;
          }

          // We have the {:induction} case, or something to be treated in the same way
          if (CommandLineOptions.Clo.Trace) {
            Console.Write("Applying requested induction on all bound variables of: ");
            tracePrinter(Console.Out);
            Console.WriteLine();
          }
          return boundVars;
        }
      }

      if (DafnyOptions.O.Induction < 2) {
        return new List<VarType>();  // don't apply induction
      }

      // consider automatically applying induction
      var inductionVariables = new List<VarType>();
      foreach (var n in boundVars) {
        if (!n.Type.IsTypeParameter && searchExprs.Exists(expr => VarOccursInArgumentToRecursiveFunction(expr, n))) {
          if (CommandLineOptions.Clo.Trace) {
            Console.Write("Applying automatic induction on variable '{0}' of: ", n.Name);
            tracePrinter(Console.Out);
            Console.WriteLine();
          }
          inductionVariables.Add(n);
        }
      }

      return inductionVariables;
    }

    /// <summary>
    /// Returns 'true' iff by looking at 'expr' the Induction Heuristic determines that induction should be applied to 'n'.
    /// More precisely:
    ///   DafnyInductionHeuristic      Return 'true'
    ///   -----------------------      -------------
    ///        0                       always
    ///        1    if 'n' occurs as   any subexpression (of 'expr')
    ///        2    if 'n' occurs as   any subexpression of          any index argument of an array/sequence select expression or any                       argument to a recursive function
    ///        3    if 'n' occurs as   a prominent subexpression of  any index argument of an array/sequence select expression or any                       argument to a recursive function
    ///        4    if 'n' occurs as   any subexpression of                                                                       any                       argument to a recursive function
    ///        5    if 'n' occurs as   a prominent subexpression of                                                               any                       argument to a recursive function
    ///        6    if 'n' occurs as   a prominent subexpression of                                                               any decreases-influencing argument to a recursive function
    /// Parameter 'n' is allowed to be a ThisSurrogate.
    /// </summary>
    bool VarOccursInArgumentToRecursiveFunction(Expression expr, IVariable n) {
      switch (DafnyOptions.O.InductionHeuristic) {
        case 0: return true;
        case 1: return ContainsFreeVariable(expr, false, n);
        default: return VarOccursInArgumentToRecursiveFunction(expr, n, false);
      }
    }

    /// <summary>
    /// Worker routine for VarOccursInArgumentToRecursiveFunction(expr,n), where the additional parameter 'exprIsProminent' says whether or
    /// not 'expr' prominent status in its context.
    /// DafnyInductionHeuristic cases 0 and 1 are assumed to be handled elsewhere (i.e., a precondition of this method is DafnyInductionHeuristic is at least 2).
    /// Parameter 'n' is allowed to be a ThisSurrogate.
    /// </summary>
    bool VarOccursInArgumentToRecursiveFunction(Expression expr, IVariable n, bool exprIsProminent) {
      Contract.Requires(expr != null);
      Contract.Requires(n != null);

      // The following variable is what gets passed down to recursive calls if the subexpression does not itself acquire prominent status.
      var subExprIsProminent = DafnyOptions.O.InductionHeuristic == 2 || DafnyOptions.O.InductionHeuristic == 4 ? /*once prominent, always prominent*/exprIsProminent : /*reset the prominent status*/false;

      if (expr is ThisExpr) {
        return exprIsProminent && n is ThisSurrogate;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return exprIsProminent && e.Var == n;
      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        var q = DafnyOptions.O.InductionHeuristic < 4 || subExprIsProminent;
        return VarOccursInArgumentToRecursiveFunction(e.Seq, n, subExprIsProminent) ||  // this subexpression does not acquire "prominent" status
          (e.E0 != null && VarOccursInArgumentToRecursiveFunction(e.E0, n, q)) ||  // this one does (unless arrays/sequences are excluded)
          (e.E1 != null && VarOccursInArgumentToRecursiveFunction(e.E1, n, q));    // ditto
      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        var q = DafnyOptions.O.InductionHeuristic < 4 || subExprIsProminent;
        return VarOccursInArgumentToRecursiveFunction(e.Array, n, subExprIsProminent) ||
          e.Indices.Exists(exp => VarOccursInArgumentToRecursiveFunction(exp, n, q));
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        // For recursive functions:  arguments are "prominent"
        // For non-recursive function:  arguments are "prominent" if the call is
        var rec = e.Function.IsRecursive && e.CoCall != FunctionCallExpr.CoCallResolution.Yes;
        bool inferredDecreases;  // we don't actually care
        var decr = FunctionDecreasesWithDefault(e.Function, out inferredDecreases);
        bool variantArgument;
        if (DafnyOptions.O.InductionHeuristic < 6) {
          variantArgument = rec;
        } else {
          // The receiver is considered to be "variant" if the function is recursive and the receiver participates
          // in the effective decreases clause of the function.  The receiver participates if it's a free variable
          // of a term in the explicit decreases clause.
          variantArgument = rec && decr.Exists(ee => ContainsFreeVariable(ee, true, null));
        }
        if (VarOccursInArgumentToRecursiveFunction(e.Receiver, n, variantArgument || subExprIsProminent)) {
          return true;
        }
        Contract.Assert(e.Function.Formals.Count == e.Args.Count);
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          var f = e.Function.Formals[i];
          var exp = e.Args[i];
          if (DafnyOptions.O.InductionHeuristic < 6) {
            variantArgument = rec;
          } else {
            // The argument position is considered to be "variant" if the function is recursive and the argument participates
            // in the effective decreases clause of the function.  The argument participates if it's a free variable
            // of a term in the explicit decreases clause.
            variantArgument = rec && decr.Exists(ee => ContainsFreeVariable(ee, false, f));
          }
          if (VarOccursInArgumentToRecursiveFunction(exp, n, variantArgument || subExprIsProminent)) {
            return true;
          }
        }
        return false;
      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        var q = n.Type.IsDatatype ? exprIsProminent : subExprIsProminent;  // prominent status continues, if we're looking for a variable whose type is a datatype
        return e.Arguments.Exists(exp => VarOccursInArgumentToRecursiveFunction(exp, n, q));
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        // both Not and SeqLength preserve prominence
        return VarOccursInArgumentToRecursiveFunction(e.E, n, exprIsProminent);
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        bool q;
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.Add:
          case BinaryExpr.ResolvedOpcode.Sub:
          case BinaryExpr.ResolvedOpcode.Mul:
          case BinaryExpr.ResolvedOpcode.Div:
          case BinaryExpr.ResolvedOpcode.Mod:
          case BinaryExpr.ResolvedOpcode.Union:
          case BinaryExpr.ResolvedOpcode.Intersection:
          case BinaryExpr.ResolvedOpcode.SetDifference:
          case BinaryExpr.ResolvedOpcode.Concat:
            // these operators preserve prominence
            q = exprIsProminent;
            break;
          default:
            // whereas all other binary operators do not
            q = subExprIsProminent;
            break;
        }
        return VarOccursInArgumentToRecursiveFunction(e.E0, n, q) ||
          VarOccursInArgumentToRecursiveFunction(e.E1, n, q);
      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        // ignore the guard
        return VarOccursInArgumentToRecursiveFunction(e.Body, n);

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return VarOccursInArgumentToRecursiveFunction(e.Test, n, subExprIsProminent) ||  // test is not "prominent"
          VarOccursInArgumentToRecursiveFunction(e.Thn, n, exprIsProminent) ||  // but the two branches are
          VarOccursInArgumentToRecursiveFunction(e.Els, n, exprIsProminent);
      } else if (expr is OldExpr ||
                 expr is ConcreteSyntaxExpression ||
                 expr is BoxingCastExpr ||
                 expr is UnboxingCastExpr) {
        foreach (var exp in expr.SubExpressions) {
          if (VarOccursInArgumentToRecursiveFunction(exp, n, exprIsProminent)) {  // maintain prominence
            return true;
          }
        }
        return false;
      } else {
        // in all other cases, reset the prominence status and recurse on the subexpressions
        foreach (var exp in expr.SubExpressions) {
          if (VarOccursInArgumentToRecursiveFunction(exp, n, subExprIsProminent)) {
            return true;
          }
        }
        return false;
      }
    }

    IEnumerable<Bpl.Expr> InductionCases(Type ty, Bpl.Expr expr, ExpressionTranslator etran) {
      IndDatatypeDecl dt = ty.AsIndDatatype;
      if (dt == null) {
        yield return Bpl.Expr.True;
      } else {
        UserDefinedType instantiatedType = (UserDefinedType)ty;  // correctness of cast follows from the non-null return of ty.AsDatatype
        var subst = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < dt.TypeArgs.Count; i++) {
          subst.Add(dt.TypeArgs[i], instantiatedType.TypeArgs[i]);
        }

        foreach (DatatypeCtor ctor in dt.Ctors) {
          Bpl.VariableSeq bvs;
          List<Bpl.Expr> args;
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          // (exists args :: args-have-the-expected-types && ct(args) == expr)
          Bpl.Expr q = Bpl.Expr.Binary(ctor.tok, BinaryOperator.Opcode.Eq, ct, expr);
          if (bvs.Length != 0) {
            int i = 0;
            Bpl.Expr typeAntecedent = Bpl.Expr.True;
            foreach (Formal arg in ctor.Formals) {
              var instantiatedArgType = Resolver.SubstType(arg.Type, subst);
              Bpl.Expr wh = GetWhereClause(arg.tok, etran.CondApplyUnbox(arg.tok, args[i], arg.Type, instantiatedArgType), instantiatedArgType, etran);
              if (wh != null) {
                typeAntecedent = BplAnd(typeAntecedent, wh);
              }
              i++;
            }
            q = new Bpl.ExistsExpr(ctor.tok, bvs, BplAnd(typeAntecedent, q));
          }
          yield return q;
        }
      }
    }

    /// <summary>
    /// Returns true iff 'v' occurs as a free variable in 'expr'.
    /// Parameter 'v' is allowed to be a ThisSurrogate, in which case the method return true iff 'this'
    /// occurs in 'expr'.
    /// </summary>
    static bool ContainsFreeVariable(Expression expr, bool lookForReceiver, IVariable v) {
      Contract.Requires(expr != null);
      Contract.Requires(lookForReceiver || v != null);

      if (expr is ThisExpr) {
        return lookForReceiver || v is ThisSurrogate;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        return e.Var == v;
      } else {
        foreach (var ee in expr.SubExpressions) {
          if (ContainsFreeVariable(ee, lookForReceiver, v)) {
            return true;
          }
        }
        return false;
      }
    }

    /// <summary>
    /// Returns true iff 'expr' is a two-state expression, that is, if it mentions "old(...)" or "fresh(...)".
    /// </summary>
    public static bool MentionsOldState(Expression expr) {
      Contract.Requires(expr != null);
      if (expr is OldExpr || expr is FreshExpr) {
        return true;
      }
      foreach (var ee in expr.SubExpressions) {
        if (MentionsOldState(ee)) {
          return true;
        }
      }
      return false;
    }

    public static Expression Substitute(Expression expr, Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap) {
      Contract.Requires(expr != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(Contract.Result<Expression>() != null);

      Expression newExpr = null;  // set to non-null value only if substitution has any effect; if non-null, newExpr will be resolved at end

      if (expr is LiteralExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        // nothing to substitute
      } else if (expr is ThisExpr) {
        return receiverReplacement == null ? expr : receiverReplacement;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        Expression substExpr;
        if (substMap.TryGetValue(e.Var, out substExpr)) {
          return cce.NonNull(substExpr);
        }
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        List<Expression> newElements = SubstituteExprList(e.Elements, receiverReplacement, substMap);
        if (newElements != e.Elements) {
          if (expr is SetDisplayExpr) {
            newExpr = new SetDisplayExpr(expr.tok, newElements);
          } else if (expr is MultiSetDisplayExpr) {
            newExpr = new MultiSetDisplayExpr(expr.tok, newElements);
          } else {
            newExpr = new SeqDisplayExpr(expr.tok, newElements);
          }
        }

      } else if (expr is FieldSelectExpr) {
        FieldSelectExpr fse = (FieldSelectExpr)expr;
        Expression substE = Substitute(fse.Obj, receiverReplacement, substMap);
        if (substE != fse.Obj) {
          FieldSelectExpr fseNew = new FieldSelectExpr(fse.tok, substE, fse.FieldName);
          fseNew.Field = fse.Field;  // resolve on the fly (and fseExpr.Type is set at end of method)
          newExpr = fseNew;
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr sse = (SeqSelectExpr)expr;
        Expression seq = Substitute(sse.Seq, receiverReplacement, substMap);
        Expression e0 = sse.E0 == null ? null : Substitute(sse.E0, receiverReplacement, substMap);
        Expression e1 = sse.E1 == null ? null : Substitute(sse.E1, receiverReplacement, substMap);
        if (seq != sse.Seq || e0 != sse.E0 || e1 != sse.E1) {
          newExpr = new SeqSelectExpr(sse.tok, sse.SelectOne, seq, e0, e1);
        }

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr sse = (SeqUpdateExpr)expr;
        Expression seq = Substitute(sse.Seq, receiverReplacement, substMap);
        Expression index = Substitute(sse.Index, receiverReplacement, substMap);
        Expression val = Substitute(sse.Value, receiverReplacement, substMap);
        if (seq != sse.Seq || index != sse.Index || val != sse.Value) {
          newExpr = new SeqUpdateExpr(sse.tok, seq, index, val);
        }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr mse = (MultiSelectExpr)expr;
        Expression array = Substitute(mse.Array, receiverReplacement, substMap);
        List<Expression> newArgs = SubstituteExprList(mse.Indices, receiverReplacement, substMap);
        if (array != mse.Array || newArgs != mse.Indices) {
          newExpr = new MultiSelectExpr(mse.tok, array, newArgs);
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Expression receiver = Substitute(e.Receiver, receiverReplacement, substMap);
        List<Expression> newArgs = SubstituteExprList(e.Args, receiverReplacement, substMap);
        if (receiver != e.Receiver || newArgs != e.Args) {
          FunctionCallExpr newFce = new FunctionCallExpr(expr.tok, e.Name, receiver, e.OpenParen, newArgs);
          newFce.Function = e.Function;  // resolve on the fly (and set newFce.Type below, at end)
          newExpr = newFce;
        }

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        List<Expression> newArgs = SubstituteExprList(dtv.Arguments, receiverReplacement, substMap);
        if (newArgs != dtv.Arguments) {
          DatatypeValue newDtv = new DatatypeValue(dtv.tok, dtv.DatatypeName, dtv.MemberName, newArgs);
          newDtv.Ctor = dtv.Ctor;  // resolve on the fly (and set newDtv.Type below, at end)
          newExpr = newDtv;
        }

      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        // Note, it is up to the caller to avoid variable capture.  In most cases, this is not a
        // problem, since variables have unique declarations.  However, it is an issue if the substitution
        // takes place inside an OldExpr.  In those cases (see LetExpr), the caller can use a
        // BoogieWrapper before calling Substitute.
        Expression se = Substitute(e.E, receiverReplacement, substMap);
        if (se != e.E) {
          newExpr = new OldExpr(expr.tok, se);
        }
      } else if (expr is FreshExpr) {
        FreshExpr e = (FreshExpr)expr;
        Expression se = Substitute(e.E, receiverReplacement, substMap);
        if (se != e.E) {
          newExpr = new FreshExpr(expr.tok, se);
        }
      } else if (expr is AllocatedExpr) {
        AllocatedExpr e = (AllocatedExpr)expr;
        Expression se = Substitute(e.E, receiverReplacement, substMap);
        if (se != e.E) {
          newExpr = new AllocatedExpr(expr.tok, se);
        }
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        Expression se = Substitute(e.E, receiverReplacement, substMap);
        if (se != e.E) {
          newExpr = new UnaryExpr(expr.tok, e.Op, se);
        }
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        Expression e0 = Substitute(e.E0, receiverReplacement, substMap);
        Expression e1 = Substitute(e.E1, receiverReplacement, substMap);
        if (e0 != e.E0 || e1 != e.E1) {
          BinaryExpr newBin = new BinaryExpr(expr.tok, e.Op, e0, e1);
          newBin.ResolvedOp = e.ResolvedOp;  // part of what needs to be done to resolve on the fly (newBin.Type is set below, at end)
          newExpr = newBin;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        var rhss = new List<Expression>();
        bool anythingChanged = false;
        foreach (var rhs in e.RHSs) {
          var r = Substitute(rhs, receiverReplacement, substMap);
          if (r != rhs) {
            anythingChanged = true;
          }
          rhss.Add(r);
        }
        var body = Substitute(e.Body, receiverReplacement, substMap);
        if (anythingChanged || body != e.Body) {
          newExpr = new LetExpr(e.tok, e.Vars, rhss, body);
        }

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        Expression newRange = e.Range == null ? null : Substitute(e.Range, receiverReplacement, substMap);
        Expression newTerm = Substitute(e.Term, receiverReplacement, substMap);
        Attributes newAttrs = SubstAttributes(e.Attributes, receiverReplacement, substMap);
        if (e is SetComprehension) {
          if (newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes) {
            newExpr = new SetComprehension(expr.tok, e.BoundVars, newRange, newTerm);
          }
        } else if (e is MapComprehension) {
          if (newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes) {
            newExpr = new MapComprehension(expr.tok, e.BoundVars, newRange, newTerm);
          }
        } else if (e is QuantifierExpr) {
          var q = (QuantifierExpr)e;
          if (newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes) {
            if (expr is ForallExpr) {
              newExpr = new ForallExpr(expr.tok, e.BoundVars, newRange, newTerm, newAttrs);
            } else {
              newExpr = new ExistsExpr(expr.tok, e.BoundVars, newRange, newTerm, newAttrs);
            }
          }
        } else {
          Contract.Assert(false);  // unexpected ComprehensionExpr
        }

      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        Expression g = Substitute(e.Guard, receiverReplacement, substMap);
        Expression b = Substitute(e.Body, receiverReplacement, substMap);
        if (g != e.Guard || b != e.Body) {
          if (expr is AssertExpr) {
            newExpr = new AssertExpr(e.tok, g, b);
          } else {
            newExpr = new AssumeExpr(e.tok, g, b);
          }
        }

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Expression test = Substitute(e.Test, receiverReplacement, substMap);
        Expression thn = Substitute(e.Thn, receiverReplacement, substMap);
        Expression els = Substitute(e.Els, receiverReplacement, substMap);
        if (test != e.Test || thn != e.Thn || els != e.Els) {
          newExpr = new ITEExpr(expr.tok, test, thn, els);
        }

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return Substitute(e.ResolvedExpression, receiverReplacement, substMap);
      }

      if (newExpr == null) {
        return expr;
      } else {
        newExpr.Type = expr.Type;  // resolve on the fly (any additional resolution must be done above)
        return newExpr;
      }
    }

    static List<Expression/*!*/>/*!*/ SubstituteExprList(List<Expression/*!*/>/*!*/ elist,
                                                 Expression receiverReplacement, Dictionary<IVariable,Expression/*!*/>/*!*/ substMap) {
      Contract.Requires(cce.NonNullElements(elist));
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Expression>>()));

      List<Expression> newElist = null;  // initialized lazily
      for (int i = 0; i < elist.Count; i++)
      {cce.LoopInvariant(  newElist == null || newElist.Count == i);

        Expression substE = Substitute(elist[i], receiverReplacement, substMap);
        if (substE != elist[i] && newElist == null) {
          newElist = new List<Expression>();
          for (int j = 0; j < i; j++) {
            newElist.Add(elist[j]);
          }
        }
        if (newElist != null) {
          newElist.Add(substE);
        }
      }
      if (newElist == null) {
        return elist;
      } else {
        return newElist;
      }
    }

    static Attributes SubstAttributes(Attributes attrs, Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap) {
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      if (attrs != null) {
        List<Attributes.Argument> newArgs = new List<Attributes.Argument>();  // allocate it eagerly, what the heck, it doesn't seem worth the extra complexity in the code to do it lazily for the infrequently occurring attributes
        bool anyArgSubst = false;
        foreach (Attributes.Argument arg in attrs.Args) {
          Attributes.Argument newArg = arg;
          if (arg.E != null) {
            Expression newE = Substitute(arg.E, receiverReplacement, substMap);
            if (newE != arg.E) {
              newArg = new Attributes.Argument(arg.Tok, newE);
              anyArgSubst = true;
            }
          }
          newArgs.Add(newArg);
        }
        if (!anyArgSubst) {
          newArgs = attrs.Args;
        }

        Attributes prev = SubstAttributes(attrs.Prev, receiverReplacement, substMap);
        if (newArgs != attrs.Args || prev != attrs.Prev) {
          return new Attributes(attrs.Name, newArgs, prev);
        }
      }
      return attrs;
    }

  }
}
