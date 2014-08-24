//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using BplParser = Parser;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class Translator {

    [NotDelayed]
    public Translator() {
      InsertChecksums = 0 < CommandLineOptions.Clo.VerifySnapshots;
      Bpl.Program boogieProgram = ReadPrelude();
      if (boogieProgram != null) {
        sink = boogieProgram;
        predef = FindPredefinedDecls(boogieProgram);
      }
    }

    // translation state
    readonly Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>/*!*/ classes = new Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<TopLevelDecl, string>/*!*/ classConstants = new Dictionary<TopLevelDecl, string>();
    readonly Dictionary<int, string> functionConstants = new Dictionary<int, string>();
    readonly Dictionary<Function, string> functionHandles = new Dictionary<Function, string>();
    readonly Dictionary<Field/*!*/,Bpl.Constant/*!*/>/*!*/ fields = new Dictionary<Field/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/, Bpl.Function/*!*/>/*!*/ fieldFunctions = new Dictionary<Field/*!*/, Bpl.Function/*!*/>();
    readonly Dictionary<string, Bpl.Constant> fieldConstants = new Dictionary<string,Constant>();
    readonly ISet<string> abstractTypes = new HashSet<string>();
    Program program;

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(classes));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fields));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fieldFunctions));
      Contract.Invariant(codeContext == null || codeContext.EnclosingModule == currentModule);
    }

    readonly Bpl.Program sink;
    readonly PredefinedDecls predef;

    public bool InsertChecksums { get; set; }
    public string UniqueIdPrefix { get; set; }

    internal class PredefinedDecls {
      public readonly Bpl.Type RefType;
      public readonly Bpl.Type BoxType;
      public readonly Bpl.Type TickType;
      private readonly Bpl.TypeSynonymDecl setTypeCtor;
      private readonly Bpl.TypeSynonymDecl multiSetTypeCtor;
      private readonly Bpl.TypeCtorDecl mapTypeCtor;
      public readonly Bpl.Function ArrayLength;
      public readonly Bpl.Function RealTrunc;
      private readonly Bpl.TypeCtorDecl seqTypeCtor;
      readonly Bpl.TypeCtorDecl fieldName;
      public readonly Bpl.Type HeapType;
      public readonly string HeapVarName;
      public readonly Bpl.Type ClassNameType;
      public readonly Bpl.Type NameFamilyType;
      public readonly Bpl.Type DatatypeType;
      public readonly Bpl.Type HandleType;
      public readonly Bpl.Type LayerType;
      public readonly Bpl.Type DtCtorId;
      public readonly Bpl.Type Ty;
      public readonly Bpl.Type TyTag;
      public readonly Bpl.Expr Null;
      private readonly Bpl.Constant allocField;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(RefType != null);
        Contract.Invariant(BoxType != null);
        Contract.Invariant(TickType != null);
        Contract.Invariant(setTypeCtor != null);
        Contract.Invariant(multiSetTypeCtor != null);
        Contract.Invariant(ArrayLength != null);
        Contract.Invariant(RealTrunc != null);
        Contract.Invariant(seqTypeCtor != null);
        Contract.Invariant(fieldName != null);
        Contract.Invariant(HeapVarName != null);
        Contract.Invariant(ClassNameType != null);
        Contract.Invariant(NameFamilyType != null);
        Contract.Invariant(DatatypeType != null);
        Contract.Invariant(HandleType != null);
        Contract.Invariant(LayerType != null);
        Contract.Invariant(DtCtorId != null);
        Contract.Invariant(Ty != null);
        Contract.Invariant(TyTag != null);
        Contract.Invariant(Null != null);
        Contract.Invariant(allocField != null);
      }

      public Bpl.Type SetType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, setTypeCtor, new List<Bpl.Type> { ty });
      }

      public Bpl.Type MultiSetType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, multiSetTypeCtor, new List<Bpl.Type>{ ty });
      }
      public Bpl.Type MapType(IToken tok, Bpl.Type tya, Bpl.Type tyb) {
        Contract.Requires(tok != null);
        Contract.Requires(tya != null && tyb != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(Token.NoToken, mapTypeCtor, new List<Bpl.Type> { tya, tyb });
      }

      public Bpl.Type SeqType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);
        return new Bpl.CtorType(Token.NoToken, seqTypeCtor, new List<Bpl.Type>{ ty });
      }

      public Bpl.Type FieldName(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(tok, fieldName, new List<Bpl.Type>{ ty });
      }

      public Bpl.IdentifierExpr Alloc(IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

        return new Bpl.IdentifierExpr(tok, allocField);
      }

      public PredefinedDecls(Bpl.TypeCtorDecl refType, Bpl.TypeCtorDecl boxType, Bpl.TypeCtorDecl tickType,
                             Bpl.TypeSynonymDecl setTypeCtor, Bpl.TypeSynonymDecl multiSetTypeCtor, Bpl.TypeCtorDecl mapTypeCtor,
                             Bpl.Function arrayLength, Bpl.Function realTrunc, Bpl.TypeCtorDecl seqTypeCtor, Bpl.TypeCtorDecl fieldNameType,
                             Bpl.TypeCtorDecl tyType, Bpl.TypeCtorDecl tyTagType,
                             Bpl.GlobalVariable heap, Bpl.TypeCtorDecl classNameType, Bpl.TypeCtorDecl nameFamilyType,
                             Bpl.TypeCtorDecl datatypeType, Bpl.TypeCtorDecl handleType, Bpl.TypeCtorDecl layerType, Bpl.TypeCtorDecl dtCtorId,
                             Bpl.Constant allocField) {
        #region Non-null preconditions on parameters
        Contract.Requires(refType != null);
        Contract.Requires(boxType != null);
        Contract.Requires(tickType != null);
        Contract.Requires(setTypeCtor != null);
        Contract.Requires(multiSetTypeCtor != null);
        Contract.Requires(mapTypeCtor != null);
        Contract.Requires(arrayLength != null);
        Contract.Requires(realTrunc != null);
        Contract.Requires(seqTypeCtor != null);
        Contract.Requires(fieldNameType != null);
        Contract.Requires(heap != null);
        Contract.Requires(classNameType != null);
        Contract.Requires(datatypeType != null);
        Contract.Requires(layerType != null);
        Contract.Requires(dtCtorId != null);
        Contract.Requires(allocField != null);
        Contract.Requires(tyType != null);
        Contract.Requires(tyTagType != null);
        #endregion

        Bpl.CtorType refT = new Bpl.CtorType(Token.NoToken, refType, new List<Bpl.Type>());
        this.RefType = refT;
        this.BoxType = new Bpl.CtorType(Token.NoToken, boxType, new List<Bpl.Type>());
        this.TickType = new Bpl.CtorType(Token.NoToken, tickType, new List<Bpl.Type>());
        this.setTypeCtor = setTypeCtor;
        this.multiSetTypeCtor = multiSetTypeCtor;
        this.mapTypeCtor = mapTypeCtor;
        this.ArrayLength = arrayLength;
        this.RealTrunc = realTrunc;
        this.seqTypeCtor = seqTypeCtor;
        this.fieldName = fieldNameType;
        this.HeapType = heap.TypedIdent.Type;
        this.HeapVarName = heap.Name;
        this.Ty = new Bpl.CtorType(Token.NoToken, tyType, new List<Bpl.Type>());
        this.TyTag = new Bpl.CtorType(Token.NoToken, tyTagType, new List<Bpl.Type>());
        this.ClassNameType = new Bpl.CtorType(Token.NoToken, classNameType, new List<Bpl.Type>());
        this.NameFamilyType = new Bpl.CtorType(Token.NoToken, nameFamilyType, new List<Bpl.Type>());
        this.DatatypeType = new Bpl.CtorType(Token.NoToken, datatypeType, new List<Bpl.Type>());
        this.HandleType = new Bpl.CtorType(Token.NoToken, handleType, new List<Bpl.Type>());
        this.LayerType = new Bpl.CtorType(Token.NoToken, layerType, new List<Bpl.Type>());
        this.DtCtorId = new Bpl.CtorType(Token.NoToken, dtCtorId, new List<Bpl.Type>());
        this.allocField = allocField;
        this.Null = new Bpl.IdentifierExpr(Token.NoToken, "null", refT);
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
      Bpl.Function realTrunc = null;
      Bpl.TypeCtorDecl seqTypeCtor = null;
      Bpl.TypeCtorDecl fieldNameType = null;
      Bpl.TypeCtorDecl classNameType = null;
      Bpl.TypeCtorDecl tyType = null;
      Bpl.TypeCtorDecl tyTagType = null;
      Bpl.TypeCtorDecl nameFamilyType = null;
      Bpl.TypeCtorDecl datatypeType = null;
      Bpl.TypeCtorDecl handleType = null;
      Bpl.TypeCtorDecl layerType = null;
      Bpl.TypeCtorDecl dtCtorId = null;
      Bpl.TypeCtorDecl boxType = null;
      Bpl.TypeCtorDecl tickType = null;
      Bpl.TypeCtorDecl mapTypeCtor = null;
      Bpl.GlobalVariable heap = null;
      Bpl.Constant allocField = null;
      foreach (var d in prog.TopLevelDeclarations) {
        if (d is Bpl.TypeCtorDecl) {
          Bpl.TypeCtorDecl dt = (Bpl.TypeCtorDecl)d;
          if (dt.Name == "Seq") {
            seqTypeCtor = dt;
          } else if (dt.Name == "Field") {
            fieldNameType = dt;
          } else if (dt.Name == "ClassName") {
            classNameType = dt;
          } else if (dt.Name == "Ty") {
            tyType = dt;
          } else if (dt.Name == "TyTag") {
            tyTagType = dt;
          } else if (dt.Name == "DatatypeType") {
            datatypeType = dt;
          } else if (dt.Name == "HandleType") {
            handleType = dt;
          } else if (dt.Name == "LayerType") {
            layerType = dt;
          } else if (dt.Name == "DtCtorId") {
            dtCtorId = dt;
          } else if (dt.Name == "ref") {
            refType = dt;
          } else if (dt.Name == "NameFamily") {
            nameFamilyType = dt;
          } else if (dt.Name == "Box") {
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
          } 
        } else if (d is Bpl.GlobalVariable) {
          Bpl.GlobalVariable v = (Bpl.GlobalVariable)d;
          if (v.Name == "$Heap") {
            heap = v;
          }
        } else if (d is Bpl.Function) {
          var f = (Bpl.Function)d;
          if (f.Name == "_System.array.Length") {
            arrayLength = f;
          } else if (f.Name == "_System.real.Trunc") {
            realTrunc = f;
          }
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
      } else if (realTrunc == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.real.Trunc");
      } else if (fieldNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Field");
      } else if (classNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ClassName");
      } else if (tyType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Ty");
      } else if (tyTagType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type TyTag");
      } else if (nameFamilyType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type NameFamily");
      } else if (datatypeType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type DatatypeType");
      } else if (handleType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type HandleType");
      } else if (layerType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type LayerType");
      } else if (dtCtorId == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type DtCtorId");
      } else if (refType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ref");
      } else if (boxType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Box");
      } else if (tickType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type TickType");
      } else if (heap == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of $Heap");
      } else if (allocField == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of constant alloc");
      } else {
        return new PredefinedDecls(refType, boxType, tickType,
                                   setTypeCtor, multiSetTypeCtor, mapTypeCtor,
                                   arrayLength, realTrunc, seqTypeCtor, fieldNameType,
                                   tyType, tyTagType,
                                   heap, classNameType, nameFamilyType,
                                   datatypeType, handleType, layerType, dtCtorId,
                                   allocField);
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
      int errorCount = BplParser.Parse(preludePath, (List<string>)null, out prelude);
      if (prelude == null || errorCount > 0) {
        return null;
      } else {
        return prelude;
      }
    }

    public Bpl.IdentifierExpr TrVar(IToken tok, IVariable var) {
      Contract.Requires(var != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
      return new Bpl.IdentifierExpr(tok, var.AssignUniqueName(currentDeclaration), TrType(var.Type));
    }

    public Bpl.Program Translate(Program p) {
      Contract.Requires(p != null);
      Contract.Ensures(Contract.Result<Bpl.Program>() != null);
      
      program = p;

      if (sink == null || predef == null) {
        // something went wrong during construction, which reads the prelude; an error has
        // already been printed, so just return an empty program here (which is non-null)
        return new Bpl.Program();
      }

      foreach (var ad in ArrowType.ArrowTypeDecls) {
        currentDeclaration = ad;
        GetClassTyCon(ad);
        AddArrowTypeAxioms(ad);
      }

      foreach (TopLevelDecl d in program.BuiltIns.SystemModule.TopLevelDecls) {
        currentDeclaration = d;
        if (d is OpaqueTypeDecl) {
          AddTypeDecl((OpaqueTypeDecl)d);
        } else if (d is DerivedTypeDecl) {
          AddTypeDecl((DerivedTypeDecl)d);
        } else if (d is DatatypeDecl) {
          AddDatatype((DatatypeDecl)d);
        } else {
          AddClassMembers((ClassDecl)d);
        }
      }
      foreach (ModuleDefinition m in program.Modules) {
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          currentDeclaration = d;
          if (d is OpaqueTypeDecl) {
            AddTypeDecl((OpaqueTypeDecl)d);
          } else if (d is DerivedTypeDecl) {
            AddTypeDecl((DerivedTypeDecl)d);
          } else if (d is TypeSynonymDecl) {
            // do nothing, just bypass type synonyms in the translation
          } else if (d is DatatypeDecl) {
            AddDatatype((DatatypeDecl)d);
          } else if (d is ModuleDecl) {
            // submodules have already been added as a top level module, ignore this.
          } else if (d is ClassDecl) {
            AddClassMembers((ClassDecl)d);
            if (d is IteratorDecl) {
              AddIteratorSpecAndBody((IteratorDecl)d);
            }
          } else {
            Contract.Assert(false);
          }
        }
      }
      foreach(var c in fieldConstants.Values) {
        sink.TopLevelDeclarations.Add(c);
      }
      HashSet<Tuple<string, string>> checkedMethods = new HashSet<Tuple<string, string>>();
      HashSet<Tuple<string, string>> checkedFunctions = new HashSet<Tuple<string, string>>();
      foreach (var t in program.TranslationTasks) {
        if (t is MethodCheck) {
          var m = (MethodCheck)t;
          currentDeclaration = m.Refining;
          var id = new Tuple<string, string>(m.Refined.FullSanitizedName, m.Refining.FullSanitizedName);
          if (!checkedMethods.Contains(id)) {
            AddMethodRefinementCheck(m);
            checkedMethods.Add(id);
          }
        } else if (t is FunctionCheck) {
          var f = (FunctionCheck)t;
          currentDeclaration = f.Refining;
          var id = new Tuple<string, string>(f.Refined.FullSanitizedName, f.Refining.FullSanitizedName);
          if (!checkedFunctions.Contains(id)) {
            AddFunctionRefinementCheck(f);
            checkedFunctions.Add(id);
          }
        }
      }

      //adding TraitParent function and axioms
      AddTraitParentFuncAndAxioms();


      if (InsertChecksums)
      {
        foreach (var decl in sink.TopLevelDeclarations)
        {
          var impl = decl as Implementation;
          if (impl != null && impl.FindStringAttribute("checksum") == null)
          {
            impl.AddAttribute("checksum", "stable");
          }

          var func = decl as Bpl.Function;
          if (func != null && func.FindStringAttribute("checksum") == null)
          {
            func.AddAttribute("checksum", "stable");
          }
        }
      }

      return sink;
    }

    //adding TraitParent function and axioms
    //if a class A extends trait J and B does not extned anything, then this method adds the followings to the sink: 
    //   const unique NoTraitAtAll: ClassName;
    //   function TraitParent(ClassName): ClassName;
    //   axiom TraitParent(class.A) == class.J;
    //   axiom TraitParent(class.B) == NoTraitAtAll;
    private void AddTraitParentFuncAndAxioms()
    {
        foreach (ModuleDefinition m in program.Modules)
        {
            if (m.TopLevelDecls.Any(d => (d is ClassDecl && ((ClassDecl)d).Trait != null) || (d is TraitDecl)))
            {
                //adding const unique NoTraitAtAll: ClassName;
                Token tNoTrait = new Token();
                Token tTraitParent = new Token();
                Bpl.Constant cNoTrait = new Bpl.Constant(tNoTrait, new Bpl.TypedIdent(tNoTrait, "NoTraitAtAll", predef.ClassNameType), true);
                sink.TopLevelDeclarations.Add(cNoTrait);
                //adding function TraitParent(ClassName): ClassName;
                var arg_ref = new Bpl.Formal(tTraitParent, new Bpl.TypedIdent(tTraitParent, Bpl.TypedIdent.NoName, predef.ClassNameType), true);
                var res = new Bpl.Formal(tTraitParent, new Bpl.TypedIdent(tTraitParent, Bpl.TypedIdent.NoName, predef.ClassNameType), false);
                var fTraitParent = new Bpl.Function(tTraitParent, "TraitParent", new List<Variable> { arg_ref }, res);
                sink.TopLevelDeclarations.Add(fTraitParent);

                foreach (TopLevelDecl d in m.TopLevelDecls)
                {
                    if (d is ClassDecl)
                    {
                        var c = (ClassDecl)d;
                        if (c is ClassDecl && c.Trait != null)
                        {
                            //this adds: axiom TraitParent(class.A) == class.J; Where A extends J
                            Bpl.TypedIdent trait_id = new Bpl.TypedIdent(c.Trait.tok, string.Format("class.{0}", c.Trait.FullSanitizedName), predef.ClassNameType);
                            Bpl.Constant trait = new Bpl.Constant(c.Trait.tok, trait_id, true);
                            Bpl.Expr traitId_expr = new Bpl.IdentifierExpr(c.Trait.tok, trait);

                            var args = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.ClassNameType), true);
                            var ret_value = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.ClassNameType), false);
                            var funCall = new Bpl.FunctionCall(new Bpl.Function(c.tok, "TraitParent", new List<Variable> { args }, ret_value));
                            var funCallExpr = new Bpl.NAryExpr(c.tok, funCall, new List<Expr> { new Bpl.IdentifierExpr(c.tok, string.Format("class.{0}", c.FullSanitizedName), predef.ClassNameType) });
                            var traitParentAxiom = new Bpl.Axiom(c.tok, Bpl.Expr.Eq(funCallExpr, traitId_expr));

                            sink.TopLevelDeclarations.Add(traitParentAxiom);
                        }
                        else if (c is ClassDecl && c.Trait == null)
                        {
                            //this adds: axiom TraitParent(class.B) == NoTraitAtAll; Where B does not extend any traits
                            Bpl.TypedIdent noTraitAtAll_id = new Bpl.TypedIdent(c.tok, "NoTraitAtAll", predef.ClassNameType);
                            Bpl.Constant noTraitAtAll = new Bpl.Constant(c.tok, noTraitAtAll_id, true);
                            Bpl.Expr noTraitAtAll_expr = new Bpl.IdentifierExpr(c.tok, noTraitAtAll);

                            var args = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.ClassNameType), true);
                            var ret_value = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.ClassNameType), false);
                            var funCall = new Bpl.FunctionCall(new Bpl.Function(c.tok, "TraitParent", new List<Variable> { args }, ret_value));
                            var funCallExpr = new Bpl.NAryExpr(c.tok, funCall, new List<Expr> { new Bpl.IdentifierExpr(c.tok, string.Format("class.{0}", c.FullSanitizedName), predef.ClassNameType) });
                            var traitParentAxiom = new Bpl.Axiom(c.tok, Bpl.Expr.Eq(funCallExpr, noTraitAtAll_expr));

                            sink.TopLevelDeclarations.Add(traitParentAxiom);
                        }
                    }
                }
            }
        }
    }

    void AddTypeDecl(OpaqueTypeDecl td) {
      Contract.Requires(td != null);
      AddTypeDecl_Aux(td.tok, nameTypeParam(td.TheType), td.TypeArgs);
    }
    void AddTypeDecl(DerivedTypeDecl dd) {
      Contract.Requires(dd != null);
      AddTypeDecl_Aux(dd.tok, dd.FullName, new List<TypeParameter>());
    }
    void AddTypeDecl_Aux(IToken tok, string nm, List<TypeParameter> typeArgs) {
      Contract.Requires(tok != null);
      Contract.Requires(nm != null);
      Contract.Requires(typeArgs != null);

      if (abstractTypes.Contains(nm)) {
        // nothing to do; has already been added
        return;
      }
      if (typeArgs.Count == 0) {
        sink.TopLevelDeclarations.Add(
          new Bpl.Constant(tok,
            new TypedIdent(tok, nm, predef.Ty), false /* not unique */));
      } else {
        // Note, the function produced is NOT necessarily injective, because the type may be replaced
        // in a refinement module in such a way that the type arguments do not matter.
        var args = new List<Bpl.Variable>(typeArgs.ConvertAll(a => (Bpl.Variable)BplFormalVar(null, predef.Ty, true)));
        var func = new Bpl.Function(tok, nm, args, BplFormalVar(null, predef.Ty, false));
        sink.TopLevelDeclarations.Add(func);
      }
      abstractTypes.Add(nm);
    }

    void AddDatatype(DatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(sink != null && predef != null);
      Bpl.Constant dt_const = GetClass(dt);
      sink.TopLevelDeclarations.Add(dt_const);

      foreach (DatatypeCtor ctor in dt.Ctors) {
        int i;

        // Add:  function #dt.ctor(tyVars, paramTypes) returns (DatatypeType);
        
        List<Bpl.Variable> argTypes = new List<Bpl.Variable>();
        foreach (Formal arg in ctor.Formals) {
          Bpl.Variable a = new Bpl.Formal(arg.tok, new Bpl.TypedIdent(arg.tok, Bpl.TypedIdent.NoName, TrType(arg.Type)), true);
          argTypes.Add(a);
        }
        Bpl.Variable resType = new Bpl.Formal(ctor.tok, new Bpl.TypedIdent(ctor.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), false);
        Bpl.Function fn = new Bpl.Function(ctor.tok, ctor.FullName, argTypes, resType, "Constructor function declaration");
        if (InsertChecksums) {
          InsertChecksum(dt, fn);
        }
        sink.TopLevelDeclarations.Add(fn);

        List<Variable> bvs;
        List<Bpl.Expr> args;


        {
          // Add:  const unique ##dt.ctor: DtCtorId;
          Bpl.Constant cid = new Bpl.Constant(ctor.tok, new Bpl.TypedIdent(ctor.tok, "#" + ctor.FullName, predef.DtCtorId), true);
          Bpl.Expr c = new Bpl.IdentifierExpr(ctor.tok, cid);
          sink.TopLevelDeclarations.Add(cid);

          {
            // Add:  axiom (forall params :: DatatypeCtorId(#dt.ctor(params)) == ##dt.ctor);       
            CreateBoundVariables(ctor.Formals, out bvs, out args);
            Bpl.Expr lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
            lhs = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, lhs);
            Bpl.Expr q = Bpl.Expr.Eq(lhs, c);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, BplForall(bvs, q), "Constructor identifier"));
          }

          {
            // Add:  function dt.ctor?(this: DatatypeType): bool { DatatypeCtorId(this) == ##dt.ctor }
            fn = GetReadonlyField(ctor.QueryField);
            sink.TopLevelDeclarations.Add(fn);

            // and here comes the associated axiom:

            Bpl.Expr th; var thVar = BplBoundVar("d", predef.DatatypeType, out th);
            var queryPredicate = FunctionCall(ctor.tok, fn.Name, Bpl.Type.Bool, th);
            var ctorId = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, th);
            var rhs = Bpl.Expr.Eq(ctorId, c);
            var body = Bpl.Expr.Iff(queryPredicate, rhs);
            var tr = BplTrigger(queryPredicate);
            var ax = BplForall(thVar, tr, body);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, ax, "Questionmark and identifier"));
          }

        }
        
        
        {
          // Add:  axiom (forall d: DatatypeType :: dt.ctor?(d) ==> (exists params :: d == #dt.ctor(params));
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          Bpl.Expr dId; var dBv = BplBoundVar("d", predef.DatatypeType, out dId);
          Bpl.Expr q = Bpl.Expr.Eq(dId, lhs);
          if (bvs.Count != 0) {
            q = new Bpl.ExistsExpr(ctor.tok, bvs, q);
          }
          Bpl.Expr dtq = FunctionCall(ctor.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, dId);
          q = BplForall(dBv, null, BplImp(dtq, q));
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Constructor questionmark has arguments"));
        }

        MapM(Bools, is_alloc => {
          /*
            (forall x0 : C0, ..., xn : Cn, G : Ty •
              { $Is(C(x0,...,xn), T(G)) }
              $Is(C(x0,...,xn), T(G)) <==> 
              $Is[Box](x0, C0(G)) && ... && $Is[Box](xn, Cn(G)));
            (forall x0 : C0, ..., xn : Cn, G : Ty •
                { $IsAlloc(C(G, x0,...,xn), T(G)) }
                $IsAlloc(C(G, x0,...,xn), T(G)) ==> 
                    $IsAlloc[Box](x0, C0(G)) && ... && $IsAlloc[Box](xn, Cn(G)));
          */
          List<Bpl.Expr> tyexprs;
          var tyvars = MkTyParamBinders(dt.TypeArgs, out tyexprs);
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr h;
          var hVar = BplBoundVar("$h", predef.HeapType, out h);
          Bpl.Expr conj = Bpl.Expr.True;
          i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (is_alloc) {
              conj = BplAnd(conj, MkIsAlloc(args[i], arg.Type, h));
            } else {
              conj = BplAnd(conj, MkIs(args[i], arg.Type));
            }
            i++;
          }
          var c_params = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          var c_ty = ClassTyCon((TopLevelDecl)dt, tyexprs);
          bvs.InsertRange(0, tyvars);
          if (!is_alloc) {
            var c_is = MkIs(c_params, c_ty);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok,
                BplForall(bvs, BplTrigger(c_is), BplIff(c_is, conj)),
                "Constructor $Is"));
          } else if (is_alloc) {
            var isGoodHeap = FunctionCall(ctor.tok, BuiltinFunction.IsGoodHeap, null, h);
            var c_alloc = MkIsAlloc(c_params, c_ty, h);
            bvs.Add(hVar);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok,
                BplForall(bvs, BplTrigger(c_alloc),
                               BplImp(isGoodHeap, BplIff(c_alloc, conj))),
                "Constructor $IsAlloc"));
          }
        });

        if (dt is IndDatatypeDecl) {
          // Add Lit axiom:
          // axiom (forall p0, ..., pn :: #dt.ctor(Lit(p0), ..., Lit(pn)) == Lit(#dt.ctor(p0, .., pn)));
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          var litargs = new List<Bpl.Expr>();
          foreach (Bpl.Expr arg in args) {
            litargs.Add(Lit(arg));
          }
          Bpl.Expr lhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, litargs);                 
          Bpl.Expr rhs = Lit(FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args), predef.DatatypeType);
          Bpl.Expr q = BplForall(bvs, BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs));
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Constructor literal"));
        }         

        // Injectivity axioms for normal arguments
        i = 0; 
        foreach (Formal arg in ctor.Formals) {
          // function ##dt.ctor#i(DatatypeType) returns (Ti);
          var sf = ctor.Destructors[i];
          Contract.Assert(sf != null);
          fn = GetReadonlyField(sf);
          sink.TopLevelDeclarations.Add(fn);
          // axiom (forall params :: ##dt.ctor#i(#dt.ctor(params)) == params_i);
          CreateBoundVariables(ctor.Formals, out bvs, out args);         
          var inner = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          var outer = FunctionCall(ctor.tok, fn.Name, TrType(arg.Type), inner);
          var q = BplForall(bvs, BplTrigger(inner), Bpl.Expr.Eq(outer, args[i]));
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Constructor injectivity"));

          if (dt is IndDatatypeDecl) {
            var argType = arg.Type.NormalizeExpand();
            if (argType.IsDatatype || argType.IsTypeParameter) {
              // for datatype:             axiom (forall params :: DtRank(params_i) < DtRank(#dt.ctor(params)));
              // for type-parameter type:  axiom (forall params :: DtRank(Unbox(params_i)) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Expr lhs = FunctionCall(ctor.tok, arg.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, args[i]);
              /* CHECK
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                argType.IsDatatype ? args[i] : FunctionCall(ctor.tok, BuiltinFunction.Unbox, predef.DatatypeType, args[i]));
              */
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Lt(lhs, rhs));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Inductive rank"));
            } else if (argType is SeqType) {
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
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                FunctionCall(arg.tok, BuiltinFunction.Unbox, predef.DatatypeType,
                  FunctionCall(arg.tok, BuiltinFunction.SeqIndex, predef.DatatypeType, args[i], ie)));
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q));
              // axiom (forall params, SeqRank(arg) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);             
              lhs = FunctionCall(ctor.tok, BuiltinFunction.SeqRank, null, args[i]);
              rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Lt(lhs, rhs));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Inductive seq rank"));
            } else if (argType is SetType) {
              // axiom (forall params, d: Datatype :: arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype :: arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              Bpl.Expr ante = Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie));
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Inductive set rank"));
            } else if (argType is MultiSetType) {
              // axiom (forall params, d: Datatype :: 0 < arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype :: 0 < arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              Bpl.Expr ante = Bpl.Expr.Gt(Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie)), Bpl.Expr.Literal(0));
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, rhs);
              q = new Bpl.ForallExpr(ctor.tok, bvs, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.TopLevelDeclarations.Add(new Bpl.Axiom(ctor.tok, q, "Inductive multiset rank"));
            }
          }

          i++;          
        }
      }

      {
        // Add:
        //   function $IsA#Dt(G: Ty,d: DatatypeType): bool {
        //     Dt.Ctor0?(G, d) || Dt.Ctor1?(G, d) || ...
        //   }
        var cases_dBv = new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), true);
        var cases_resType = new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
        var cases_fn = new Bpl.Function(dt.tok, "$IsA#" + dt.FullSanitizedName,
                                        new List<Variable> { cases_dBv },
                                        cases_resType,
                                        "One-depth case-split function");

        if (InsertChecksums) {
          InsertChecksum(dt, cases_fn);
        }

        sink.TopLevelDeclarations.Add(cases_fn);
        // and here comes the actual axiom:
        {
          Bpl.Expr d;
          var dVar = BplBoundVar("d", predef.DatatypeType, out d);
          var lhs = FunctionCall(dt.tok, cases_fn.Name, Bpl.Type.Bool, d);
          Bpl.Expr cases_body = Bpl.Expr.False;
          foreach (DatatypeCtor ctor in dt.Ctors) {
            var disj = FunctionCall(ctor.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, d);
            cases_body = BplOr(cases_body, disj);
          }
          var ax = BplForall(new List<Variable> { dVar }, BplTrigger(lhs), BplImp(lhs, cases_body));
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(dt.tok, ax, "One-depth case-split axiom"));
        }
      }

      // The axiom above ($IsA#Dt(d) <==> Dt.Ctor0?(d) || Dt.Ctor1?(d)) gets triggered only with $IsA#Dt(d).  The $IsA#Dt(d)
      // predicate is generated only where the translation inserts it; in other words, the user cannot write any assertion
      // that causes the $IsA#Dt(d) predicate to be emitted.  This is what we want, because making the RHS disjunction be
      // available too often makes performance go down.  However, we do want to allow the disjunction to be introduced if the
      // user explicitly talks about one of its disjuncts.  To make this useful, we introduce the following axiom.  Note that
      // the DtType(d) information is available everywhere.
      // axiom (forall G: Ty, d: DatatypeType ::
      //         { Dt.Ctor0?(G,d) }
      //         { Dt.Ctor1?(G,d) }
      //         $Is(d, T(G)) ==> Dt.Ctor0?(G,d) || Dt.Ctor1?(G,d) || ...);
      {
        List<Bpl.Expr> tyexprs;
        var tyvars = MkTyParamBinders(dt.TypeArgs, out tyexprs);
        Bpl.Expr d;
        var dVar = BplBoundVar("d", predef.DatatypeType, out d);
        var d_is = MkIs(d, ClassTyCon(dt, tyexprs));
        Bpl.Expr cases_body = Bpl.Expr.False;
        Bpl.Trigger tr = null;
        foreach (DatatypeCtor ctor in dt.Ctors) {
          var disj = FunctionCall(ctor.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, d);
          cases_body = BplOr(cases_body, disj);
          tr = new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { disj, d_is }, tr);
        }
        var body = Bpl.Expr.Imp(d_is, cases_body);
        var ax = BplForall(Snoc(tyvars, dVar), tr, body);
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(dt.tok, ax, "Questionmark data type disjunctivity"));
      }

      if (dt is CoDatatypeDecl) {
        var codecl = (CoDatatypeDecl)dt;

        Func<Bpl.Expr, Bpl.Expr> MinusOne = k => {
          if (k == null) {
            return null;
          } else {
            return Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
          };
        };

        Action<bool, Action<Tuple<List<Type>, List<Type>>, List<Bpl.Variable>, List<Bpl.Expr>, List<Bpl.Expr>, Bpl.Variable, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr>> CoAxHelper = (add_k, K) => {
          Func<string, List<TypeParameter>> renew = s => 
            Map(codecl.TypeArgs, tp => 
              new TypeParameter(tp.tok, tp.Name + "#" + s, tp.PositionalIndex, tp.Parent));
          List<TypeParameter> typaramsL = renew("l"), typaramsR = renew("r");
          List<Bpl.Expr> lexprs; var lvars = MkTyParamBinders(typaramsL, out lexprs);
          List<Bpl.Expr> rexprs; var rvars = MkTyParamBinders(typaramsR, out rexprs);
          Func<List<TypeParameter>, List<Type>> Types = l => Map(l, tp => (Type)new UserDefinedType(tp));
          var tyargs = Tuple.Create(Types(typaramsL), Types(typaramsR));

          var vars = Concat(lvars, rvars);

          Bpl.Expr k, kGtZero;
          Bpl.Variable kVar;
          if (add_k) {
            kVar = BplBoundVar("k", Bpl.Type.Int, out k); vars.Add(kVar);
            kGtZero = Bpl.Expr.Lt(Bpl.Expr.Literal(0), k);
          } else {
            kVar = null; k = null; kGtZero = Bpl.Expr.True;
          }
          var ly = BplBoundVar("ly", predef.LayerType, vars); 
          var d0 = BplBoundVar("d0", predef.DatatypeType, vars);
          var d1 = BplBoundVar("d1", predef.DatatypeType, vars); 

          K(tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1);
        };

        Action<Boolean> AddAxioms = add_k => {
          {
            // Add two copies of the type parameter lists!
            var args = MkTyParamFormals(Concat(GetTypeParams(dt), GetTypeParams(dt)), false);
            if (add_k) {
              args.Add(BplFormalVar(null, Bpl.Type.Int, true));
            }
            args.Add(BplFormalVar(null, predef.LayerType, true));
            args.Add(BplFormalVar(null, predef.DatatypeType, true));
            args.Add(BplFormalVar(null, predef.DatatypeType, true));
            var r = BplFormalVar(null, Bpl.Type.Bool, false);
            var fn_nm = add_k ? CoPrefixName(codecl) : CoEqualName(codecl);
            var fn = new Bpl.Function(dt.tok, fn_nm, args, r);
            if (InsertChecksums) {
              InsertChecksum(dt, fn);
            }
            sink.TopLevelDeclarations.Add(fn);
          }

          // axiom (forall G0,...,Gn : Ty, k: int, ly : Layer, d0, d1: DatatypeType :: 
          //  { Eq(G0, .., Gn, S(ly), k, d0, d1) } 
          //  Is(d0, T(G0, .., Gn)) && Is(d1, T(G0, ... Gn)) ==>
          //  (Eq(G0, .., Gn, S(ly), k, d0, d1)
          //    <==>
          //      0 < k ==>
          //        (d0.Nil? && d1.Nil?) ||
          //        (d0.Cons? && d1.Cons? && d0.head == d1.head && Eq(G0, .., Gn, ly, k-1, d0.tail, d1.tail)))
          CoAxHelper(add_k, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
            var eqDt = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var iss = BplAnd(MkIs(d0, ClassTyCon(dt, lexprs)), MkIs(d1, ClassTyCon(dt, rexprs)));
            var body = BplImp(
              iss,
              BplIff(eqDt,
                BplImp(kGtZero, BplOr(CoPrefixEquality(dt.tok, codecl, tyargs.Item1, tyargs.Item2, MinusOne(k), ly, d0, d1)))));
            var ax = BplForall(vars, BplTrigger(eqDt), body);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(dt.tok, ax, "Layered co-equality axiom"));
          });

          // axiom (forall G0,...,Gn : Ty, k: int, ly : Layer, d0, d1: DatatypeType :: 
          //  { Eq(G0, .., Gn, S(ly), k, d0, d1) } 
          //    0 < k ==>
          //      (Eq(G0, .., Gn, S(ly), k, d0, d1) <==>
          //       Eq(G0, .., Gn, ly, k, d0, d))
          CoAxHelper(add_k, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
            var eqDtSL = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var eqDtL  = CoEqualCall(codecl, lexprs, rexprs, k, ly, d0, d1);
            var body = BplImp(kGtZero, BplIff(eqDtSL, eqDtL));
            var ax = BplForall(vars, BplTrigger(eqDtSL), body);
            sink.TopLevelDeclarations.Add(new Bpl.Axiom(dt.tok, ax, "Unbump layer co-equality axiom"));
          });
        };

        AddAxioms(false); // Add the above axioms for $Equal

        // axiom (forall d0, d1: DatatypeType, k: int :: { $Equal(d0, d1) } :: Equal(d0, d1) <==> d0 == d1);
        CoAxHelper(false, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
          var Eq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var equal = Bpl.Expr.Eq(d0, d1);
          sink.TopLevelDeclarations.Add(new Axiom(dt.tok,
            BplForall(vars, BplTrigger(Eq), BplIff(Eq, equal)),
            "Equality for codatatypes"));
        });

        AddAxioms(true); // Add the above axioms for $PrefixEqual

        // The connection between the full codatatype equality and its prefix version
        // axiom (forall d0, d1: DatatypeType :: $Eq#Dt(d0, d1) <==>
        //                                       (forall k: int :: 0 <= k ==> $PrefixEqual#Dt(k, d0, d1)));
        CoAxHelper(true, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
          var Eq = CoEqualCall(codecl, lexprs, rexprs, null, LayerSucc(ly), d0, d1);
          var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          vars.Remove(kVar);
          sink.TopLevelDeclarations.Add(new Axiom(dt.tok,
            BplForall(vars, BplTrigger(Eq), BplIff(Eq, BplForall(kVar, BplTrigger(PEq), BplImp(kGtZero, PEq)))),
            "Coequality and prefix equality connection"));
        });

        // A consequence of the definition of prefix equalities is the following:
        // axiom (forall k, m: int, d0, d1: DatatypeType :: 0 <= k <= m && $PrefixEq#Dt(m, d0, d1) ==> $PrefixEq#0#Dt(k, d0, d1));
        CoAxHelper(true, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
          var m = BplBoundVar("m", Bpl.Type.Int, vars);
          var PEqK = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var PEqM = CoEqualCall(codecl, lexprs, rexprs, m, LayerSucc(ly), d0, d1);
          var kLtM = Bpl.Expr.Lt(k, m);
          sink.TopLevelDeclarations.Add(new Axiom(dt.tok,
            BplForall(vars,
            new Bpl.Trigger(dt.tok, true, new List<Bpl.Expr> { PEqK, PEqM }),
            BplImp(BplAnd(BplAnd(kGtZero, kLtM), PEqM), PEqK)),
            "Prefix equality consequence"));
        });

        // With the axioms above, going from d0==d1 to a prefix equality requires going via the full codatatype
        // equality, which in turn requires the full codatatype equality to be present.  The following axiom
        // provides a shortcut:
        // axiom (forall d0, d1: DatatypeType, k: int :: d0 == d1 && 0 <= k ==> $PrefixEqual#_module.Stream(k, d0, d1));
        CoAxHelper(true, (tyargs, vars, lexprs, rexprs, kVar, k, kGtZero, ly, d0, d1) => {
          var equal = Bpl.Expr.Eq(d0, d1);
          var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          sink.TopLevelDeclarations.Add(new Axiom(dt.tok,
            BplForall(vars, null, BplImp(BplAnd(equal, kGtZero), PEq)),
            "Prefix equality shortcut"));
        });
      }
    }

    /// <summary>
    /// Return a sequence of expressions whose conjunction denotes a memberwise equality of "dt".  Recursive
    /// codatatype equalities are written in one of the following ways:
    /// If the codatatype equality is on a type outside the SCC of "dt", then resort to ordinary equality.
    /// Else if the k==null, then:
    ///   Depending on "limited", use the #2, #1, or #0 (limited) form of codatatype equality.
    /// Else:
    ///   Depending on "limited", use the #2, #1, or #0 (limited) form of prefix equality, passing "k"
    ///   as the first argument.
    /// </summary>
    IEnumerable<Bpl.Expr> CoPrefixEquality(IToken tok, CoDatatypeDecl dt, List<Type> largs, List<Type> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, bool conjuncts = false) {
      Contract.Requires(tok != null);
      Contract.Requires(dt != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      Contract.Requires(l != null);
      Contract.Requires(predef != null);
      var etran = new ExpressionTranslator(this, predef, dt.tok);
      // For example, for possibly infinite lists:
      //     codatatype SList<T> = Nil | SCons(head: T, tail: SList<T>);
      // produce with conjucts=false (default):
      //   (A.Nil? && B.Nil?) ||
      //   (A.Cons? && B.Cons? && A.head == B.head && Equal(k, A.tail, B.tail))
      // 
      // with conjuncts=true:
      //   (A.Nil? ==> B.Nil?) &&
      //   (A.Cons? ==> (B.Cons? && A.head == B.head && Equal(k, A.tail, B.tail)))

      Dictionary<TypeParameter, Type> lsu = Util.Dict(GetTypeParams(dt), largs);
      Dictionary<TypeParameter, Type> rsu = Util.Dict(GetTypeParams(dt), rargs);

      foreach (var ctor in dt.Ctors) {
        Bpl.Expr aq = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(GetReadonlyField(ctor.QueryField)), new List<Bpl.Expr> { A });
        Bpl.Expr bq = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(GetReadonlyField(ctor.QueryField)), new List<Bpl.Expr> { B });
        Bpl.Expr chunk = Bpl.Expr.True;
        foreach (var dtor in ctor.Destructors) {  // note, ctor.Destructors has a field for every constructor parameter, whether or not the parameter was named in the source
          var a = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { A });
          var b = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { B });
          var ty = dtor.Type;
          Bpl.Expr q;
          var codecl = ty.AsCoDatatype;
          if (codecl != null && codecl.SscRepr == dt.SscRepr) {
            var lexprs = Map(ty.TypeArgs, tt => Resolver.SubstType(tt, lsu));
            var rexprs = Map(ty.TypeArgs, tt => Resolver.SubstType(tt, rsu));
            q = CoEqualCall(codecl, lexprs, rexprs, k, l, a, b);
          } else { 
            // ordinary equality; let the usual translation machinery figure out the translation
            var equal = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, new BoogieWrapper(a, ty), new BoogieWrapper(b, ty));
            equal.ResolvedOp = Resolver.ResolveOp(equal.Op, ty);  // resolve here
            equal.Type = Type.Bool;  // resolve here
            q = etran.TrExpr(equal);
          }
          chunk = BplAnd(chunk, q);
        }
        if (conjuncts) {
          yield return Bpl.Expr.Binary(new NestedToken(tok, ctor.tok), BinaryOperator.Opcode.Imp, aq, BplAnd(bq, chunk));
        } else {
          yield return BplAnd(BplAnd(aq, bq), BplImp(BplAnd(aq, bq), chunk));  
        }
      }
    }

    Bpl.Expr LayerSucc(Bpl.Expr e, int amt = 1) {
      if (amt == 0) {
        return e;
      } else if (amt > 0) {
        return FunctionCall(e.tok, BuiltinFunction.LayerSucc, null, LayerSucc(e, amt-1));
      } else {
        Contract.Assert(false);
        return null;
      }
    }

    // Makes a call to equality, if k is null, or otherwise prefix equality. For codatatypes.
    Bpl.Expr CoEqualCall(CoDatatypeDecl codecl, List<Bpl.Expr> largs, List<Bpl.Expr> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, IToken tok = null) {
      Contract.Requires(codecl != null);
      Contract.Requires(largs != null);
      Contract.Requires(rargs != null);
      Contract.Requires(l != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      if (tok == null) {
        tok = A.tok;
      }
      List<Bpl.Expr> args = Concat(largs, rargs);
      if (k != null) { 
        args.Add(k);
      }
      args.AddRange(new List<Bpl.Expr> { l, A, B });
      var fn = k == null ? CoEqualName(codecl) : CoPrefixName(codecl);
      return FunctionCall(tok, fn, Bpl.Type.Bool, args);
    }

    // Same as above, but with Dafny-typed type-argument lists
    Bpl.Expr CoEqualCall(CoDatatypeDecl codecl, List<Type> largs, List<Type> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, IToken tok = null) {
      Contract.Requires(codecl != null);
      Contract.Requires(largs != null);
      Contract.Requires(rargs != null);
      Contract.Requires(l != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      return CoEqualCall(codecl, Map(largs, TypeToTy), Map(rargs, TypeToTy), k, l, A, B, tok);
    }

    static string CoEqualName(CoDatatypeDecl codecl) {
      Contract.Requires(codecl != null);
      return "$Eq#" + codecl.FullSanitizedName;
    }

    static string CoPrefixName(CoDatatypeDecl codecl) {
      Contract.Requires(codecl != null);
      return "$PrefixEq#" + codecl.FullSanitizedName;
    }

    void CreateBoundVariables(List<Formal/*!*/>/*!*/ formals, out List<Variable>/*!*/ bvs, out List<Bpl.Expr/*!*/>/*!*/ args)
    {
      Contract.Requires(formals != null);
      Contract.Ensures(Contract.ValueAtReturn(out bvs).Count == Contract.ValueAtReturn(out args).Count);
      Contract.Ensures(Contract.ValueAtReturn(out bvs) != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out args)));

      bvs = new List<Variable>();
      args = new List<Bpl.Expr>();
      foreach (Formal arg in formals) {
        Contract.Assert(arg != null);
        var nm = string.Format("a{0}#{1}", bvs.Count, otherTmpVarCount);
        otherTmpVarCount++;
        Bpl.Variable bv = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, nm, TrType(arg.Type)));
        bvs.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.tok, bv));
      }
    }

    // This one says that this is /directly/ allocated, not that its "children" are,
    // i.e. h[x, alloc]
    public Bpl.Expr IsAlloced(IToken tok, Bpl.Expr heapExpr, Bpl.Expr e) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return ReadHeap(tok, heapExpr, e, predef.Alloc(tok));
    }

    public static Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r, Expr f) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      List<Bpl.Expr> args = new List<Bpl.Expr>();
      args.Add(heap);
      args.Add(r);
      args.Add(f);
      Bpl.Type t = (f.Type != null) ? f.Type : f.ShallowType;
      return new Bpl.NAryExpr(tok,
        new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "read", t.AsCtor.Arguments[0])),
        args);
    }

    public Bpl.Expr DType(Bpl.Expr e, Bpl.Expr type) {
      return Bpl.Expr.Eq(FunctionCall(e.tok, BuiltinFunction.DynamicType, null, e), type);
    }

    public Bpl.Expr GetArrayIndexFieldName(IToken tok, List<Bpl.Expr> indices) {
      Bpl.Expr fieldName = null;
      foreach (Bpl.Expr index in indices) {
        if (fieldName == null) {
          // the index in dimension 0:  IndexField(index0)
          fieldName = FunctionCall(tok, BuiltinFunction.IndexField, null, index);
        } else {
          // the index in dimension n:  MultiIndexField(...field name for first n indices..., index_n)
          fieldName = FunctionCall(tok, BuiltinFunction.MultiIndexField, null, fieldName, index);
        }
      }
      return fieldName;
    }

    void AddClassMembers(ClassDecl c)
    {
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(c != null);

      sink.TopLevelDeclarations.Add(GetClass(c));
      if (c is ArrayClassDecl) {
        // classes.Add(c, predef.ClassDotArray);
        AddAllocationAxiom(null, c, true);
      }

      /* // Add $Is and $IsAlloc for this class :
            axiom (forall p: ref, G: Ty ::
               { $Is(p, TClassA(G), h) }
               $Is(p, TClassA(G), h) <=> (p == null || dtype(p) == TClassA(G));
            axiom (forall p: ref, h: Heap, G: Ty ::
               { $IsAlloc(p, TClassA(G), h) }
               $IsAlloc(p, TClassA(G), h) => (p == null || h[p, alloc]);
      */

      if (!(c is TraitDecl))
      {
          MapM(Bools, is_alloc =>
          {
              List<Bpl.Expr> tyexprs;
              var vars = MkTyParamBinders(GetTypeParams(c), out tyexprs);

              var o = BplBoundVar("$o", predef.RefType, vars);

              Bpl.Expr body, is_o;
              Bpl.Expr o_null = Bpl.Expr.Eq(o, predef.Null);
              Bpl.Expr o_ty = ClassTyCon(c, tyexprs);
              string name;

              if (is_alloc)
              {
                  name = c + ": Class $IsAlloc";
                  var h = BplBoundVar("$h", predef.HeapType, vars);
                  // $IsAlloc(o, ..)
                  is_o = MkIsAlloc(o, o_ty, h);
                  body = BplIff(is_o, BplOr(o_null, IsAlloced(c.tok, h, o)));
              }
              else
              {
                  name = c + ": Class $Is";
                  // $Is(o, ..)
                  is_o = MkIs(o, o_ty);
                  Bpl.Expr rhs;
                  if (c == program.BuiltIns.ObjectDecl)
                  {
                      rhs = Bpl.Expr.True;
                  }
                  else
                  {
                      //generating $o == null || implements$J(dtype(x))
                      if (c is TraitDecl)
                      {
                          var t = (TraitDecl)c;
                          var dtypeFunc = FunctionCall(o.tok, BuiltinFunction.DynamicType, null, o);
                          Bpl.Expr implementsFunc = FunctionCall(t.tok, "implements$" + t.Name, Bpl.Type.Bool, new List<Expr> { dtypeFunc });
                          rhs = BplOr(o_null, implementsFunc);
                      }
                      else
                      {
                          rhs = BplOr(o_null, DType(o, o_ty));
                      }
                  }
                  body = BplIff(is_o, rhs);
              }

              sink.TopLevelDeclarations.Add(new Bpl.Axiom(c.tok, BplForall(vars, BplTrigger(is_o), body), name));
          });
      }

      //this adds: function implements$J(ClassName): bool;
      if (c is TraitDecl)
      {
          var arg_ref = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.Ty), true);
          var res = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
          var implement_intr = new Bpl.Function(c.tok, "implements$" + c.Name, new List<Variable> { arg_ref }, res);
          sink.TopLevelDeclarations.Add(implement_intr);
      }
      //this adds: axiom implements$J(class.C); 
      else if (c is ClassDecl)
      {
          if (c.Trait != null)
          {
              //var dtypeFunc = FunctionCall(c.tok, BuiltinFunction.DynamicType, null, o);
              //Bpl.Expr implementsFunc = FunctionCall(t.tok, "implements$" + t.Name, Bpl.Type.Bool, new List<Expr> { dtypeFunc });

              var args = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.ClassNameType), true);
              var ret_value = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
              var funCall = new Bpl.FunctionCall(new Bpl.Function(c.tok, "implements$" + c.TraitId.val, new List<Variable> { args }, ret_value));
              var expr = new Bpl.NAryExpr(c.tok, funCall, new List<Expr> { new Bpl.IdentifierExpr(c.tok, string.Format("class.{0}", c.FullSanitizedName), predef.ClassNameType) });
              var implements_axiom = new Bpl.Axiom(c.tok, expr);
              sink.TopLevelDeclarations.Add(implements_axiom);
          }
      }
       
      foreach (MemberDecl member in c.Members) {
        currentDeclaration = member;
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

          AddAllocationAxiom(f, c);

        } else if (member is Function) {
          var f = (Function)member;
          AddClassMember_Function(f);
          if (!IsOpaqueFunction(f) && !f.IsBuiltin && !(f.tok is IncludeToken)) { // Opaque function's well-formedness is checked on the full version
            AddWellformednessCheck(f);
            if (f.OverriddenFunction != null) //it means that f is overriding its associated parent function
            {
                AddFunctionOverrideCheckImpl(f);
            }
          }
          var cop = f as CoPredicate;
          if (cop != null) {
            AddClassMember_Function(cop.PrefixPredicate);
            // skip the well-formedness check, because it has already been done for the copredicate
          }

        } else if (member is Method) {
          Method m = (Method)member;

          // wellformedness check for method specification
          if (m.EnclosingClass is IteratorDecl && m == ((IteratorDecl)m.EnclosingClass).Member_MoveNext) {
            // skip the well-formedness check, because it has already been done for the iterator
          } else {
            var proc = AddMethod(m, MethodTranslationKind.SpecWellformedness);
            sink.TopLevelDeclarations.Add(proc);
            if (!(m.tok is IncludeToken)) {
              AddMethodImpl(m, proc, true);
            }
            if (m.OverriddenMethod != null) //method has overrided a parent method
            {
                var procOverrideChk = AddMethod(m, MethodTranslationKind.OverrideCheck);
                sink.TopLevelDeclarations.Add(procOverrideChk);
                AddMethodOverrideCheckImpl(m, procOverrideChk);
            }
          }
          // the method spec itself
          sink.TopLevelDeclarations.Add(AddMethod(m, MethodTranslationKind.InterModuleCall));
          sink.TopLevelDeclarations.Add(AddMethod(m, MethodTranslationKind.IntraModuleCall));
          if (m is CoLemma) {
            // Let the CoCall and Impl forms to use m.PrefixLemma signature and specification (and
            // note that m.PrefixLemma.Body == m.Body.
            m = ((CoLemma)m).PrefixLemma;
            sink.TopLevelDeclarations.Add(AddMethod(m, MethodTranslationKind.CoCall));
          }
          if (m.Body != null && !(m.tok is IncludeToken)) {
            // ...and its implementation
            var proc = AddMethod(m, MethodTranslationKind.Implementation);
            sink.TopLevelDeclarations.Add(proc);
            AddMethodImpl(m, proc, false);
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    private bool IsOpaqueFunction(Function f) {
      return Attributes.Contains(f.Attributes, "opaque") &&
            !Attributes.Contains(f.Attributes, "opaque_full");  // The full version has both attributes
    }

    private void AddClassMember_Function(Function f) {
      // declare function
      AddFunction(f);
      // add synonym axiom
      if (f.IsRecursive) {
        AddSynonymAxiom(f);
      }
      // add frame axiom
      AddFrameAxiom(f);
      // add consequence axiom
      sink.TopLevelDeclarations.Add(FunctionConsequenceAxiom(f, f.Ens));
      // add definition axioms, suitably specialized for "match" cases and for literals
      if (f.Body != null && !IsOpaqueFunction(f)) {
        AddFunctionAxiom(f, FunctionAxiomVisibility.IntraModuleOnly, f.Body.Resolved);
        AddFunctionAxiom(f, FunctionAxiomVisibility.ForeignModuleOnly, f.Body.Resolved);
      }  
      // for body-less functions, at least generate its #requires function
      if (f.Body == null) {
        var b = FunctionAxiom(f, FunctionAxiomVisibility.ForeignModuleOnly, null, null);
        Contract.Assert(b == null);
      }
      // supply the connection between co-predicates and prefix predicates
      if (f is CoPredicate) {
        AddPrefixPredicateAxioms(((CoPredicate)f).PrefixPredicate);
      }
    }

    void AddIteratorSpecAndBody(IteratorDecl iter) {
      Contract.Requires(iter != null);

      // wellformedness check for method specification
      Bpl.Procedure proc = AddIteratorProc(iter, MethodTranslationKind.SpecWellformedness);
      sink.TopLevelDeclarations.Add(proc);
      AddIteratorWellformed(iter, proc);
      // the method itself
      if (iter.Body != null) {
        proc = AddIteratorProc(iter, MethodTranslationKind.Implementation);
        sink.TopLevelDeclarations.Add(proc);
        // ...and its implementation
        AddIteratorImpl(iter, proc);
      }
    }

    Bpl.Procedure AddIteratorProc(IteratorDecl iter, MethodTranslationKind kind) {
      Contract.Requires(iter != null);
      Contract.Requires(kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation);
      Contract.Requires(predef != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);

      currentModule = iter.Module;
      codeContext = iter;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, iter.tok);

      List<Variable> inParams, outParams;
      GenerateMethodParametersChoose(iter.tok, iter, kind, true, true, false, etran, out inParams, out outParams);

      var req = new List<Bpl.Requires>();
      var mod = new List<Bpl.IdentifierExpr>();
      var ens = new List<Bpl.Ensures>();
      // FREE PRECONDITIONS
      if (kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation) {  // the other cases have no need for a free precondition
        // free requires mh == ModuleContextHeight && fh = FunctionContextHeight;
        req.Add(Requires(iter.tok, true, etran.HeightContext(iter), null, null));
      }
      mod.Add((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr);
      mod.Add(etran.Tick());

      if (kind != MethodTranslationKind.SpecWellformedness) {
        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined preconditions";
        foreach (var p in iter.Requires) {
          if (p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
            req.Add(Requires(p.E.tok, true, etran.TrExpr(p.E), null, comment));
            comment = null;
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, kind == MethodTranslationKind.InterModuleCall ? 0 : int.MaxValue, true, out splitHappened)) {
              if (kind == MethodTranslationKind.IntraModuleCall && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this precondition was inherited into this module, so just ignore it
              } else {
                req.Add(Requires(s.E.tok, s.IsOnlyFree, s.E, null, comment));
                comment = null;
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }
        comment = "user-defined postconditions";
        foreach (var p in iter.Ensures) {
          if (p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
            ens.Add(Ensures(p.E.tok, true, etran.TrExpr(p.E), null, comment));
            comment = null;
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, kind == MethodTranslationKind.InterModuleCall ? 0 : int.MaxValue, true, out splitHappened)) {
              if (kind == MethodTranslationKind.Implementation && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this postcondition was inherited into this module, so just ignore it
              } else {
                ens.Add(Ensures(s.E.tok, s.IsOnlyFree, s.E, null, comment));
                comment = null;
              }
            }
          }
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(iter.tok, iter.Modifies.Expressions, false, etran.Old, etran, etran.Old)) {
          ens.Add(Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
        }
      }

      var typeParams = TrTypeParamDecls(iter.TypeArgs);
      var name = MethodName(iter, kind);
      var proc = new Bpl.Procedure(iter.tok, name, typeParams, inParams, outParams, req, mod, ens, etran.TrAttributes(iter.Attributes, null));

      currentModule = null;
      codeContext = null;

      return proc;
    }

    void AddIteratorWellformed(IteratorDecl iter, Procedure proc) {
      currentModule = iter.Module;
      codeContext = iter;

      List<Bpl.TypeVariable> typeParams = TrTypeParamDecls(iter.TypeArgs);
      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      var builder = new Bpl.StmtListBuilder();
      var etran = new ExpressionTranslator(this, predef, iter.tok);
      var localVariables = new List<Variable>();

      Bpl.StmtList stmts;
      // check well-formedness of the preconditions, and then assume each one of them
      foreach (var p in iter.Requires) {
        CheckWellformed(p.E, new WFOptions(), localVariables, builder, etran);
        builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }
      // check well-formedness of the modifies and reads clauses
      CheckFrameWellFormed(new WFOptions(), iter.Modifies.Expressions, localVariables, builder, etran);
      CheckFrameWellFormed(new WFOptions(), iter.Reads.Expressions, localVariables, builder, etran);
      // check well-formedness of the decreases clauses
      foreach (var p in iter.Decreases.Expressions) {
        CheckWellformed(p, new WFOptions(), localVariables, builder, etran);
      }

      // Next, we assume about this.* whatever we said that the iterator constructor promises
      foreach (var p in iter.Member_Init.Ens) {
        builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }

      // play havoc with the heap, except at the locations prescribed by (this._reads - this._modifies - {this})
      var th = new ThisExpr(iter.tok);
      th.Type = Resolver.GetThisType(iter.tok, iter);  // resolve here
      var rds = new MemberSelectExpr(iter.tok, th, iter.Member_Reads.Name);
      rds.Member = iter.Member_Reads;  // resolve here
      rds.Type = iter.Member_Reads.Type;  // resolve here
      var mod = new MemberSelectExpr(iter.tok, th, iter.Member_Modifies.Name);
      mod.Member = iter.Member_Modifies;  // resolve here
      mod.Type = iter.Member_Modifies.Type;  // resolve here
      builder.Add(new Bpl.CallCmd(iter.tok, "$IterHavoc0",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(mod) },
        new List<Bpl.IdentifierExpr>()));

      // assume the automatic yield-requires precondition (which is always well-formed):  this.Valid()
      var validCall = new FunctionCallExpr(iter.tok, "Valid", th, iter.tok, new List<Expression>());
      validCall.Function = iter.Member_Valid;  // resolve here
      validCall.Type = Type.Bool;  // resolve here

      validCall.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>();  
      foreach (var p in iter.TypeArgs) {
        validCall.TypeArgumentSubstitutions[p] = new UserDefinedType(p);
      } // resolved here.

      builder.Add(new Bpl.AssumeCmd(iter.tok, etran.TrExpr(validCall)));

      // check well-formedness of the user-defined part of the yield-requires
      foreach (var p in iter.YieldRequires) {
        CheckWellformed(p.E, new WFOptions(), localVariables, builder, etran);
        builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }

      // save the heap (representing the state where yield-requires holds):  $_OldIterHeap := Heap;
      var oldIterHeap = new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, "$_OldIterHeap", predef.HeapType));
      localVariables.Add(oldIterHeap);
      builder.Add(Bpl.Cmd.SimpleAssign(iter.tok, new Bpl.IdentifierExpr(iter.tok, oldIterHeap), etran.HeapExpr));
      // simulate a modifies this, this._modifies, this._new;
      var nw = new MemberSelectExpr(iter.tok, th, iter.Member_New.Name);
      nw.Member = iter.Member_New;  // resolve here
      nw.Type = iter.Member_New.Type;  // resolve here
      builder.Add(new Bpl.CallCmd(iter.tok, "$IterHavoc1",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(mod), etran.TrExpr(nw) },
        new List<Bpl.IdentifierExpr>()));
      // assume the implicit postconditions promised by MoveNext:
      // assume fresh(_new - old(_new));
      var yeEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, new Bpl.IdentifierExpr(iter.tok, "$_OldIterHeap", predef.HeapType));
      var old_nw = new OldExpr(iter.tok, nw);
      old_nw.Type = nw.Type;  // resolve here
      var setDiff = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Sub, nw, old_nw);
      setDiff.ResolvedOp = BinaryExpr.ResolvedOpcode.SetDifference; setDiff.Type = nw.Type;  // resolve here
      Expression cond = new UnaryOpExpr(iter.tok, UnaryOpExpr.Opcode.Fresh, setDiff);
      cond.Type = Type.Bool;  // resolve here
      builder.Add(new Bpl.AssumeCmd(iter.tok, yeEtran.TrExpr(cond)));

      // check wellformedness of postconditions
      var yeBuilder = new Bpl.StmtListBuilder();
      var endBuilder = new Bpl.StmtListBuilder();
      // In the yield-ensures case:  assume this.Valid();
      yeBuilder.Add(new Bpl.AssumeCmd(iter.tok, yeEtran.TrExpr(validCall)));
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var thisY = new MemberSelectExpr(iter.tok, th, y.Name);
        thisY.Member = y; thisY.Type = y.Type;  // resolve here
        var thisYs = new MemberSelectExpr(iter.tok, th, ys.Name);
        thisYs.Member = ys; thisYs.Type = ys.Type;  // resolve here
        var oldThisYs = new OldExpr(iter.tok, thisYs);
        oldThisYs.Type = thisYs.Type;  // resolve here
        var singleton = new SeqDisplayExpr(iter.tok, new List<Expression>() { thisY });
        singleton.Type = thisYs.Type;  // resolve here
        var concat = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add, oldThisYs, singleton);
        concat.ResolvedOp = BinaryExpr.ResolvedOpcode.Concat; concat.Type = oldThisYs.Type;  // resolve here

        // In the yield-ensures case:  assume this.ys == old(this.ys) + [this.y];
        yeBuilder.Add(new Bpl.AssumeCmd(iter.tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(concat))));
        // In the ensures case:  assume this.ys == old(this.ys);
        endBuilder.Add(new Bpl.AssumeCmd(iter.tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(oldThisYs))));
      }

      foreach (var p in iter.YieldEnsures) {
        CheckWellformed(p.E, new WFOptions(), localVariables, yeBuilder, yeEtran);
        yeBuilder.Add(new Bpl.AssumeCmd(p.E.tok, yeEtran.TrExpr(p.E)));
      }
      foreach (var p in iter.Ensures) {
        CheckWellformed(p.E, new WFOptions(), localVariables, endBuilder, yeEtran);
        endBuilder.Add(new Bpl.AssumeCmd(p.E.tok, yeEtran.TrExpr(p.E)));
      }
      builder.Add(new Bpl.IfCmd(iter.tok, null, yeBuilder.Collect(iter.tok), null, endBuilder.Collect(iter.tok)));

      stmts = builder.Collect(iter.tok);

      QKeyValue kv = etran.TrAttributes(iter.Attributes, null);

      Bpl.Implementation impl = new Bpl.Implementation(iter.tok, proc.Name,
        typeParams, inParams, new List<Variable>(),
        localVariables, stmts, kv);
      sink.TopLevelDeclarations.Add(impl);

      currentModule = null;
      codeContext = null;
      loopHeapVarCount = 0;
      otherTmpVarCount = 0;
      _tmpIEs.Clear();
    }

    void AddIteratorImpl(IteratorDecl iter, Bpl.Procedure proc) {
      Contract.Requires(iter != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(iter.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && yieldCountVariable == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);
      Contract.Ensures(currentModule == null && codeContext == null && yieldCountVariable == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);

      currentModule = iter.Module;
      codeContext = iter;

      List<TypeVariable> typeParams = TrTypeParamDecls(iter.TypeArgs);
      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      ExpressionTranslator etran = new ExpressionTranslator(this, predef, iter.tok);
      List<Variable> localVariables = new List<Variable>();
      GenerateIteratorImplPrelude(iter, inParams, new List<Variable>(), builder, localVariables);

      // add locals for the yield-history variables and the extra variables
      // Assume the precondition and postconditions of the iterator constructor method
      foreach (var p in iter.Member_Init.Req) {
        builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }
      foreach (var p in iter.Member_Init.Ens) {
        // these postconditions are two-state predicates, but that's okay, because we haven't changed anything yet
        builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }
      // add the _yieldCount variable, and assume its initial value to be 0
      yieldCountVariable = new Bpl.LocalVariable(iter.tok,
        new Bpl.TypedIdent(iter.tok, iter.YieldCountVariable.AssignUniqueName(currentDeclaration), TrType(iter.YieldCountVariable.Type)));
      yieldCountVariable.TypedIdent.WhereExpr = YieldCountAssumption(iter, etran);  // by doing this after setting "yieldCountVariable", the variable can be used by YieldCountAssumption
      localVariables.Add(yieldCountVariable);
      builder.Add(new Bpl.AssumeCmd(iter.tok, Bpl.Expr.Eq(new Bpl.IdentifierExpr(iter.tok, yieldCountVariable), Bpl.Expr.Literal(0))));
      // add a variable $_OldIterHeap
      var oih = new Bpl.IdentifierExpr(iter.tok, "$_OldIterHeap", predef.HeapType);
      Bpl.Expr wh = BplAnd(
        FunctionCall(iter.tok, BuiltinFunction.IsGoodHeap, null, oih),
        FunctionCall(iter.tok, BuiltinFunction.HeapSucc, null, oih, etran.HeapExpr));
      localVariables.Add(new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, "$_OldIterHeap", predef.HeapType, wh)));

      // do an initial YieldHavoc
      YieldHavoc(iter.tok, iter, builder, etran);

      // translate the body of the method
      var stmts = TrStmt2StmtList(builder, iter.Body, localVariables, etran);

      QKeyValue kv = etran.TrAttributes(iter.Attributes, null);

      Bpl.Implementation impl = new Bpl.Implementation(iter.tok, proc.Name,
        typeParams, inParams, new List<Variable>(),
        localVariables, stmts, kv);
      sink.TopLevelDeclarations.Add(impl);

      currentModule = null;
      codeContext = null;
      yieldCountVariable = null;
      loopHeapVarCount = 0;
      otherTmpVarCount = 0;
      _tmpIEs.Clear();
    }

    Bpl.Expr YieldCountAssumption(IteratorDecl iter, ExpressionTranslator etran) {
      Contract.Requires(iter != null);
      Contract.Requires(etran != null);
      Contract.Requires(yieldCountVariable != null);
      Bpl.Expr wh = Bpl.Expr.True;
      foreach (var ys in iter.OutsHistoryFields) {
        // add the conjunct:  _yieldCount == |this.ys|
        wh = Bpl.Expr.And(wh, Bpl.Expr.Eq(new Bpl.IdentifierExpr(iter.tok, yieldCountVariable),
          FunctionCall(iter.tok, BuiltinFunction.SeqLength, null,
          ReadHeap(iter.tok, etran.HeapExpr,
            new Bpl.IdentifierExpr(iter.tok, etran.This, predef.RefType),
            new Bpl.IdentifierExpr(iter.tok, GetField(ys))))));
      }
      return wh;
    }

    class Specialization
    {
      public readonly List<Formal/*!*/> Formals;
      public readonly List<Expression/*!*/> ReplacementExprs;
      public readonly List<BoundVar/*!*/> ReplacementFormals;
      public readonly Dictionary<IVariable, Expression> SubstMap;
      readonly Translator translator;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(Formals));
        Contract.Invariant(cce.NonNullElements(ReplacementExprs));
        Contract.Invariant(Formals.Count == ReplacementExprs.Count);
        Contract.Invariant(cce.NonNullElements(ReplacementFormals));
        Contract.Invariant(SubstMap != null);
      }

      public Specialization(IVariable formal, MatchCase mc, Specialization prev, Translator translator) {
        Contract.Requires(formal is Formal || formal is BoundVar);
        Contract.Requires(mc != null);
        Contract.Requires(prev == null || formal is BoundVar || !prev.Formals.Contains((Formal)formal));
        Contract.Requires(translator != null);

        this.translator = translator;

        List<Expression> rArgs = new List<Expression>();
        foreach (BoundVar p in mc.Arguments) {
          IdentifierExpr ie = new IdentifierExpr(p.tok, p.AssignUniqueName(translator.currentDeclaration));
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
            ReplacementExprs.Add(translator.Substitute(e, null, substMap));
          }
          foreach (var rf in prev.ReplacementFormals) {
            if (rf != formal) {
              ReplacementFormals.Add(rf);
            }
          }
          foreach (var entry in prev.SubstMap) {
            SubstMap.Add(entry.Key, translator.Substitute(entry.Value, null, substMap));
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

    void AddFunctionAxiom(Function f, FunctionAxiomVisibility visibility, Expression body) {
      Contract.Requires(f != null);
      Contract.Requires(body != null);

      var ax = FunctionAxiom(f, visibility, body, null);
      sink.TopLevelDeclarations.Add(ax);
      // TODO(namin) Is checking f.Reads.Count==0 excluding Valid() of BinaryTree in the right way?
      //             I don't see how this in the decreasing clause would help there.
      // danr: Let's create the literal function axioms if there is an arrow type in the signature
      if (!(f is CoPredicate) && (f.Reads.Count == 0 || f.Formals.Exists(a => a.Type is ArrowType))) {
        var FVs = new HashSet<IVariable>();
        bool usesHeap = false, usesOldHeap = false;
        Type usesThis = null;
        foreach (var e in f.Decreases.Expressions) {
          ComputeFreeVariables(e, FVs, ref usesHeap, ref usesOldHeap, ref usesThis, false);
        }
        var decs = new List<Formal>();
        foreach (var formal in f.Formals) {
          if (FVs.Contains(formal)) {
            decs.Add(formal);
          }
        }
        Contract.Assert(decs.Count <= f.Formals.Count);
        if (0 < decs.Count && decs.Count < f.Formals.Count) {
          ax = FunctionAxiom(f, visibility, body, decs);
          sink.TopLevelDeclarations.Add(ax);
        }
        ax = FunctionAxiom(f, visibility, body, f.Formals);
        sink.TopLevelDeclarations.Add(ax);
      }
    }

    enum FunctionAxiomVisibility { IntraModuleOnly, ForeignModuleOnly }

    Bpl.Axiom FunctionConsequenceAxiom(Function f, List<Expression> ens) {
      Contract.Requires(f != null);
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Ensures(Contract.Result<Bpl.Axiom>() != null);

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);

      // This method generate the Consequence Axiom, which has information about the function's
      // return type and postconditions
      //
      // axiom  // consequence axiom
      //   AXIOM_ACTIVATION
      //   ==>
      //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
      //       { f(s, args) }
      //       f#canCall(args) || USE_VIA_CONTEXT
      //       ==>
      //       ens &&
      //       f(s, args)-has-the-expected type);
      //
      // where:
      //
      // AXIOM_ACTIVATION
      // means:
      //   mh < ModuleContextHeight ||
      //   (mh == ModuleContextHeight && fh <= FunctionContextHeight)
      //
      // USE_VIA_CONTEXT
      //   (mh != ModuleContextHeight || fh != FunctionContextHeight) &&
      //   GOOD_PARAMETERS
      // where GOOD_PARAMETERS means:
      //   $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      //   Pre($Heap,formals)
      //
      // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
      // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
      // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
      // sound after that, then it would also have been sound just before the allocation.
      //      
      List<Bpl.Expr> tyargs;      
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
      var args = new List<Bpl.Expr>();
      Bpl.BoundVariable layer;
      if (f.IsRecursive) {
        layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
        formals.Add(layer);
        // Note, "layer" is not added to "args" here; rather, that's done below, as needed
      } else {
        layer = null;
      }
      var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      formals.Add(bv);
      args.Add(new Bpl.IdentifierExpr(f.tok, bv));
      // ante:  $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      Bpl.Expr ante = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);

      if (!f.IsStatic) {
        var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, predef.RefType));
        formals.Add(bvThis);
        var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        args.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(bvThisIdExpr, predef.Null),
          etran.GoodRef(f.tok, bvThisIdExpr, thisType));
        ante = Bpl.Expr.And(ante, wh);
      }
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (Formal p in f.Formals) {
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration), TrType(p.Type)));
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        formals.Add(bv);
        args.Add(formal);
        // add well-typedness conjunct to antecedent
        Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran);
        if (wh != null) { ante = Bpl.Expr.And(ante, wh); }
      }

      Bpl.Expr funcAppl;
      {
        var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        var funcArgs = new List<Bpl.Expr>();
        funcArgs.AddRange(tyargs);
        if (layer != null) {
          var ly = new Bpl.IdentifierExpr(f.tok, layer);
          funcArgs.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, ly));
        }
        funcArgs.AddRange(args);        
        funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
      }

      Bpl.Expr pre = Bpl.Expr.True;
      foreach (Expression req in f.Req) {
        pre = BplAnd(pre, etran.TrExpr(Substitute(req, null, substMap)));
      }
      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight)
      var mod = f.EnclosingClass.Module;
      Bpl.Expr useViaContext = Bpl.Expr.Or(
        Bpl.Expr.Neq(Bpl.Expr.Literal(mod.Height), etran.ModuleContextHeight()),
        Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight()));
      // useViaCanCall: f#canCall(args)
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

      // ante := useViaCanCall || (useViaContext && typeAnte && pre)
      ante = Bpl.Expr.Or(useViaCanCall, BplAnd(useViaContext, BplAnd(ante, pre)));

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { funcAppl });
      var typeParams = TrTypeParamDecls(f.TypeArgs);
      Bpl.Expr meat = Bpl.Expr.True;
      foreach (Expression p in ens) {
        Bpl.Expr q = etran.TrExpr(Substitute(p, null, substMap));
        meat = BplAnd(meat, q);
      }
      Bpl.Expr whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etran);
      if (whr != null) { meat = Bpl.Expr.And(meat, whr); }

      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, null, tr, Bpl.Expr.Imp(ante, meat));
      var activate = AxiomActivation(f, true, true, etran);
      string comment = "consequence axiom for " + f.FullSanitizedName;
      return new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    }

    Bpl.Expr AxiomActivation(Function f, bool interModule, bool intraModule, ExpressionTranslator etran) {
      Contract.Requires(f != null);
      Contract.Requires(interModule || intraModule);
      Contract.Requires(etran != null);
      var module = f.EnclosingClass.Module;
      // mh < ModuleContextHeight
      var activateForeignModule = Bpl.Expr.Lt(Bpl.Expr.Literal(module.Height), etran.ModuleContextHeight());
      // mh == ModuleContextHeight && fh <= FunctionContextHeight
      var activateIntraModule = Bpl.Expr.And(
        Bpl.Expr.Eq(Bpl.Expr.Literal(module.Height), etran.ModuleContextHeight()),
        Bpl.Expr.Le(Bpl.Expr.Literal(module.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight()));
      if (interModule && !intraModule) {
        return activateForeignModule;
      } else if (!interModule && intraModule) {
        return activateIntraModule;
      } else {
        return Bpl.Expr.Or(activateForeignModule, activateIntraModule);
      }
    }

    Bpl.Axiom FunctionAxiom(Function f, FunctionAxiomVisibility visibility, Expression body, ICollection<Formal> lits) {
      Contract.Requires(f != null);
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);

      // only if body is null, we will return null:
      Contract.Ensures((Contract.Result<Bpl.Axiom>() == null) == (body == null));

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);

      // This method generates the Definition Axiom, suitably modified according to the optional "lits".
      //
      // axiom  // definition axiom
      //   AXIOM_ACTIVATION
      //   ==>
      //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
      //       { f(Succ(s), args) }                      // (*)
      //       f#canCall(args) || USE_VIA_CONTEXT
      //       ==>
      //       BODY-can-make-its-calls &&
      //       f(Succ(s), args) == BODY);                // (*)
      //
      // where:
      //
      // AXIOM_ACTIVATION
      // for visibility==ForeignModuleOnly, means:
      //   mh < ModuleContextHeight
      // for visibility==IntraModuleOnly, means:
      //   mh == ModuleContextHeight && fh <= FunctionContextHeight
      //
      // USE_VIA_CONTEXT
      // for visibility==ForeignModuleOnly, means:
      //   GOOD_PARAMETERS
      // for visibility==IntraModuleOnly, means:
      //   fh != FunctionContextHeight &&
      //   GOOD_PARAMETERS
      // where GOOD_PARAMETERS means:
      //   $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      //   Pre($Heap,formals)
      // 
      // NOTE: this is lifted out to a #requires function for intra module calls,
      //       and used in the function pseudo-handles for top level functions.
      //       For body-less functions, this is emitted when body is null.
      //
      // BODY
      // means:
      //   the body of f translated with "s" as the layer argument
      //
      // The variables "formals" are the formals of function "f".
      // The list "args" is the list of formals of function "f".
      //
      // The translation of "body" uses "s" as the layer argument for intra-cluster calls and the default layer argument
      // (which is Succ(0)) for other calls.  Usually, the layer argument in the LHS of the definition (and also in the trigger,
      // see the two occurrences of (*) above) use Succ(s) as the layer argument.  However, if "lits" are specified, then
      // then the argument used is just "s" (in both the LHS and trigger).
      //
      // Note, an antecedent $Heap[this,alloc] is intentionally left out:  including it would only weaken
      // the axiom.  Moreover, leaving it out does not introduce any soundness problem, because the Dafny
      // allocation statement changes only an allocation bit and then re-assumes $IsGoodHeap; so if it is
      // sound after that, then it would also have been sound just before the allocation.
      //

      // quantify over the type arguments, and add them first to the arguments
      List<Bpl.Expr> args = new List<Bpl.Expr>();
      List<Bpl.Expr> tyargs;      
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);          

      Bpl.BoundVariable layer;
      if (f.IsRecursive) {
        layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
        formals.Add(layer);
        // Note, "layer" is not added to "args" here; rather, that's done below, as needed
      } else {
        layer = null;
      }
      var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      formals.Add(bv);
      args.Add(new Bpl.IdentifierExpr(f.tok, bv));
      // ante:  $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      Bpl.Expr ante = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);

      if (!f.IsStatic) {
        var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, predef.RefType));
        formals.Add(bvThis);
        var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        args.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(bvThisIdExpr, predef.Null),
          etran.GoodRef(f.tok, bvThisIdExpr, thisType));
        ante = Bpl.Expr.And(ante, wh);
      }

      var substMap = new Dictionary<IVariable, Expression>();
      foreach (Formal p in f.Formals) {
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration), TrType(p.Type)));
        formals.Add(bv);
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        if (lits != null && lits.Contains(p) && !substMap.ContainsKey(p)) {
          args.Add(Lit(formal));
          var ie = new IdentifierExpr(p.tok, p.AssignUniqueName(f));
          ie.Var = p; ie.Type = ie.Var.Type;
          var l = new UnaryOpExpr(p.tok, UnaryOpExpr.Opcode.Lit, ie);
          l.Type = ie.Var.Type;
          substMap.Add(p, l);
        } else {
          args.Add(formal);
        }
        // add well-typedness conjunct to antecedent
        Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran);
        if (wh != null) { ante = Bpl.Expr.And(ante, wh); }
      }

      Bpl.Expr pre = Bpl.Expr.True;
      foreach (Expression req in f.Req) {
        pre = BplAnd(pre, etran.TrExpr(Substitute(req, null, substMap)));
      }
      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight)
      ModuleDefinition mod = f.EnclosingClass.Module;
      Bpl.Expr useViaContext = visibility == FunctionAxiomVisibility.ForeignModuleOnly ? (Bpl.Expr)Bpl.Expr.True :
        Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight());

      // ante := (useViaContext && typeAnte && pre)
      ante = BplAnd(useViaContext, BplAnd(ante, pre));

      // Add the precondition function and its axiom (which is equivalent to the ante)
      if (body == null || (visibility == FunctionAxiomVisibility.IntraModuleOnly && lits == null)) {
        var precondF = new Bpl.Function(f.tok, 
          RequiresName(f), new List<Bpl.TypeVariable>(), 
          formals.ConvertAll(v => (Bpl.Variable)BplFormalVar(null, v.TypedIdent.Type, true)), 
          BplFormalVar(null, Bpl.Type.Bool, false));
        sink.TopLevelDeclarations.Add(precondF);
        var appl = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, 
          formals.ConvertAll(x => (Bpl.Expr)(new Bpl.IdentifierExpr(f.tok, x))));
        sink.TopLevelDeclarations.Add(new Axiom(f.tok, BplForall(formals, BplTrigger(appl), Bpl.Expr.Eq(appl, ante))));
        // you could use it to check that it always works, but it makes VSI-Benchmarks/b3.dfy time out:
        // ante = appl; 
        if (body == null) {
          return null;
        }
      }

      // useViaCanCall: f#canCall(args)
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs,args));

      // ante := useViaCanCall || (useViaContext && typeAnte && pre)
      ante = Bpl.Expr.Or(useViaCanCall, ante);

      Bpl.Expr funcAppl;
      {
        var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        var funcArgs = new List<Bpl.Expr>();
        funcArgs.AddRange(tyargs);
        if (layer != null) {
          var ly = new Bpl.IdentifierExpr(f.tok, layer);
          if (lits == null) {
            funcArgs.Add(LayerSucc(ly));
          } else {
            funcArgs.Add(ly);
          }
        }
        funcArgs.AddRange(args);
        funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
      }


      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { funcAppl });
      var typeParams = TrTypeParamDecls(f.TypeArgs);
      Bpl.Expr meat;
      if (visibility == FunctionAxiomVisibility.ForeignModuleOnly /* TODO: add 'public' feature and add: && !IsPublic(f) */) {
        meat = Bpl.Expr.True;
      } else {
        var bodyWithSubst = Substitute(body, null, substMap);
        if (f is PrefixPredicate) {
          var pp = (PrefixPredicate)f;
          bodyWithSubst = PrefixSubstitution(pp, bodyWithSubst);
        }
        var etranBody = layer == null ? etran : etran.LimitedFunctions(f, new Bpl.IdentifierExpr(f.tok, layer));
        meat = BplAnd(CanCallAssumption(bodyWithSubst, etranBody),
          Bpl.Expr.Eq(funcAppl, etranBody.TrExpr(bodyWithSubst)));
      }
      QKeyValue kv = null;
      if (lits != null) {
        kv = new QKeyValue(f.tok, "weight", new List<object>() { Bpl.Expr.Literal(3) }, null);
      }
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, kv, tr, Bpl.Expr.Imp(ante, meat));
      var activate = AxiomActivation(f, visibility == FunctionAxiomVisibility.ForeignModuleOnly, visibility == FunctionAxiomVisibility.IntraModuleOnly, etran);
      string comment;
      comment = "definition axiom for " + f.FullSanitizedName;
      if (lits != null) {
        if (lits.Count == f.Formals.Count) {
          comment += " for all literals";
        } else {
          comment += " for decreasing-related literals";
        }
      }
      if (visibility == FunctionAxiomVisibility.IntraModuleOnly) {
        comment += " (intra-module)";
      } else if (visibility == FunctionAxiomVisibility.ForeignModuleOnly) {
        comment += " (foreign modules)";
      }
      return new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    }

    /// <summary>
    /// For a copredicate P, "pp" is the prefix predicate for P (such that P = pp.Co) and
    /// "body" is the body of P.  Return what would be the body of the prefix predicate pp.
    /// In particular, return
    ///   0 LESS _k  IMPLIES  body'
    /// where body' is body with the formals of P replaced by the corresponding
    /// formals of pp and with corecursive calls P(s) replaced by recursive calls to
    /// pp(_k - 1, s).
    /// </summary>
    Expression PrefixSubstitution(PrefixPredicate pp, Expression body) {
      Contract.Requires(pp != null);

      var typeMap = Util.Dict<TypeParameter,Type>(pp.Co.TypeArgs, Map(pp.TypeArgs, x => new UserDefinedType(x))); 
      
      var paramMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < pp.Co.Formals.Count; i++) {
        var replacement = pp.Formals[i + 1];  // the +1 is to skip pp's _k parameter
        var param = new IdentifierExpr(replacement.tok, replacement.Name);
        param.Var = replacement;  // resolve here
        param.Type = replacement.Type;  // resolve here
        paramMap.Add(pp.Co.Formals[i], param);
      }

      var k = new IdentifierExpr(pp.tok, pp.K.Name);
      k.Var = pp.K;  // resolve here
      k.Type = pp.K.Type;  // resolve here
      var kMinusOne = Expression.CreateSubtract(k, Expression.CreateIntLiteral(pp.tok, 1));

      var s = new PrefixCallSubstituter(null, paramMap, typeMap, pp.Co, kMinusOne, this);
      body = s.Substitute(body);

      // add antecedent "0 < _k ==>"
      var kIsPositive = Expression.CreateLess(Expression.CreateIntLiteral(pp.tok, 0), k);
      return Expression.CreateImplies(kIsPositive, body);
    }

    void AddSynonymAxiom(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(f.IsRecursive);
      Contract.Requires(sink != null && predef != null);
      // axiom  // layer synonym axiom
      //   (forall s, $Heap, formals ::
      //       { f(Succ(s), $Heap, formals) }
      //       f(Succ(s), $Heap, formals) == f(s, $Heap, formals));

      List<Bpl.Expr> tyargs;
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
      var args1 = new List<Bpl.Expr>(tyargs);
      var args0 = new List<Bpl.Expr>(tyargs);

      var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
      formals.Add(bv);
      var s = new Bpl.IdentifierExpr(f.tok, bv);
      args1.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, s));
      args0.Add(s);

      bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      formals.Add(bv);
      s = new Bpl.IdentifierExpr(f.tok, bv);
      args1.Add(s);
      args0.Add(s);

      if (!f.IsStatic) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }
      foreach (var p in f.Formals) {
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }

      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
      var funcAppl1 = new Bpl.NAryExpr(f.tok, funcID, args1);
      var funcAppl0 = new Bpl.NAryExpr(f.tok, funcID, args0);

      var typeParams = TrTypeParamDecls(f.TypeArgs);

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { funcAppl1 });
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax, "layer synonym axiom"));
    }

    /// <summary>
    /// Add the axioms:
    ///   forall args :: P(args) ==> forall k: nat :: P#[k](args)
    ///   forall args :: (forall k: nat :: P#[k](args)) ==> P(args)
    ///   forall args,k :: k == 0 ==> P#[k](args)
    /// where "args" is "heap, formals".  In more details:
    ///   AXIOM_ACTIVATION ==> forall args :: { P(args) } args-have-appropriate-values && P(args) ==> forall k { P#[k](args) } :: 0 ATMOST k ==> P#[k](args)
    ///   AXIOM_ACTIVATION ==> forall args :: { P(args) } args-have-appropriate-values && (forall k :: 0 ATMOST k ==> P#[k](args)) ==> P(args)
    ///   AXIOM_ACTIVATION ==> forall args,k :: args-have-appropriate-values && k == 0 ==> P#0#[k](args)
    /// where
    /// AXIOM_ACTIVATION
    /// means:
    ///   mh LESS ModuleContextHeight ||
    ///   (mh == ModuleContextHeight && fh ATMOST FunctionContextHeight)

    /// </summary>
    void AddPrefixPredicateAxioms(PrefixPredicate pp) {
      Contract.Requires(pp != null);
      Contract.Requires(predef != null);
      var co = pp.Co;
      var tok = pp.tok;
      var etran = new ExpressionTranslator(this, predef, tok);

      List<Bpl.Expr> tyexprs; 
      var tyvars = MkTyParamBinders(pp.TypeArgs, out tyexprs);

      var bvs = new List<Variable>(tyvars);
      var coArgs = new List<Bpl.Expr>(tyexprs);
      var prefixArgs = new List<Bpl.Expr>(tyexprs);
      var prefixArgsLimited = new List<Bpl.Expr>(tyexprs);
      if (pp.IsRecursive) {
        var sV = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$ly", predef.LayerType));
        var s = new Bpl.IdentifierExpr(tok, sV);
        var succS = FunctionCall(tok, BuiltinFunction.LayerSucc, null, s);
        bvs.Add(sV);
        coArgs.Add(succS);
        prefixArgs.Add(succS);
        prefixArgsLimited.Add(s);
      }
      var bv = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, predef.HeapVarName, predef.HeapType));
      bvs.Add(bv);
      coArgs.Add(new Bpl.IdentifierExpr(tok, bv));
      prefixArgs.Add(new Bpl.IdentifierExpr(tok, bv));
      prefixArgsLimited.Add(new Bpl.IdentifierExpr(tok, bv));
      // ante:  $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      Bpl.Expr ante = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);

      if (!pp.IsStatic) {
        var bvThis = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, etran.This, predef.RefType));
        bvs.Add(bvThis);
        var bvThisIdExpr = new Bpl.IdentifierExpr(tok, bvThis);
        coArgs.Add(bvThisIdExpr);
        prefixArgs.Add(bvThisIdExpr);
        prefixArgsLimited.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(tok, pp);
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(bvThisIdExpr, predef.Null),
          etran.GoodRef(tok, bvThisIdExpr, thisType));
        ante = Bpl.Expr.And(ante, wh);
      }


      Bpl.Expr kWhere = null, kId = null;
      Bpl.Variable k = null;

      // DR: Changed to add the pp formals instead of co (since types would otherwise be wrong)
      //     Note that k is not added to bvs or coArgs.
      foreach (var p in pp.Formals) {
        bool is_k = p == pp.Formals[0];
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(pp), TrType(p.Type)));
        var formal = new Bpl.IdentifierExpr(p.tok, bv);
        if (!is_k) {
          coArgs.Add(formal);
        }
        prefixArgs.Add(formal);
        prefixArgsLimited.Add(formal);
        var wh = GetWhereClause(p.tok, formal, p.Type, etran);
        if (is_k) {
          // add the formal _k
          k = bv;
          kId = formal;
          kWhere = wh;
        } else {
          bvs.Add(bv);
          if (wh != null) { 
            // add well-typedness conjunct to antecedent
            ante = Bpl.Expr.And(ante, wh); 
          }
        }
      }

      var funcID = new Bpl.IdentifierExpr(tok, co.FullSanitizedName, TrType(co.ResultType));
      var coAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), coArgs);
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgs);

      var activation = AxiomActivation(pp, true, true, etran);

      // forall args :: { P(args) } args-have-appropriate-values && P(args) ==> forall k { P#[k](args) } :: 0 ATMOST k ==> P#[k](args)
      var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { prefixAppl });
      var allK = new Bpl.ForallExpr(tok, new List<Variable> { k }, tr, BplImp(kWhere, prefixAppl));
      tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { coAppl });
      var allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, coAppl), allK));
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, allS), 
        "1st prefix predicate axiom for " + pp.FullSanitizedName));

      // forall args :: { P(args) } args-have-appropriate-values && (forall k :: 0 ATMOST k ==> P#[k](args)) ==> P(args)
      allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, allK), coAppl));
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, allS),
        "2nd prefix predicate axiom"));

      // forall args,k :: args-have-appropriate-values && k == 0 ==> P#0#[k](args)
      var moreBvs = new List<Variable>();
      moreBvs.AddRange(bvs);
      moreBvs.Add(k);
      var z = Bpl.Expr.Eq(kId, Bpl.Expr.Literal(0));
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixLimited = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
      var trueAtZero = new Bpl.ForallExpr(tok, moreBvs, BplImp(BplAnd(ante, z), prefixLimited));
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, trueAtZero),
        "3rd prefix predicate axiom"));
    }

    /// <summary>
    /// Generate:
    ///     axiom (forall o: ref, h: Heap, G : Ty ::
    ///         { h[o, f], TClassA(G) }
    ///         $IsHeap(h) && o != null &&
    ///         $Is(o, TClassA(G))  // or dtype(o) = TClassA(G)
    ///       ==>
    ///         ($IsAlloc(o, TClassA(G), h) // or h[o, alloc]
    ///           ==> $IsAlloc(h[o, f], TT(PP), h))
    ///       && $Is(h[o, f], TT(PP), h);
    /// <summary>
    /// This can be optimised later to: 
    ///     axiom (forall o: ref, h: Heap ::
    ///         { h[o, f] }
    ///         $IsHeap(h) && o != null && Tag(dtype(o)) = TagClass
    ///       ==>
    ///         (h[o, alloc] ==> $IsAlloc(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h))
    ///       && $Is(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h);
    void AddAllocationAxiom(Field f, ClassDecl c, bool is_array = false)
    {
      // IFF you're adding the array axioms, then the field should be null
      Contract.Requires((is_array == true) == (f == null));
      Contract.Requires(sink != null && predef != null);

      Bpl.Expr h, o;
      var hVar = BplBoundVar("$h", predef.HeapType, out h);
      var oVar = BplBoundVar("$o", predef.RefType, out o);

      // only used for arrays
      List<Bpl.Variable> ixvars = new List<Bpl.Variable>();
      List<Bpl.Expr> ixs = new List<Bpl.Expr>();
      ArrayClassDecl ac = null;

      // h[o,f]
      Bpl.Expr oDotF;
      if (is_array) {
        ac = (ArrayClassDecl)c;
        for (int i = 0; i < ac.Dims; i++) {
          Bpl.Expr e; Bpl.Variable v = BplBoundVar("$i" + i, Bpl.Type.Int, out e);
          ixs.Add(e); ixvars.Add(v);
        }
        oDotF = ReadHeap(c.tok, h, o, GetArrayIndexFieldName(c.tok, ixs));
      } else if (f.IsMutable) {
        oDotF = ReadHeap(c.tok, h, o, new Bpl.IdentifierExpr(c.tok, GetField(f)));
      } else {
        oDotF = new Bpl.NAryExpr(c.tok, new Bpl.FunctionCall(GetReadonlyField(f)), new List<Bpl.Expr> { o });
      }

      List<Bpl.Expr> tyexprs;
      var tyvars = MkTyParamBinders(GetTypeParams(c), out tyexprs);

      Bpl.Expr o_ty = ClassTyCon(c, tyexprs); 

      // Bpl.Expr is_o      = MkIs(o, o_ty);         // $Is(o, ..)
      // Changed to use dtype(o) == o_ty instead:
      Bpl.Expr is_o      = DType(o, o_ty);
      // Bpl.Expr isalloc_o = MkIsAlloc(o, o_ty, h); // $IsAlloc(o, ..)
      // Changed to use h[o,alloc] instead:
      Bpl.Expr isalloc_o = IsAlloced(c.tok, h, o);

      Bpl.Expr is_hf, isalloc_hf;

      if (is_array) {
        is_hf = MkIs(oDotF, tyexprs[0], true);              
        isalloc_hf = MkIsAlloc(oDotF, tyexprs[0], h, true);
      } else {
        is_hf = MkIs(oDotF, f.Type);              // $Is(h[o, f], ..)
        isalloc_hf = MkIsAlloc(oDotF, f.Type, h); // $IsAlloc(h[o, f], ..)
      }

      Bpl.Expr ante = BplAnd(new List<Bpl.Expr>
          { FunctionCall(c.tok, BuiltinFunction.IsGoodHeap, null, h)
          , Bpl.Expr.Neq(o, predef.Null)
          , is_o
          });

      if (is_array) {
        for (int i = 0; i < ac.Dims; i++) {
          // 0 <= i && i < _System.array.Length(o)
          var e1 = Bpl.Expr.Le(Bpl.Expr.Literal(0), ixs[i]);
          var ff = GetReadonlyField((Field)(ac.Members[i]));
          var e2 = Bpl.Expr.Lt(ixs[i], new Bpl.NAryExpr(c.tok, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o }));
          ante = BplAnd(ante, BplAnd(e1, e2));
        }
      }

      Bpl.Expr cseq = BplAnd(is_hf, BplImp(isalloc_o, isalloc_hf));

      Bpl.Expr body = BplImp(ante, cseq);

      List<Bpl.Expr> t_es = new List<Bpl.Expr>();
      Bpl.Trigger tr = null;
      // trigger must mention both o and h (and index variables)
      if (is_array || f.IsMutable) {
        t_es.Add(oDotF);
        // trigger must mention type variables, if there are any
        if (tyvars.Count > 0) {
          t_es.Add(o_ty);
        }
        tr = new Bpl.Trigger(c.tok, true, t_es);
      }
      Bpl.Expr ax = BplForall(Concat(Concat(tyvars, ixvars), new List<Variable> { hVar, oVar }), tr, body);
      sink.TopLevelDeclarations.Add(new Bpl.Axiom(c.tok, ax, 
        c + "." + f + ": Allocation axiom"));
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

    ModuleDefinition currentModule = null;  // the name of the module whose members are currently being translated
    ICallable codeContext = null;  // the method/iterator whose implementation is currently being translated or the function whose specification is being checked for well-formedness
    Bpl.LocalVariable yieldCountVariable = null;  // non-null when an iterator body is being translated
    bool assertAsAssume = false; // generate assume statements instead of assert statements
    int loopHeapVarCount = 0;
    int otherTmpVarCount = 0;
    Dictionary<string, Bpl.IdentifierExpr> _tmpIEs = new Dictionary<string, Bpl.IdentifierExpr>();
    Bpl.IdentifierExpr GetTmpVar_IdExpr(IToken tok, string name, Bpl.Type ty, List<Variable> locals)  // local variable that's shared between statements that need it
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

    Bpl.IdentifierExpr GetPrevHeapVar_IdExpr(IToken tok, List<Variable> locals)  // local variable that's shared between statements that need it
    {
      Contract.Requires(tok != null);
      Contract.Requires(locals != null); Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      return GetTmpVar_IdExpr(tok, "$prevHeap", predef.HeapType, locals);
    }

    Bpl.IdentifierExpr GetNewVar_IdExpr(IToken tok, List<Variable> locals)  // local variable that's shared between statements that need it
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
    Bpl.Expr SaveInTemp(Bpl.Expr expr, bool otherExprsCanAffectPreviouslyKnownExpressions, string name, Bpl.Type ty, Bpl.StmtListBuilder builder, List<Variable> locals) {
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
      Contract.Requires(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);
      Contract.Ensures(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);

      currentModule = m.EnclosingClass.Module;
      codeContext = m;

      List<TypeVariable> typeParams = TrTypeParamDecls(GetTypeParams(m));
      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      builder.Add(new CommentCmd("AddMethodImpl: " + m + ", " + proc));
      ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);
      List<Variable> localVariables = new List<Variable>();
      GenerateImplPrelude(m, wellformednessProc, inParams, outParams, builder, localVariables);

      Bpl.StmtList stmts;      
      if (!wellformednessProc) {
        if (3 <= DafnyOptions.O.Induction && m.IsGhost && m.Mod.Expressions.Count == 0 && m.Outs.Count == 0 && !(m is CoLemma)) {
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
            //     forall (this', y' | Pre(this', x, y') && VF(this', x, y') << VF(this, x, y)) {
            //       this'.M(x, y');
            //     }
            // Generate bound variables for the forall statement, and a substitution for the Pre and VF

            // assume case-analysis-on-parameter[[ y' ]];
            foreach (var inFormal in m.Ins) {
              var dt = inFormal.Type.AsDatatype;
              if (dt != null) {
                var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(inFormal.tok, "$IsA#" + dt.FullSanitizedName, Bpl.Type.Bool));
                var f = new Bpl.IdentifierExpr(inFormal.tok, inFormal.AssignUniqueName(m), TrType(inFormal.Type));
                builder.Add(new Bpl.AssumeCmd(inFormal.tok, new Bpl.NAryExpr(inFormal.tok, funcID, new List<Bpl.Expr> { f })));
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
            var recursiveCall = new CallStmt(m.tok, m.tok, new List<Expression>(), recursiveCallReceiver, m.Name, recursiveCallArgs);
            recursiveCall.Method = m;  // resolve here
            recursiveCall.IsGhost = m.IsGhost;  // resolve here

            Expression parRange = new LiteralExpr(m.tok, true);
            parRange.Type = Type.Bool;  // resolve here
            if (receiverReplacement != null) {
              // add "this' != null" to the range
              var nil = new LiteralExpr(receiverReplacement.tok);
              nil.Type = receiverReplacement.Type;  // resolve here
              var neqNull = new BinaryExpr(receiverReplacement.tok, BinaryExpr.Opcode.Neq, receiverReplacement, nil);
              neqNull.ResolvedOp = BinaryExpr.ResolvedOpcode.NeqCommon;  // resolve here
              neqNull.Type = Type.Bool;  // resolve here
              parRange = Expression.CreateAnd(parRange, neqNull);
            }
            foreach (var pre in m.Req) {
              if (!pre.IsFree) {
                parRange = Expression.CreateAnd(parRange, Substitute(pre.E, receiverReplacement, substMap));
              }
            }
            // construct an expression (generator) for:  VF' << VF
            ExpressionConverter decrCheck = delegate(Dictionary<IVariable, Expression> decrSubstMap, ExpressionTranslator exprTran) {
              var decrToks = new List<IToken>();
              var decrTypes = new List<Type>();
              var decrCallee = new List<Expr>();
              var decrCaller = new List<Expr>();
              foreach (var ee in m.Decreases.Expressions) {
                decrToks.Add(ee.tok);
                decrTypes.Add(ee.Type.NormalizeExpand());
                decrCaller.Add(exprTran.TrExpr(ee));
                Expression es = Substitute(ee, receiverReplacement, substMap);
                es = Substitute(es, null, decrSubstMap);
                decrCallee.Add(exprTran.TrExpr(es));
              }
              return DecreasesCheck(decrToks, decrTypes, decrTypes, decrCallee, decrCaller, null, null, false, true);
            };

#if VERIFY_CORRECTNESS_OF_TRANSLATION_FORALL_STATEMENT_RANGE
            var definedness = new Bpl.StmtListBuilder();
            var exporter = new Bpl.StmtListBuilder();
            TrForallStmtCall(m.tok, parBoundVars, parRange, decrCheck, recursiveCall, definedness, exporter, localVariables, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(m.tok, null, definedness.Collect(m.tok), null, exporter.Collect(m.tok)));
#else
            TrForallStmtCall(m.tok, parBoundVars, parRange, decrCheck, recursiveCall, null, builder, localVariables, etran);
#endif
          }
        }
        // translate the body of the method
        Contract.Assert(m.Body != null);  // follows from method precondition and the if guard
        // $_reverifyPost := false;
        builder.Add(Bpl.Cmd.SimpleAssign(m.tok, new Bpl.IdentifierExpr(m.tok, "$_reverifyPost", Bpl.Type.Bool), Bpl.Expr.False));
        stmts = TrStmt2StmtList(builder, m.Body, localVariables, etran);
      } else {
        // check well-formedness of the preconditions, and then assume each one of them
        foreach (MaybeFreeExpression p in m.Req) {
          CheckWellformed(p.E, new WFOptions(), localVariables, builder, etran);
          builder.Add(new Bpl.AssumeCmd(p.E.tok, etran.TrExpr(p.E)));
        }
        // check well-formedness of the modifies clause
        CheckFrameWellFormed(new WFOptions(), m.Mod.Expressions, localVariables, builder, etran);
        // check well-formedness of the decreases clauses
        foreach (Expression p in m.Decreases.Expressions)
        {
          CheckWellformed(p, new WFOptions(), localVariables, builder, etran);
        }

        // play havoc with the heap according to the modifies clause
        builder.Add(new Bpl.HavocCmd(m.tok, new List<Bpl.IdentifierExpr>{ (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
        // assume the usual two-state boilerplate information
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, etran.Old, etran, etran.Old))
        {
          if (tri.IsFree) {
            builder.Add(new Bpl.AssumeCmd(m.tok, tri.Expr));
          }
        }

        // also play havoc with the out parameters
        if (outParams.Count != 0)
        {  // don't create an empty havoc statement
          List<Bpl.IdentifierExpr> outH = new List<Bpl.IdentifierExpr>();
          foreach (Bpl.Variable b in outParams) {
            Contract.Assert(b != null);
            outH.Add(new Bpl.IdentifierExpr(b.tok, b));
          }
          builder.Add(new Bpl.HavocCmd(m.tok, outH));
        }
        // mark the end of the modifles/out-parameter havocking with a CaptureState; make its location be the first ensures clause, if any (and just
        // omit the CaptureState if there's no ensures clause)
        if (m.Ens.Count != 0) {
          builder.Add(CaptureState(m.Ens[0].E.tok, false, "post-state"));
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

      if (InsertChecksums)
      {
        InsertChecksum(m, impl);
      }

      currentModule = null;
      codeContext = null;
      loopHeapVarCount = 0;
      otherTmpVarCount = 0;
      _tmpIEs.Clear();
    }

    private void AddFunctionOverrideCheckImpl(Function f)
    {
        Contract.Requires(f != null);
        //Contract.Requires(proc != null);
        Contract.Requires(sink != null && predef != null);
        Contract.Requires(f.OverriddenFunction != null);
        Contract.Requires(f.Formals.Count == f.OverriddenFunction.Formals.Count);
        Contract.Requires(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);
        Contract.Ensures(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);

        #region first procedure, no impl yet
        //Function nf = new Function(f.tok, "OverrideCheck_" + f.Name, f.IsStatic, f.IsGhost, f.TypeArgs, f.OpenParen, f.Formals, f.ResultType, f.Req, f.Reads, f.Ens, f.Decreases, f.Body, f.Attributes, f.SignatureEllipsis);
        //AddFunction(f);
        currentModule = f.EnclosingClass.Module;
        codeContext = f;

        ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);
        // parameters of the procedure
        List<Variable> inParams = new List<Variable>();
        if (!f.IsStatic)
        {
            Bpl.Expr wh = Bpl.Expr.And(
              Bpl.Expr.Neq(new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), predef.Null),
              etran.GoodRef(f.tok, new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), Resolver.GetReceiverType(f.tok, f)));
            Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType, wh), true);
            inParams.Add(thVar);
        }
        foreach (Formal p in f.Formals)
        {
            Bpl.Type varType = TrType(p.Type);
            Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f), varType), p.Type, etran);
            inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), varType, wh), true));
        }
        List<TypeVariable> typeParams = TrTypeParamDecls(f.TypeArgs);
        // the procedure itself
        var req = new List<Bpl.Requires>();
        // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
        req.Add(Requires(f.tok, true, etran.HeightContext(f), null, null));
        // modifies $Heap, $Tick
        var mod = new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr, etran.Tick() };
        // check that postconditions hold
        var ens = new List<Bpl.Ensures>();
        foreach (Expression p in f.Ens)
        {
            var functionHeight = currentModule.CallGraph.GetSCCRepresentativeId(f);
            var splits = new List<SplitExprInfo>();
            bool splitHappened/*we actually don't care*/ = TrSplitExpr(p, splits, true, functionHeight,false, etran);
            foreach (var s in splits)
            {
                if (s.IsChecked && !RefinementToken.IsInherited(s.E.tok, currentModule))
                {
                    ens.Add(Ensures(s.E.tok, false, s.E, null, null));
                }
            }
        }
        Bpl.Procedure proc = new Bpl.Procedure(f.tok, "OverrideCheck$$" + f.FullSanitizedName, typeParams, inParams, new List<Variable>(),
          req, mod, ens, etran.TrAttributes(f.Attributes, null));
        sink.TopLevelDeclarations.Add(proc);
        var implInParams = Bpl.Formal.StripWhereClauses(inParams);

        #endregion

        //List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

        Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
        List<Variable> localVariables = new List<Variable>();
        //GenerateImplPrelude(m, wellformednessProc, inParams, outParams, builder, localVariables);

        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < f.Formals.Count; i++)
        {
            //get corresponsing formal in the class
            var ie = new IdentifierExpr(f.Formals[i].tok, f.Formals[i].AssignUniqueName(f));
            ie.Var = f.Formals[i]; ie.Type = ie.Var.Type;
            substMap.Add(f.OverriddenFunction.Formals[i], ie);
        }

        Bpl.StmtList stmts;
        //adding assume Pre’; assert P; // this checks that Pre’ implies P
        AddFunctionOverrideReqsChk(f, builder, etran, substMap);

        //adding assert R <= Rank’;
        AddFunctionOverrideTerminationChk(f, builder, etran, substMap);

        //adding assert W <= Frame’
        AddFunctionOverrideSubsetChk(f, builder, etran, localVariables, substMap);

        //change the heap at locations W
        HavocFunctionFrameLocations(f, builder, etran, localVariables);

        //adding assume Q; assert Post’;
        AddFunctionOverrideEnsChk(f, builder, etran, substMap, implInParams);

        //creating an axiom that conncets J.F and C.F
        //which is a class function and overridden trait function
        AddFunctionOverrideAxiom(f);

        stmts = builder.Collect(f.tok);

        QKeyValue kv = etran.TrAttributes(f.Attributes, null);

        Bpl.Implementation impl = new Bpl.Implementation(f.tok, proc.Name, typeParams, implInParams, new List<Variable>(), localVariables, stmts, kv);
        sink.TopLevelDeclarations.Add(impl);

        if (InsertChecksums)
        {
            InsertChecksum(f, proc, true);
        }

        currentModule = null;
        codeContext = null;
        loopHeapVarCount = 0;
        otherTmpVarCount = 0;
        _tmpIEs.Clear();
    }

    private void AddFunctionOverrideAxiom(Function f)
    {
        Contract.Requires(f != null);
        Contract.Requires(sink != null && predef != null);
        // function override axiom
        // axiom (forall $heap: HeapType, this: ref, x#0: int ::
        //     { J.F($heap, this, x#0) }
        //     this != null && dtype(this) == class.C
        //     ==>
        //     J.F($heap, this, x#0) == C.F($heap, this, x#0));

        var formals = new List<Variable>();
        var argsC = new List<Bpl.Expr>();
        var argsT = new List<Bpl.Expr>();

        var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
        var s = new Bpl.IdentifierExpr(f.tok, bv);
        if (f.IsRecursive)
        {
            formals.Add(bv);
            argsC.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, s));
            argsT.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, s));
        }

        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        argsC.Add(s);
        argsT.Add(s);

        if (!f.IsStatic)
        {
            bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType));
            formals.Add(bv);
            s = new Bpl.IdentifierExpr(f.tok, bv);
            argsC.Add(s);
            argsT.Add(s);
        }
        foreach (var p in f.Formals)
        {
            bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, f.FullSanitizedName + "_" + p.AssignUniqueName(f), TrType(p.Type)));
            formals.Add(bv);
            s = new Bpl.IdentifierExpr(f.tok, bv);
            argsC.Add(s);
        }
        foreach (var p in f.OverriddenFunction.Formals)
        {
            bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, f.OverriddenFunction.FullSanitizedName + "_" + p.AssignUniqueName(f.OverriddenFunction), TrType(p.Type)));
            formals.Add(bv);
            s = new Bpl.IdentifierExpr(f.OverriddenFunction.tok, bv);
            argsT.Add(s);
        }

        var funcIdC = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        var funcIdT = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.OverriddenFunction.tok, f.OverriddenFunction.FullSanitizedName, TrType(f.OverriddenFunction.ResultType)));
        var funcApplC = new Bpl.NAryExpr(f.tok, funcIdC, argsC);
        var funcApplT = new Bpl.NAryExpr(f.OverriddenFunction.tok, funcIdT, argsT);

        var typeParams = TrTypeParamDecls(f.TypeArgs);

        Bpl.Trigger tr = new Bpl.Trigger(f.OverriddenFunction.tok, true, new List<Bpl.Expr> { funcApplT, funcApplC });
        Bpl.Expr ax = new Bpl.ForallExpr(f.tok, typeParams, formals, null, tr, Bpl.Expr.Eq(funcApplC, funcApplT));
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax, "function override axiom"));
    }

    private void AddFunctionOverrideEnsChk(Function f, StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap, List<Variable> implInParams)
    {
        //generating class post-conditions
        foreach (var en in f.Ens)
        {
            builder.Add(new Bpl.AssumeCmd(f.tok, etran.TrExpr(en)));
        }

        //generating assume J.F(ins) == C.F(ins)
        Bpl.FunctionCall funcIdC = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        Bpl.FunctionCall funcIdT = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.OverriddenFunction.tok, f.OverriddenFunction.FullSanitizedName, TrType(f.OverriddenFunction.ResultType)));
        List<Bpl.Expr> argsC = new List<Bpl.Expr>();
        List<Bpl.Expr> argsT = new List<Bpl.Expr>();
        if (f.IsRecursive)
        {
            argsC.Add(etran.LayerN(1));
        }
        if (f.OverriddenFunction.IsRecursive)
        {
            argsT.Add(etran.LayerN(1));
        }
        argsC.Add(etran.HeapExpr);
        argsT.Add(etran.HeapExpr);
        foreach (Variable p in implInParams)
        {
            argsC.Add(new Bpl.IdentifierExpr(f.tok, p));
            argsT.Add(new Bpl.IdentifierExpr(f.OverriddenFunction.tok, p));
        }
        Bpl.Expr funcExpC = new Bpl.NAryExpr(f.tok, funcIdC, argsC);
        Bpl.Expr funcExpT = new Bpl.NAryExpr(f.OverriddenFunction.tok, funcIdT, argsT);
        builder.Add(new Bpl.AssumeCmd(f.tok, Bpl.Expr.Eq(funcExpC, funcExpT)));

        //generating trait post-conditions with class variables
        foreach (var en in f.OverriddenFunction.Ens)
        {
            Expression postcond = Substitute(en, null, substMap);
            bool splitHappened;
            var reqSplitedE = TrSplitExpr(postcond, etran,false, out splitHappened);
            foreach (var s in reqSplitedE)
            {
                var assert = new Bpl.AssertCmd(f.tok, s.E);
                assert.ErrorData = "Error: the function must provide an equal or more detailed postcondition than in its parent trait";
                builder.Add(assert);
            }
        }
    }

    private void HavocFunctionFrameLocations(Function f, StmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables)
    {
        // play havoc with the heap according to the modifies clause
        builder.Add(new Bpl.HavocCmd(f.tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
        // assume the usual two-state boilerplate information
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(f.tok, f.Reads, f.IsGhost, etran.Old, etran, etran.Old))
        {
            if (tri.IsFree)
            {
                builder.Add(new Bpl.AssumeCmd(f.tok, tri.Expr));
            }
        }
    }

    private void AddFunctionOverrideSubsetChk(Function func, StmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables, Dictionary<IVariable, Expression> substMap)
    {
        //getting framePrime
        List<FrameExpression> traitFrameExps = new List<FrameExpression>();
        foreach (var e in func.OverriddenFunction.Reads)
        {
            var newE = Substitute(e.E, null, substMap);
            FrameExpression fe = new FrameExpression(e.tok, newE, e.FieldName);
            traitFrameExps.Add(fe);
        }

        QKeyValue kv = etran.TrAttributes(func.Attributes, null);

        IToken tok = func.tok;
        // Declare a local variable $_Frame: <alpha>[ref, Field alpha]bool
        Bpl.IdentifierExpr traitFrame = etran.TheFrame(func.OverriddenFunction.tok);  // this is a throw-away expression, used only to extract the type and name of the $_Frame variable
        traitFrame.Name = func.EnclosingClass.Name + "_" + traitFrame.Name;
        Contract.Assert(traitFrame.Type != null);  // follows from the postcondition of TheFrame
        Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, null ?? traitFrame.Name, traitFrame.Type));
        localVariables.Add(frame);
        // $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
        Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
        Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
        Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
        Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
        Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
        Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
        Bpl.Expr consequent = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
        Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null,
                                             Bpl.Expr.Imp(ante, consequent));

        //to initialize $_Frame variable to Frame'
        builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));

        // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_Frame[o,f]);
        Bpl.Expr oInCallee = InRWClause(tok, o, f, func.Reads, etran, null, null);
        Bpl.Expr consequent2 = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
        Bpl.Expr q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
                                        Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), consequent2));
        builder.Add(Assert(tok, q, "expression may read an object not in the parent trait context's reads clause", kv));
    }

    private void AddFunctionOverrideTerminationChk(Function f, StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
        var decrToks = new List<IToken>();
        var decrTypes1 = new List<Type>();
        var decrTypes2 = new List<Type>();
        var decrClass = new List<Expr>();
        var decrTrait = new List<Expr>();
        if (f.Decreases != null)
        {
            foreach (var decC in f.Decreases.Expressions)
            {
                decrToks.Add(decC.tok);
                decrTypes1.Add(decC.Type);
                decrClass.Add(etran.TrExpr(decC));
            }
        }
        if (f.OverriddenFunction.Decreases != null)
        {
            foreach (var decT in f.OverriddenFunction.Decreases.Expressions)
            {
                var decCNew = Substitute(decT, null, substMap);
                decrTypes2.Add(decCNew.Type);
                decrTrait.Add(etran.TrExpr(decCNew));
            }
        }
        var decrChk = DecreasesCheck(decrToks, decrTypes1, decrTypes2, decrClass, decrTrait, null, null, true, false);
        builder.Add(new Bpl.AssertCmd(f.tok, decrChk));
    }

    private void AddFunctionOverrideReqsChk(Function f, StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
        //generating trait pre-conditions with class variables
        foreach (var req in f.OverriddenFunction.Req)
        {
            Expression precond = Substitute(req, null, substMap);
            builder.Add(new Bpl.AssumeCmd(f.tok, etran.TrExpr(precond)));
        }
        //generating class pre-conditions
        foreach (var req in f.Req)
        {
            bool splitHappened;
            var reqSplitedE = TrSplitExpr(req, etran,false, out splitHappened);
            foreach (var s in reqSplitedE)
            {
                var assert = new Bpl.AssertCmd(f.tok, s.E);
                assert.ErrorData = "Error: the function must provide an equal or more permissive precondition than in its parent trait";
                builder.Add(assert);
            }
        }
    }

    private void AddMethodOverrideCheckImpl(Method m, Bpl.Procedure proc)
    {
        Contract.Requires(m != null);
        Contract.Requires(proc != null);
        Contract.Requires(sink != null && predef != null);
        Contract.Requires(m.OverriddenMethod != null);
        Contract.Requires(m.Ins.Count == m.OverriddenMethod.Ins.Count);
        Contract.Requires(m.Outs.Count == m.OverriddenMethod.Outs.Count);
        //Contract.Requires(wellformednessProc || m.Body != null);
        Contract.Requires(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);
        Contract.Ensures(currentModule == null && codeContext == null && loopHeapVarCount == 0 && _tmpIEs.Count == 0);

        currentModule = m.EnclosingClass.Module;
        codeContext = m;

        List<TypeVariable> typeParams = TrTypeParamDecls(m.TypeArgs);
        List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
        List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

        Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
        ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);
        List<Variable> localVariables = new List<Variable>();
        //GenerateImplPrelude(m, wellformednessProc, inParams, outParams, builder, localVariables);

        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < m.Ins.Count; i++)
        {
            //get corresponsing formal in the class
            var ie = new IdentifierExpr(m.Ins[i].tok, m.Ins[i].AssignUniqueName(m));
            ie.Var = m.Ins[i]; ie.Type = ie.Var.Type;
            substMap.Add(m.OverriddenMethod.Ins[i], ie);
        }
        for (int i = 0; i < m.Outs.Count; i++)
        {
            //get corresponsing formal in the class
            var ie = new IdentifierExpr(m.Outs[i].tok, m.Outs[i].AssignUniqueName(m));
            ie.Var = m.Outs[i]; ie.Type = ie.Var.Type;
            substMap.Add(m.OverriddenMethod.Outs[i], ie);
        }

        Bpl.StmtList stmts;
        //adding assume Pre’; assert P; // this checks that Pre’ implies P
        AddMethodOverrideReqsChk(m, builder, etran, substMap);

        //adding assert R <= Rank’;
        AddMethodOverrideTerminationChk(m, builder, etran, substMap);

        //adding assert W <= Frame’
        AddMethodOverrideSubsetChk(m, builder, etran, localVariables, substMap);

        //change the heap at locations W
        HavocMethodFrameLocations(m, builder, etran, localVariables);

        //adding assume Q; assert Post’;
        AddMethodOverrideEnsChk(m, builder, etran, substMap);

        stmts = builder.Collect(m.tok);

        QKeyValue kv = etran.TrAttributes(m.Attributes, null);

        Bpl.Implementation impl = new Bpl.Implementation(m.tok, proc.Name, typeParams, inParams, outParams, localVariables, stmts, kv);
        sink.TopLevelDeclarations.Add(impl);

        if (InsertChecksums)
        {
            InsertChecksum(m, impl);
        }

        currentModule = null;
        codeContext = null;
        loopHeapVarCount = 0;
        otherTmpVarCount = 0;
        _tmpIEs.Clear();
    }

    private void HavocMethodFrameLocations(Method m, Bpl.StmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables)
    {
        Contract.Requires(m != null);
        Contract.Requires(m.EnclosingClass != null && m.EnclosingClass is ClassDecl);

        // play havoc with the heap according to the modifies clause
        builder.Add(new Bpl.HavocCmd(m.tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
        // assume the usual two-state boilerplate information
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, etran.Old, etran, etran.Old))
        {
            if (tri.IsFree)
            {
                builder.Add(new Bpl.AssumeCmd(m.tok, tri.Expr));
            }
        }
    }

    private void AddMethodOverrideEnsChk(Method m, Bpl.StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
        //generating class post-conditions
        foreach (var en in m.Ens)
        {
            builder.Add(new Bpl.AssumeCmd(m.tok, etran.TrExpr(en.E)));
        }
        //generating trait post-conditions with class variables
        foreach (var en in m.OverriddenMethod.Ens)
        {
            Expression postcond = Substitute(en.E, null, substMap);
            bool splitHappened;
            var reqSplitedE = TrSplitExpr(postcond, etran,false, out splitHappened);
            foreach (var s in reqSplitedE)
            {
                var assert = new Bpl.AssertCmd(m.tok, s.E);
                assert.ErrorData = "Error: the method must provide an equal or more detailed postcondition than in its parent trait";
                builder.Add(assert);
            }
        }
    }

    private void AddMethodOverrideReqsChk(Method m, Bpl.StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
        //generating trait pre-conditions with class variables
        foreach (var req in m.OverriddenMethod.Req)
        {
            Expression precond = Substitute(req.E, null, substMap);
            builder.Add(new Bpl.AssumeCmd(m.tok, etran.TrExpr(precond)));
        }
        //generating class pre-conditions
        foreach (var req in m.Req)
        {
            bool splitHappened;
            var reqSplitedE = TrSplitExpr(req.E, etran,false, out splitHappened);
            foreach (var s in reqSplitedE)
            {
                var assert = new Bpl.AssertCmd(m.tok, s.E);
                assert.ErrorData = "Error: the method must provide an equal or more permissive precondition than in its parent trait";
                builder.Add(assert);
            }
        }
    }

    private void AddMethodOverrideTerminationChk(Method m, Bpl.StmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
        var decrToks = new List<IToken>();
        var decrTypes1 = new List<Type>();
        var decrTypes2 = new List<Type>();
        var decrClass = new List<Expr>();
        var decrTrait = new List<Expr>();
        if (m.Decreases != null)
        {
            foreach (var decC in m.Decreases.Expressions)
            {
                decrToks.Add(decC.tok);
                decrTypes1.Add(decC.Type);
                decrClass.Add(etran.TrExpr(decC));
            }
        }
        if (m.OverriddenMethod.Decreases != null)
        {
            foreach (var decT in m.OverriddenMethod.Decreases.Expressions)
            {
                var decCNew = Substitute(decT, null, substMap);
                decrTypes2.Add(decCNew.Type);
                decrTrait.Add(etran.TrExpr(decCNew));
            }
        }
        var decrChk = DecreasesCheck(decrToks, decrTypes1, decrTypes2, decrClass, decrTrait, null, null, true, false);
        builder.Add(new Bpl.AssertCmd(m.tok, decrChk));
    }

    private void AddMethodOverrideSubsetChk(Method m, Bpl.StmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables, Dictionary<IVariable, Expression> substMap)
    {
        //getting framePrime
        List<FrameExpression> traitFrameExps = new List<FrameExpression>();
        List<FrameExpression> classFrameExps = m.Mod != null ? m.Mod.Expressions : new List<FrameExpression>();
        if (m.OverriddenMethod.Mod != null)
        {
            foreach (var e in m.OverriddenMethod.Mod.Expressions)
            {
                var newE = Substitute(e.E, null, substMap);
                FrameExpression fe = new FrameExpression(e.tok, newE, e.FieldName);
                traitFrameExps.Add(fe);
            }
        }

        QKeyValue kv = etran.TrAttributes(m.Attributes, null);

        IToken tok = m.tok;
        // Declare a local variable $_Frame: <alpha>[ref, Field alpha]bool
        Bpl.IdentifierExpr traitFrame = etran.TheFrame(m.OverriddenMethod.tok);  // this is a throw-away expression, used only to extract the type and name of the $_Frame variable
        traitFrame.Name = m.EnclosingClass.Name + "_" + traitFrame.Name;
        Contract.Assert(traitFrame.Type != null);  // follows from the postcondition of TheFrame
        Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, null ?? traitFrame.Name, traitFrame.Type));
        localVariables.Add(frame);
        // $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
        Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
        Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
        Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
        Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
        Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
        Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
        Bpl.Expr consequent = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
        Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null,
                                             Bpl.Expr.Imp(ante, consequent));

        //to initialize $_Frame variable to Frame'
        builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));

        // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_Frame[o,f]);
        Bpl.Expr oInCallee = InRWClause(tok, o, f, classFrameExps, etran, null, null);
        Bpl.Expr consequent2 = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
        Bpl.Expr q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
                                        Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), consequent2));
        builder.Add(Assert(tok, q, "expression may modify an object not in the parent trait context's modifies clause", kv));
    }

    private void InsertChecksum(Method m, Bpl.Declaration decl, bool specificationOnly = false)
    {
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintAttributes(m.Attributes);
        printer.PrintFormals(m.Ins);
        if (m.Outs.Any())
        {
          writer.Write("returns ");
          printer.PrintFormals(m.Outs);
        }
        printer.PrintSpec("", m.Req, 0);
        printer.PrintFrameSpecLine("", m.Mod.Expressions, 0, null);
        printer.PrintSpec("", m.Ens, 0);
        printer.PrintDecreasesSpec(m.Decreases, 0);
        if (!specificationOnly && m.Body != null)
        {
          printer.PrintStatement(m.Body, 0);
        }
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(DatatypeDecl d, Bpl.Declaration decl)
    {
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintDatatype(d, 0);
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Expression e, Bpl.Declaration decl)
    {
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintExpression(e, false);
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Function f, Bpl.Declaration decl, bool specificationOnly = false)
    {
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintAttributes(f.Attributes);
        if (f.OpenParen != null) {
          printer.PrintFormals(f.Formals);
        }
        writer.Write(": ");
        printer.PrintType(f.ResultType);
        printer.PrintSpec("", f.Req, 0);
        printer.PrintFrameSpecLine("", f.Reads, 0, null);
        printer.PrintSpec("", f.Ens, 0);
        printer.PrintDecreasesSpec(f.Decreases, 0);
        if (!specificationOnly && f.Body != null)
        {
          printer.PrintExpression(f.Body, false);
        }
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Bpl.Declaration decl, byte[] data)
    {
      var md5 = System.Security.Cryptography.MD5.Create();
      var hashedData = md5.ComputeHash(data);
      var checksum = BitConverter.ToString(hashedData);

      decl.AddAttribute("checksum", checksum);

      InsertUniqueIdForImplementation(decl);
    }

    public void InsertUniqueIdForImplementation(Bpl.Declaration decl)
    {
      var impl = decl as Bpl.Implementation;
      var prefix = UniqueIdPrefix ?? System.Text.RegularExpressions.Regex.Replace(decl.tok.filename, @".v\d+.dfy", ".dfy");
      if (impl != null && !string.IsNullOrEmpty(prefix))
      {
        decl.AddAttribute("id", prefix + ":" + impl.Name + ":0");
      }
    }

    void CheckFrameWellFormed(WFOptions wfo, List<FrameExpression> fes, List<Variable> locals, StmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(fes != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      foreach (var fe in fes) {
        CheckWellformed(fe.E, wfo, locals, builder, etran);
        if (fe.Field != null && fe.E.Type.IsRefType) {
          builder.Add(Assert(fe.tok, Bpl.Expr.Neq(etran.TrExpr(fe.E), predef.Null), "frame expression may dereference null"));
        }
      }
    }

    void GenerateImplPrelude(Method m, bool wellformednessProc, List<Variable> inParams, List<Variable> outParams,
                             Bpl.StmtListBuilder builder, List<Variable> localVariables) {
      Contract.Requires(m != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);

      // set up the information used to verify the method's modifies clause
      DefineFrame(m.tok, m.Mod.Expressions, builder, localVariables, null);
      if (wellformednessProc) {
        builder.Add(CaptureState(m.tok, false, "initial state"));
      } else {
        Contract.Assert(m.Body != null);  // follows from precondition and the if guard
        // use the position immediately after the open-curly-brace of the body
        builder.Add(CaptureState(m.Body.Tok, true, "initial state"));
      }
    }

    void GenerateIteratorImplPrelude(IteratorDecl iter, List<Variable> inParams, List<Variable> outParams,
                                     Bpl.StmtListBuilder builder, List<Variable> localVariables) {
      Contract.Requires(iter != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);

      // set up the information used to verify the method's modifies clause
      var iteratorFrame = new List<FrameExpression>();
      var th = new ThisExpr(iter.tok);
      th.Type = Resolver.GetThisType(iter.tok, iter);  // resolve here
      iteratorFrame.Add(new FrameExpression(iter.tok, th, null));
      iteratorFrame.AddRange(iter.Modifies.Expressions);
      DefineFrame(iter.tok, iteratorFrame, builder, localVariables, null);
      builder.Add(CaptureState(iter.tok, false, "initial state"));
    }

    Bpl.Cmd CaptureState(IToken tok, bool isEndToken, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      var col = tok.col + (isEndToken ? tok.val.Length : 0);
      string description = string.Format("{0}({1},{2}){3}{4}", tok.filename, tok.line, col, additionalInfo == null ? "" : ": ", additionalInfo ?? "");
      QKeyValue kv = new QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return new Bpl.AssumeCmd(tok, Bpl.Expr.True, kv);
    }
    Bpl.Cmd CaptureState(Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(stmt.EndTok, true, null);
    }

    void DefineFrame(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frameClause, Bpl.StmtListBuilder/*!*/ builder, List<Variable>/*!*/ localVariables, string name)
    {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(frameClause));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(localVariables));
      Contract.Requires(predef != null);

      var etran = new ExpressionTranslator(this, predef, tok);
      // Declare a local variable $_Frame: <alpha>[ref, Field alpha]bool
      Bpl.IdentifierExpr theFrame = etran.TheFrame(tok);  // this is a throw-away expression, used only to extract the type and name of the $_Frame variable
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
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null,
                                           Bpl.Expr.Imp(ante, consequent));

      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));
    }

    void CheckFrameSubset(IToken tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable, Expression /*!*/> substMap,
                          ExpressionTranslator /*!*/ etran,
                          Bpl.StmtListBuilder /*!*/ builder,
                          string errorMessage,
                          Bpl.QKeyValue kv) 
    {
      CheckFrameSubset(tok, calleeFrame, receiverReplacement, substMap, etran,
        (t, e, s, q) => builder.Add(Assert(t, e, s, q)), errorMessage, kv);
    }

    void CheckFrameSubset(IToken tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable,Expression/*!*/> substMap,
                          ExpressionTranslator/*!*/ etran, 
                          Action<IToken, Bpl.Expr, string, Bpl.QKeyValue> MakeAssert,
                          string errorMessage,
                          Bpl.QKeyValue kv)
    {
      Contract.Requires(tok != null);
      Contract.Requires(calleeFrame != null);
      Contract.Requires((receiverReplacement == null) == (substMap == null));
      Contract.Requires(etran != null);
      Contract.Requires(MakeAssert != null);
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
      Bpl.Expr q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
                                      Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), inEnclosingFrame));
      MakeAssert(tok, q, errorMessage, kv);
    }

    /// <summary>
    /// Generates:
    ///   axiom (forall s, h0: HeapType, h1: HeapType, formals... ::
    ///        { HeapSucc(h0,h1), F(s,h1,formals) }
    ///        heaps are well-formed and formals are allocated AND
    ///        HeapSucc(h0,h1)
    ///        AND
    ///        (forall(alpha) o: ref, f: Field alpha ::
    ///            o != null AND h0[o,alloc] AND h1[o,alloc] AND
    ///            o in reads clause of formals in h0
    ///            IMPLIES h0[o,f] == h1[o,f])
    ///        IMPLIES
    ///        F(s,h0,formals) == F(s,h1,formals)
    ///      );
    /// Or, in the simple case where the function has an empty "reads" clause, generates:
    ///   function F#frame(ly, formals): T;
    ///   axiom (forall s,h: HeapType, formals... ::
    ///        { F(s,h,formals) }
    ///        heap is well-formed and formals are allocated
    ///        IMPLIES
    ///        F(s,h,formals) == F#frame(s,formals)
    ///      );
    /// </summary>
    void AddFrameAxiom(Function f)
    {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);

      var comment = "frame axiom for " + f.FullSanitizedName;
#if POSSIBLY_FUTURE_OPTIMIZATION
      if (f.Reads.Count == 0) {
        // This is the simple case

        // declare a frame-axiom helper function
        var typeParams = TrTypeParamDecls(f.TypeArgs);
        {
          var formals = new List<Variable>();
          if (f.IsRecursive) {
            formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType), true));
          }
          if (!f.IsStatic) {
            formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType), true));
          }
          foreach (var p in f.Formals) {
            formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)), true));
          }
          var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
          var funcFrame = new Bpl.Function(f.tok, f.FullSanitizedName + "#frame", typeParams, formals, res, comment);
          sink.TopLevelDeclarations.Add(funcFrame);
        }

        var heapVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$h", predef.HeapType));
        Bpl.Expr heap = new Bpl.IdentifierExpr(f.tok, heapVar);
        var etran = new ExpressionTranslator(this, predef, heap);

        Bpl.Expr wellFormed = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);

        List<Variable> bvars = new List<Variable>();
        List<Bpl.Expr> argsF = new List<Bpl.Expr>();
        List<Bpl.Expr> argsFFrame = new List<Bpl.Expr>();
        List<Bpl.Expr> argsCanCall = new List<Bpl.Expr>();
        if (f.IsRecursive) {
          var sV = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
          var s = new Bpl.IdentifierExpr(f.tok, sV);
          bvars.Add(sV);
          argsF.Add(s); argsFFrame.Add(s);  // but not argsCanCall
        }

        bvars.Add(heapVar);
        argsF.Add(heap); argsCanCall.Add(heap);  // but not argsFFrame

        if (!f.IsStatic) {
          Bpl.BoundVariable thVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType));
          Bpl.Expr th = new Bpl.IdentifierExpr(f.tok, thVar);
          bvars.Add(thVar);
          argsF.Add(th); argsFFrame.Add(th); argsCanCall.Add(th);

          Type thisType = Resolver.GetReceiverType(f.tok, f);
          Bpl.Expr wh = Bpl.Expr.And(Bpl.Expr.Neq(th, predef.Null), etran.GoodRef(f.tok, th, thisType));
          wellFormed = Bpl.Expr.And(wellFormed, wh);
        }

        // (formalsAreWellFormed[h0] || canCallF(h0,...))
        Bpl.Expr fwf0 = Bpl.Expr.True;
        foreach (Formal p in f.Formals) {
          Bpl.BoundVariable bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)));
          bvars.Add(bv);
          Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
          argsF.Add(formal); argsFFrame.Add(formal); argsCanCall.Add(formal);
          Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran);
          if (wh != null) { fwf0 = Bpl.Expr.And(fwf0, wh); }
        }
        var canCall = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool));
        wellFormed = Bpl.Expr.And(wellFormed, Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, argsCanCall), fwf0));

        var fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        var F0 = new Bpl.NAryExpr(f.tok, fn, argsF);
        var fnFrame = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#frame", TrType(f.ResultType)));
        var F1 = new Bpl.NAryExpr(f.tok, fnFrame, argsFFrame);
        var eq = Bpl.Expr.Eq(F0, F1);
        var tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { F0 });

        var ax = new Bpl.ForallExpr(f.tok, typeParams, bvars, null, tr, Bpl.Expr.Imp(wellFormed, eq));
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax));
      } else {
#else
        // This is the general case                
        Bpl.Expr h0; var h0Var = BplBoundVar("$h0", predef.HeapType, out h0);
        Bpl.Expr h1; var h1Var = BplBoundVar("$h1", predef.HeapType, out h1);          
      
        var etran0 = new ExpressionTranslator(this, predef, h0);
        var etran1 = new ExpressionTranslator(this, predef, h1);

        Bpl.Expr wellFormed = Bpl.Expr.And(
          FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran0.HeapExpr),
          FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran1.HeapExpr));

        Bpl.TypeVariable alpha = new Bpl.TypeVariable(f.tok, "alpha");
        Bpl.Expr o; var oVar = BplBoundVar("$o", predef.RefType, out o);
        Bpl.Expr field; var fieldVar = BplBoundVar("$f", predef.FieldName(f.tok, alpha), out field);        
        Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
        Bpl.Expr oNotNullAlloced = Bpl.Expr.And(oNotNull, Bpl.Expr.And(etran0.IsAlloced(f.tok, o), etran1.IsAlloced(f.tok, o)));
        Bpl.Expr unchanged = Bpl.Expr.Eq(ReadHeap(f.tok, h0, o, field), ReadHeap(f.tok, h1, o, field));

        Bpl.Expr heapSucc = FunctionCall(f.tok, BuiltinFunction.HeapSucc, null, h0, h1);
        Bpl.Expr r0 = InRWClause(f.tok, o, field, f.Reads, etran0, null, null);
        Bpl.Expr q0 = new Bpl.ForallExpr(f.tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fieldVar },
          Bpl.Expr.Imp(Bpl.Expr.And(oNotNullAlloced, r0), unchanged));

        List<Bpl.Expr> tyexprs;
        var bvars = MkTyParamBinders(GetTypeParams(f), out tyexprs);
        var f0args = new List<Bpl.Expr>(tyexprs);
        var f1args = new List<Bpl.Expr>(tyexprs);
        var f0argsCanCall = new List<Bpl.Expr>(tyexprs);
        var f1argsCanCall = new List<Bpl.Expr>(tyexprs);
        if (f.IsRecursive) {
          Bpl.Expr s; var sV = BplBoundVar("$ly", predef.LayerType, out s);          
          bvars.Add(sV);
          f0args.Add(s); f1args.Add(s);  // but don't add to f0argsCanCall or f1argsCanCall
        }

        bvars.Add(h0Var); bvars.Add(h1Var);
        f0args.Add(h0); f1args.Add(h1); f0argsCanCall.Add(h0); f1argsCanCall.Add(h1);
        if (!f.IsStatic) {
          Bpl.Expr th; var thVar = BplBoundVar("this", predef.RefType, out th);
          bvars.Add(thVar);
          f0args.Add(th); f1args.Add(th); f0argsCanCall.Add(th); f1argsCanCall.Add(th);

          Type thisType = Resolver.GetReceiverType(f.tok, f);
          Bpl.Expr wh = Bpl.Expr.And(Bpl.Expr.Neq(th, predef.Null),
            Bpl.Expr.And(etran0.GoodRef(f.tok, th, thisType), etran1.GoodRef(f.tok, th, thisType)));
          wellFormed = Bpl.Expr.And(wellFormed, wh);
        }

        // (formalsAreWellFormed[h0] || canCallF(h0,...)) && (formalsAreWellFormed[h1] || canCallF(h1,...))
        Bpl.Expr fwf0 = Bpl.Expr.True;
        Bpl.Expr fwf1 = Bpl.Expr.True;
        foreach (Formal p in f.Formals) {
        Bpl.BoundVariable bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)));
          bvars.Add(bv);
          Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
          f0args.Add(formal); f1args.Add(formal); f0argsCanCall.Add(formal); f1argsCanCall.Add(formal);
          Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran0);
          if (wh != null) { fwf0 = Bpl.Expr.And(fwf0, wh); }
          wh = GetWhereClause(p.tok, formal, p.Type, etran1);
          if (wh != null) { fwf1 = Bpl.Expr.And(fwf1, wh); }
        }
        var canCall = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool));
        wellFormed = Bpl.Expr.And(wellFormed, Bpl.Expr.And(
          Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f0argsCanCall), fwf0), 
          Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f1argsCanCall), fwf1)));
      
        /*
        DR: I conjecture that this should be enough,
            as the requires is preserved when the frame is:

        wellFormed = Bpl.Expr.And(wellFormed, 
          Bpl.Expr.Or(new Bpl.NAryExpr(f.tok, canCall, f0argsCanCall), fwf0));
        */

        var fn = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        var F0 = new Bpl.NAryExpr(f.tok, fn, f0args);
        var F1 = new Bpl.NAryExpr(f.tok, fn, f1args);
        var eq = Bpl.Expr.Eq(F0, F1);
        var tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { heapSucc, F1 });

        var typeParams = TrTypeParamDecls(f.TypeArgs);
        var ax = new Bpl.ForallExpr(f.tok, typeParams, bvars, null, tr,
          Bpl.Expr.Imp(Bpl.Expr.And(wellFormed, heapSucc),
          Bpl.Expr.Imp(q0, eq)));
        sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, ax, comment));
#endif
#if POSSIBLY_FUTURE_OPTIMIZATION
      }
#endif
    }

    Bpl.Expr/*!*/ InRWClause(IToken tok, Bpl.Expr o, Bpl.Expr f, List<FrameExpression> rw, ExpressionTranslator etran,
                             Expression receiverReplacement, Dictionary<IVariable,Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(cce.NonNullElements(rw));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(predef != null);
      Contract.Requires((receiverReplacement == null) == (substMap == null));
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // requires o to denote an expression of type RefType
      // "rw" is is allowed to contain a WildcardExpr

      Bpl.Expr disjunction = Bpl.Expr.False;
      foreach (FrameExpression rwComponent in rw) {
        Expression e = rwComponent.E;
        if (receiverReplacement != null) {
          Contract.Assert(substMap != null);
          e = Substitute(e, receiverReplacement, substMap);
        }

        e = Resolver.FrameArrowToObjectSet(e, ref otherTmpVarCount);

        Bpl.Expr disjunct;
        var eType = e.Type.NormalizeExpand();
        if (e is WildcardExpr) {
          disjunct = Bpl.Expr.True;
        } else if (eType is SetType) {
          // old(e)[Box(o)]
          disjunct = etran.TrInSet(tok, o, e, ((SetType)eType).Arg);
        } else if (eType is SeqType) {
          // (exists i: int :: 0 <= i && i < Seq#Length(old(e)) && Seq#Index(old(e),i) == Box(o))
          Bpl.Expr boxO = FunctionCall(tok, BuiltinFunction.Box, null, o);
          Bpl.Variable iVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$i", Bpl.Type.Int));
          Bpl.Expr i = new Bpl.IdentifierExpr(tok, iVar);
          Bpl.Expr iBounds = InSeqRange(tok, i, etran.TrExpr(e), true, null, false);
          Bpl.Expr XsubI = FunctionCall(tok, BuiltinFunction.SeqIndex, predef.BoxType, etran.TrExpr(e), i);
          // TODO: the equality in the next line should be changed to one that understands extensionality
          disjunct = new Bpl.ExistsExpr(tok, new List<Variable> { iVar }, Bpl.Expr.And(iBounds, Bpl.Expr.Eq(XsubI, boxO)));
        } else {
          // o == old(e)
          disjunct = Bpl.Expr.Eq(o, etran.TrExpr(e));
        }
        if (rwComponent.Field != null && f != null) {
          disjunct = Bpl.Expr.And(disjunct, Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.tok, GetField(rwComponent.Field))));
        }
        disjunction = BplOr(disjunction, disjunct);
      }
      return disjunction;
    }

    private void AddWellformednessCheck(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);

      currentModule = f.EnclosingClass.Module;
      codeContext = f;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);
      // parameters of the procedure
      List<Variable> inParams = new List<Variable>();
      var typeInParams = MkTyParamFormals(GetTypeParams(f));
      if (!f.IsStatic) {
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), predef.Null),
          etran.GoodRef(f.tok, new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), Resolver.GetReceiverType(f.tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType, wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in f.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f), varType), p.Type, etran);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), varType, wh), true));
      }
      List<TypeVariable> typeParams = TrTypeParamDecls(f.TypeArgs);
      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      req.Add(Requires(f.tok, true, etran.HeightContext(f), null, null));
      // modifies $Heap, $Tick
      var mod = new List<Bpl.IdentifierExpr> {
        (Bpl.IdentifierExpr /*TODO: this cast is rather dubious*/)etran.HeapExpr,
        etran.Tick()
      };
      // check that postconditions hold
      var ens = new List<Bpl.Ensures>();
      foreach (Expression p in f.Ens) {
        var functionHeight = currentModule.CallGraph.GetSCCRepresentativeId(f);
        var splits = new List<SplitExprInfo>();
        bool splitHappened /*we actually don't care*/ = TrSplitExpr(p, splits, true, functionHeight, true, etran);
        foreach (var s in splits) {
          if (s.IsChecked && !RefinementToken.IsInherited(s.E.tok, currentModule)) {
            ens.Add(Ensures(s.E.tok, false, s.E, null, null));
          }
        }
      }
      Bpl.Procedure proc = new Bpl.Procedure(f.tok, "CheckWellformed$$" + f.FullSanitizedName, typeParams,
        Concat(typeInParams, inParams), new List<Variable>(),
        req, mod, ens, etran.TrAttributes(f.Attributes, null));
      sink.TopLevelDeclarations.Add(proc);

      if (InsertChecksums) {
        InsertChecksum(f, proc, true);
      }

      Contract.Assert(proc.InParams.Count == typeInParams.Count + inParams.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new Bpl.StmtListBuilder();
      builder.Add(new CommentCmd("AddWellformednessCheck for function " + f));
      builder.Add(CaptureState(f.tok, false, "initial state"));

      DefineFrame(f.tok, f.Reads, builder, locals, null);

      // check well-formedness of the preconditions (including termination, and reads checks), and then
      // assume each one of them
      var wfo = new WFOptions(null, true, true /* do delayed reads checks over requires */);

      // check well-formedness of the reads clause
      CheckFrameWellFormed(wfo, f.Reads, locals, builder, etran);

      // check the reads of the preconditions now
      foreach (var a in wfo.Asserts) {
        builder.Add(a);
      }

      foreach (Expression p in f.Req) {
        CheckWellformed(p, new WFOptions(null, true /* do reads checks */), locals, builder, etran);
        builder.Add(new Bpl.AssumeCmd(p.tok, etran.TrExpr(p)));
      }

      // check well-formedness of the decreases clauses (including termination, but no reads checks)
      foreach (Expression p in f.Decreases.Expressions)
      {
        CheckWellformed(p, new WFOptions(null, false), locals, builder, etran);
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
        var args = new List<Bpl.Expr>();
        foreach (var p in GetTypeParams(f)) {
          args.Add(trTypeParam(p, null));
        }
        if (f.IsRecursive) {
          args.Add(etran.LayerN(1));
        }
        args.Add(etran.HeapExpr);
        if (!f.IsStatic) {
          args.Add(new Bpl.IdentifierExpr(f.tok, etran.This, predef.RefType));
        }
        foreach (var p in f.Formals) {
          args.Add(new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f), TrType(p.Type)));
        }
        Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), args);

        var wh = GetWhereClause(f.tok, funcAppl, f.ResultType, etran);
        if (wh != null) {
          postCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, wh));
        }
      }
      // Now for the ensures clauses
      foreach (Expression p in f.Ens) {
        CheckWellformed(p, new WFOptions(f, false), locals, postCheckBuilder, etran);
        // assume the postcondition for the benefit of checking the remaining postconditions
        postCheckBuilder.Add(new Bpl.AssumeCmd(p.tok, etran.TrExpr(p)));
      }
      // Here goes the body (and include both termination checks and reads checks)
      StmtListBuilder bodyCheckBuilder = new StmtListBuilder();
      if (f.Body == null) {
        // don't fall through to postcondition checks
        bodyCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, Bpl.Expr.False));
      } else {
        Bpl.FunctionCall funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        List<Bpl.Expr> args = new List<Bpl.Expr>();
        foreach (var p in GetTypeParams(f)) {
          args.Add(trTypeParam(p, null));
        }
        if (f.IsRecursive) {
          args.Add(etran.LayerN(1));
        }
        args.Add(etran.HeapExpr);
        foreach (Variable p in implInParams) {
          args.Add(new Bpl.IdentifierExpr(f.tok, p));
        }
        Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, funcID, args);

        DefineFrame(f.tok, f.Reads, bodyCheckBuilder
                   , new List<Variable>() /* dummy local variable list, since frame axiom variable (and its definition) 
                                           * is already added. The only reason why we add the frame axiom definition 
                                           * again is to make boogie gives the same trace as before the change that
                                           * makes reads clauses also guard the requires */
                   , null);

        CheckWellformedWithResult(f.Body, new WFOptions(null, true), funcAppl, f.ResultType, locals, bodyCheckBuilder, etran);
      }
      // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
      postCheckBuilder.Add(new Bpl.AssumeCmd(f.tok, Bpl.Expr.False));
      builder.Add(new Bpl.IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));

      // var b$reads_guards_requires#0 : bool
      locals.AddRange(wfo.Locals);                                  
      // This ugly way seems to be the way to add things at the start of a builder:
      StmtList sl = builder.Collect(f.tok);
      // b$reads_guards_requires#0 := true   ...
      sl.BigBlocks[0].simpleCmds.InsertRange(0, wfo.AssignLocals); 

      Bpl.Implementation impl = new Bpl.Implementation(f.tok, proc.Name,
        typeParams, Concat(typeInParams, implInParams), new List<Variable>(),
        locals, sl, etran.TrAttributes(f.Attributes, null));
      sink.TopLevelDeclarations.Add(impl);

      if (InsertChecksums)
      {
        InsertChecksum(f, impl);
      }

      Contract.Assert(currentModule == f.EnclosingClass.Module);
      Contract.Assert(codeContext == f);
      currentModule = null;
      codeContext = null;
    }

    Bpl.Expr CtorInvocation(MatchCase mc, ExpressionTranslator etran, List<Variable> locals, StmtListBuilder localTypeAssumptions) {
      Contract.Requires(mc != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      List<Bpl.Expr> args = new List<Bpl.Expr>();
      for (int i = 0; i < mc.Arguments.Count; i++) {
        BoundVar p = mc.Arguments[i];
        Bpl.Variable local = new Bpl.LocalVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration), TrType(p.Type)));
        locals.Add(local);
        Type t = mc.Ctor.Formals[i].Type;
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, local), p.Type, etran);
        if (wh != null) {
          localTypeAssumptions.Add(new Bpl.AssumeCmd(p.tok, wh));
        }
        args.Add(CondApplyBox(mc.tok, new Bpl.IdentifierExpr(p.tok, local), cce.NonNull(p.Type), t));
      }
      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(mc.tok, mc.Ctor.FullName, predef.DatatypeType);
      return new Bpl.NAryExpr(mc.tok, new Bpl.FunctionCall(id), args);
    }

    Bpl.Expr CtorInvocation(IToken tok, DatatypeCtor ctor, ExpressionTranslator etran, List<Variable> locals, StmtListBuilder localTypeAssumptions) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // create local variables for the formals
      var args = new List<Bpl.Expr>();
      foreach (Formal arg in ctor.Formals) {
        Contract.Assert(arg != null);
        var nm = string.Format("a{0}#{1}", args.Count, otherTmpVarCount);
        otherTmpVarCount++;
        Bpl.Variable bv = new Bpl.LocalVariable(arg.tok, new Bpl.TypedIdent(arg.tok, nm, TrType(arg.Type)));
        locals.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.tok, bv));
      }

      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(tok, ctor.FullName, predef.DatatypeType);
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(id), args);
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
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        if (e.Obj is ThisExpr) {
          return Bpl.Expr.True;
        } else {
          Bpl.Expr r = CanCallAssumption(e.Obj, etran);
          return r;
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
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
        if (e.ResolvedUpdateExpr != null)
        {
          return CanCallAssumption(e.ResolvedUpdateExpr, etran);
        }
        Bpl.Expr total = CanCallAssumption(e.Seq, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        Bpl.Expr index = etran.TrExpr(e.Index);
        total = BplAnd(total, CanCallAssumption(e.Index, etran));
        total = BplAnd(total, CanCallAssumption(e.Value, etran));
        return total;
      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        return BplAnd(
          Cons(CanCallAssumption(e.Function, etran), 
          e.Args.ConvertAll(ee => CanCallAssumption(ee, etran))));
      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        // check well-formedness of receiver
        Bpl.Expr r = CanCallAssumption(e.Receiver, etran);
        // check well-formedness of the other parameters
        r = BplAnd(r, CanCallAssumption(e.Args, etran));
 //       if (e.Name != "requires" && e.Name != "reads") {
          Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
          // get to assume canCall
          Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null);
          Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
          r = BplAnd(r, canCallFuncAppl);
  //      }
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
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        return CanCallAssumption(e.E, etran);
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
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return BplAnd(CanCallAssumption(e.E0, etran), BplAnd(CanCallAssumption(e.E1, etran), CanCallAssumption(e.E2, etran)));

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          // CanCall[[ var b := RHS(g); Body(b,g,h) ]] =
          //   CanCall[[ RHS(g) ]] &&
          //   CanCall[[ Body(b,g,h)[b := PROTECT(RHS(g))] ]]
          // where PROTECT(e) means protect e from variable capture (which is achieved by translating
          // e and then putting it into a BoogieWrapper).  Actually, since the b may be a pattern,
          // the substitution is really [b0 := PROTECT( RHS(g).dtor )] for each b0 in b and each corresponding
          // path of destructors dtor.
          Bpl.Expr canCallRHS = Bpl.Expr.True;
          var substMap = new Dictionary<IVariable, Expression>();
          int i = 0;
          foreach (var lhs in e.LHSs) {
            canCallRHS = BplAnd(canCallRHS, CanCallAssumption(e.RHSs[i], etran));
            AddCasePatternVarSubstitutions(lhs, etran.TrExpr(e.RHSs[i]), substMap);
            i++;
          }
          var canCallBody = CanCallAssumption(Substitute(e.Body, null, substMap), etran);
          return BplAnd(canCallRHS, canCallBody);
        } else {
          // CanCall[[ var b :| RHS(b,g); Body(b,g,h) ]] =
          //   (forall b :: typeAntecedent ==>
          //       CanCall[[ RHS(b,g) ]] &&
          //       (RHS(b,g) ==> CanCall[[ Body(b,g,h) ]]) &&
          //       $let$canCall(b,g))
          var bvars = new List<Variable>();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(e.BoundVars.ToList<BoundVar>(), bvars);
          Contract.Assert(e.RHSs.Count == 1);  // this is true of all successfully resolved let-such-that expressions
          var canCallRHS = CanCallAssumption(e.RHSs[0], etran);
          var canCallBody = Bpl.Expr.Imp(etran.TrExpr(e.RHSs[0]), CanCallAssumption(e.Body, etran));
          var d = LetDesugaring(e);  // call LetDesugaring to prepare the desugaring and populate letSuchThatExprInfo with something for e
          var info = letSuchThatExprInfo[e];
          var canCallFunction = info.CanCallFunctionCall(this, etran);
          var cc = new Bpl.ForallExpr(e.tok, bvars, Bpl.Expr.Imp(typeAntecedent, BplAnd(BplAnd(canCallRHS, canCallBody), canCallFunction)));
          return cc;
        }

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        var canCall = CanCallAssumption(e.Body, etran);
        if (e.Contract != null)
          return BplAnd(canCall, CanCallAssumption(e.Contract, etran));
        else return canCall;
      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;

        List<Bpl.Variable> bvars = new List<Bpl.Variable>();

        int u = otherTmpVarCount++;
        Func<string, string> MkName = s => "$l" + u + "#" + s;

        Bpl.Expr heap; var hVar = BplBoundVar(MkName("heap"), predef.HeapType, out heap);
        bvars.Add(hVar);

        Dictionary<IVariable, Expression> subst = new Dictionary<IVariable,Expression>();
        foreach (var bv in e.BoundVars) {
          Bpl.Expr ve; var yVar = BplBoundVar(MkName(bv.Name), TrType(bv.Type), out ve);
          bvars.Add(yVar);

          subst[bv] = new BoogieWrapper(ve, bv.Type);
        }

        ExpressionTranslator et = new ExpressionTranslator(etran, heap);
        var ebody = CanCallAssumption(Substitute(e.Body, null, subst), et);
        return BplForall(bvars, ebody);
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var canCall = CanCallAssumption(e.Term, etran);
        var q = e as QuantifierExpr;
        var tyvars = MkTyParamBinders(q != null ? q.TypeArgs : new List<TypeParameter>());
        if (e.Range != null) {
          canCall = BplAnd(CanCallAssumption(e.Range, etran), BplImp(etran.TrExpr(e.Range), canCall));
        }
        if (canCall != Bpl.Expr.True) {
          List<Variable> bvars = new List<Variable>();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars);
          canCall = new Bpl.ForallExpr(expr.tok, Concat(tyvars, bvars), Bpl.Expr.Imp(typeAntecedent, canCall));
        }
        return canCall;
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return CanCallAssumption(e.E, etran);
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
      } else if (expr is BoogieFunctionCall) {
        var e = (BoogieFunctionCall)expr;
        return CanCallAssumption(e.Args, etran);
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var ite = etran.DesugarMatchExpr(e);
        return CanCallAssumption(ite, etran);
      } else if (expr is BoxingCastExpr) {
        var e = (BoxingCastExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is UnboxingCastExpr) {
        var e = (UnboxingCastExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    void AddCasePatternVarSubstitutions(CasePattern pat, Bpl.Expr rhs, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(pat != null);
      Contract.Requires(rhs != null);
      Contract.Requires(substMap != null);
      if (pat.Var != null) {
        substMap.Add(pat.Var, new BoogieWrapper(rhs, pat.Var.Type));
      } else if (pat.Arguments != null) {
        Contract.Assert(pat.Ctor != null);  // follows from successful resolution
        Contract.Assert(pat.Arguments.Count == pat.Ctor.Destructors.Count);  // follows from successful resolution
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var dtor = pat.Ctor.Destructors[i];
          var r = new Bpl.NAryExpr(pat.tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          var de = CondApplyUnbox(pat.tok, r, dtor.Type, arg.Expr.Type);
          AddCasePatternVarSubstitutions(arg, de, substMap);
        }
      }
    }

    void CheckCasePatternShape(CasePattern pat, Bpl.Expr rhs, StmtListBuilder builder) {
      Contract.Requires(pat != null);
      Contract.Requires(rhs != null);
      Contract.Requires(builder != null);
      if (pat.Var != null) {
        CheckSubrange(pat.tok, rhs, pat.Var.Type, builder);
      } else if (pat.Arguments != null) {
        Contract.Assert(pat.Ctor != null);  // follows from successful resolution
        Contract.Assert(pat.Arguments.Count == pat.Ctor.Destructors.Count);  // follows from successful resolution
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var ctor = pat.Ctor;
          var dtor = ctor.Destructors[i];
          var correctConstructor = FunctionCall(pat.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, rhs);
          if (ctor.EnclosingDatatype.Ctors.Count == 1) {
            // There is only one constructor, so the value must have been constructed by it; might as well assume that here.
            builder.Add(new Bpl.AssumeCmd(pat.tok, correctConstructor));
          } else {
            builder.Add(Assert(pat.tok, correctConstructor, string.Format("RHS is not certain to look like the pattern '{0}'", ctor.Name)));
          }

          var r = new Bpl.NAryExpr(pat.tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          var de = CondApplyUnbox(pat.tok, r, dtor.Type, arg.Expr.Type);
          CheckCasePatternShape(arg, de, builder);
        }
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
    void CheckNonNull(IToken tok, Expression e, Bpl.StmtListBuilder builder, ExpressionTranslator etran, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (e is ThisExpr) {
        // already known to be non-null
      } else if (e is StaticReceiverExpr) {
        // also ok
      } else {
        builder.Add(Assert(tok, Bpl.Expr.Neq(etran.TrExpr(e), predef.Null), "target object may be null", kv));
      }
    }

    /// <summary>
    /// Instances of WFContext are used as an argument to CheckWellformed, supplying options for the
    /// checks to be performed.
    /// If "SelfCallsAllowance" is non-null, termination checks will be omitted for calls that look
    /// like it.  This is useful in function postconditions, where the result of the function is
    /// syntactically given as what looks like a recursive call with the same arguments.
    /// "DoReadsChecks" indicates whether or not to perform reads checks.  If so, the generated code
    /// will make references to $_Frame.
    /// </summary>
    private class WFOptions
    {
      public readonly List<Bpl.Variable> Locals;
      public readonly List<Bpl.Cmd> Asserts;
      public readonly Function SelfCallsAllowance;
      public readonly bool DoReadsChecks;
      public readonly Bpl.QKeyValue AssertKv;

      public WFOptions() {
      }

      public WFOptions(Function selfCallsAllowance, bool doReadsChecks, bool saveReadsChecks = false) {
        SelfCallsAllowance = selfCallsAllowance;
        DoReadsChecks = doReadsChecks;
        if (saveReadsChecks) {
          Locals = new List<Variable>();
          Asserts = new List<Bpl.Cmd>();
        }
      }

      public WFOptions(Bpl.QKeyValue kv) {
        AssertKv = kv;
      }

      public Action<IToken, Bpl.Expr, string, Bpl.QKeyValue> AssertSink(Translator tran, StmtListBuilder builder) {
        return (t, e, s, qk) => {
          if (Locals != null) {
            var b = BplLocalVar("b$reqreads#" + tran.otherTmpVarCount++, Bpl.Type.Bool, Locals);
            Asserts.Add(tran.Assert(t, b, s, qk));
            builder.Add(Bpl.Cmd.SimpleAssign(e.tok, (Bpl.IdentifierExpr)b, e));
          } else {
            builder.Add(tran.Assert(t, e, s, qk));
          }
        };
      }

      public List<Bpl.AssignCmd> AssignLocals {
        get {
          return Map(Locals, l =>
            Bpl.Cmd.SimpleAssign(l.tok,
              new Bpl.IdentifierExpr(Token.NoToken, l),
              Bpl.Expr.True)
            );
        }
      }
    }

    void TrStmt_CheckWellformed(Expression expr, Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, bool subsumption) {
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

    void CheckWellformed(Expression expr, WFOptions options, List<Variable> locals, Bpl.StmtListBuilder builder, ExpressionTranslator etran) {
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
                                   List<Variable> locals, Bpl.StmtListBuilder builder, ExpressionTranslator etran) {
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
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        CheckFunctionSelectWF("naked function", builder, etran, e, " Possible solution: eta expansion.");
        CheckWellformed(e.Obj, options, locals, builder, etran);
        if (e.Obj.Type.IsRefType) {
          CheckNonNull(expr.tok, e.Obj, builder, etran, options.AssertKv);
        } else if (e.Member is DatatypeDestructor) {
          var dtor = (DatatypeDestructor)e.Member;
          var correctConstructor = FunctionCall(e.tok, dtor.EnclosingCtor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Obj));
          if (dtor.EnclosingCtor.EnclosingDatatype.Ctors.Count == 1) {
            // There is only one constructor, so the value must be been constructed by it; might as well assume that here.
            builder.Add(new Bpl.AssumeCmd(expr.tok, correctConstructor));
          } else {
            builder.Add(Assert(expr.tok, correctConstructor,
              string.Format("destructor '{0}' can only be applied to datatype values constructed by '{1}'", dtor.Name, dtor.EnclosingCtor.Name)));
          }
        }
        if (options.DoReadsChecks && e.Member is Field && ((Field)e.Member).IsMutable) {
          options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), etran.TrExpr(e.Obj), GetField(e)), "insufficient reads clause to read field", options.AssertKv);
        }
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        var eSeqType = e.Seq.Type.NormalizeExpand();
        bool isSequence = eSeqType is SeqType;
        CheckWellformed(e.Seq, options, locals, builder, etran);
        Bpl.Expr seq = etran.TrExpr(e.Seq);
        if (eSeqType.IsArrayType) {
          builder.Add(Assert(e.Seq.tok, Bpl.Expr.Neq(seq, predef.Null), "array may be null"));
        }
        Bpl.Expr e0 = null;
        if (eSeqType is MapType) {
          e0 = etran.TrExpr(e.E0);
          CheckWellformed(e.E0, options, locals, builder, etran);
          Bpl.Expr inDomain = FunctionCall(expr.tok, BuiltinFunction.MapDomain, predef.MapType(e.tok, predef.BoxType, predef.BoxType), seq);
          inDomain = Bpl.Expr.Select(inDomain, BoxIfNecessary(e.tok, e0, e.E0.Type));
          builder.Add(Assert(expr.tok, inDomain, "element may not be in domain", options.AssertKv));
        } else if (eSeqType is MultiSetType) {
          // cool

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
        if (options.DoReadsChecks && eSeqType.IsArrayType) {
          if (e.SelectOne) {
            Contract.Assert(e.E0 != null);
            Bpl.Expr fieldName = FunctionCall(expr.tok, BuiltinFunction.IndexField, null, etran.TrExpr(e.E0));
            options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), seq, fieldName), "insufficient reads clause to read array element", options.AssertKv);
          } else {
            Bpl.Expr lowerBound = e.E0 == null ? Bpl.Expr.Literal(0) : etran.TrExpr(e.E0);
            Contract.Assert(eSeqType.AsArrayType.Dims == 1);
            Bpl.Expr upperBound = e.E1 == null ? ArrayLength(e.tok, seq, 1, 0) : etran.TrExpr(e.E1);
            // check that, for all i in lowerBound..upperBound, a[i] is in the frame
            Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.tok, new Bpl.TypedIdent(e.tok, "$i", Bpl.Type.Int));
            Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.tok, iVar);
            var range = BplAnd(Bpl.Expr.Le(lowerBound, i), Bpl.Expr.Lt(i, upperBound));
            var fieldName = FunctionCall(e.tok, BuiltinFunction.IndexField, null, i);
            var allowedToRead = Bpl.Expr.SelectTok(e.tok, etran.TheFrame(e.tok), seq, fieldName);
            var qq = new Bpl.ForallExpr(e.tok, new List<Variable> { iVar }, Bpl.Expr.Imp(range, allowedToRead));
            options.AssertSink(this, builder)(expr.tok, qq, "insufficient reads clause to read the indicated range of array elements", options.AssertKv);
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
        if (e.ResolvedUpdateExpr != null)
        {
          CheckWellformedWithResult(e.ResolvedUpdateExpr, options, result, resultType, locals, builder, etran);
        }
        else
        {
          CheckWellformed(e.Seq, options, locals, builder, etran);
          Bpl.Expr seq = etran.TrExpr(e.Seq);
          Bpl.Expr index = etran.TrExpr(e.Index);
          Bpl.Expr value = etran.TrExpr(e.Value);
          CheckWellformed(e.Index, options, locals, builder, etran);
          var eSeqType = e.Seq.Type.NormalizeExpand();
          if (eSeqType is SeqType) {
            builder.Add(Assert(expr.tok, InSeqRange(expr.tok, index, seq, true, null, false), "index out of range", options.AssertKv));
          } else if (eSeqType is MapType) {
            // updates to maps are always valid if the values are well formed
          } else if (eSeqType is MultiSetType) {
            builder.Add(Assert(expr.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), value), "new number of occurrences might be negative", options.AssertKv));
          } else {
            Contract.Assert(false);
          }
          CheckWellformed(e.Value, options, locals, builder, etran);
        }
      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        int arity = e.Args.Count;
        var tt = e.Function.Type as ArrowType;
        Contract.Assert(tt != null);
        Contract.Assert(tt.Arity == arity);

        // check WF of receiver and arguments
        CheckWellformed(e.Function, options, locals, builder, etran);
        foreach (Expression arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }

        // check subranges of arguments
        for (int i = 0; i < arity; ++i) {
          CheckSubrange(e.Args[i].tok, etran.TrExpr(e.Args[i]), tt.Args[i], builder);
        }

        // check parameter availability
        if (etran.UsesOldHeap) {
          for (int i = 0; i < e.Args.Count; i++) {
            Expression ee = e.Args[i];
            Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran);
            if (wh != null) {
              builder.Add(Assert(ee.tok, wh, "argument must be allocated in the state in which the function is invoked"));
            }
          }
        }

        // translate arguments to requires and reads
        Func<Expression, Bpl.Expr> TrArg = arg => {
          Bpl.Expr inner = etran.TrExpr(arg);
          if (ModeledAsBoxType(arg.Type)) {
            return inner;
          } else {
            return FunctionCall(arg.tok, BuiltinFunction.Box, null, inner);
          }
        };

        var args = Concat(
          Map(tt.TypeArgs, TypeToTy),
          Cons(etran.TrExpr(e.Function), 
          Cons(etran.HeapExpr, 
          e.Args.ConvertAll(arg => TrArg(arg)))));

        // check precond
        var precond = FunctionCall(e.tok, Requires(arity), Bpl.Type.Bool, args);
        builder.Add(Assert(expr.tok, precond, "possible violation of function precondition"));

        if (options.DoReadsChecks) {
          Type objset = new SetType(new ObjectType());
          Expression wrap = new BoogieWrapper(
            FunctionCall(e.tok, Reads(arity), TrType(objset), args),
            objset);
          var reads = new FrameExpression(e.tok, wrap, null);
          CheckFrameSubset(expr.tok, new List<FrameExpression>{ reads }, null, null, 
            etran, options.AssertSink(this, builder), "insufficient reads clause to invoke function", options.AssertKv);
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        // check well-formedness of receiver
        CheckWellformed(e.Receiver, options, locals, builder, etran);
        if (!e.Function.IsStatic && !(e.Receiver is ThisExpr) && !(e.Receiver.Type is ArrowType)) {
          CheckNonNull(expr.tok, e.Receiver, builder, etran, options.AssertKv);
        } else if (e.Receiver.Type is ArrowType) {
          CheckFunctionSelectWF("function specification", builder, etran, e.Receiver, "");
        }
        // check well-formedness of the other parameters
        foreach (Expression arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }
        // create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.Function.Formals.Count; i++) {
          Formal p = e.Function.Formals[i];
          // Note, in the following, the "##" makes the variable invisible in BVD.  An alternative would be to communicate
          // to BVD what this variable stands for and display it as such to the user.
          LocalVariable local = new LocalVariable(p.tok, p.tok, "##" + p.Name, p.Type, p.IsGhost);
          local.type = local.OptionalType;  // resolve local here
          IdentifierExpr ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration));
          ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(p, ie);
          locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration), TrType(local.Type))));
          Bpl.IdentifierExpr lhs = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
          Expression ee = e.Args[i];
          Type et = Resolver.SubstType(p.Type, e.TypeArgumentSubstitutions);
          CheckSubrange(ee.tok, etran.TrExpr(ee), et, builder);
          Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.tok, lhs, CondApplyBox(p.tok, etran.TrExpr(ee), cce.NonNull(ee.Type), p.Type));
          builder.Add(cmd);
          builder.Add(new Bpl.CommentCmd("assume allocatedness for argument to function"));
          builder.Add(new Bpl.AssumeCmd(e.Args[i].tok, MkIsAlloc(lhs, et, etran.HeapExpr)));
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
          Expression precond = Substitute(p, e.Receiver, substMap, e.TypeArgumentSubstitutions);
          bool splitHappened;  // we don't actually care
          foreach (var ss in TrSplitExpr(precond, etran, true, out splitHappened)) {
            if (ss.IsChecked) {
              var tok = new NestedToken(expr.tok, ss.E.tok);
              if (options.AssertKv != null) {
                // use the given assert attribute only
                builder.Add(Assert(tok, ss.E, "possible violation of function precondition", options.AssertKv));
              } else {
                builder.Add(AssertNS(tok, ss.E, "possible violation of function precondition"));
              }
            }
          }
          if (options.AssertKv == null) {
            // assume only if no given assert attribute is given
            builder.Add(new Bpl.AssumeCmd(expr.tok, etran.TrExpr(precond)));
          }
        }
        if (options.DoReadsChecks) {
          // check that the callee reads only what the caller is already allowed to read
          var s = new Substituter(null, new Dictionary<IVariable,Expression>(), e.TypeArgumentSubstitutions, this);
          CheckFrameSubset(expr.tok,
            e.Function.Reads.ConvertAll(s.SubstFrameExpr),
            e.Receiver, substMap, etran, options.AssertSink(this, builder), "insufficient reads clause to invoke function", options.AssertKv);
        }

        Bpl.Expr allowance = null;
        if (codeContext != null && e.CoCall != FunctionCallExpr.CoCallResolution.Yes && !(e.Function is CoPredicate)) {
          // check that the decreases measure goes down
          if (ModuleDefinition.InSameSCC(e.Function, codeContext)) {
            List<Expression> contextDecreases = codeContext.Decreases.Expressions;
            List<Expression> calleeDecreases = e.Function.Decreases.Expressions;
            if (e.Function == options.SelfCallsAllowance) {
              allowance = Bpl.Expr.True;
              if (!e.Function.IsStatic) {
                allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(e.Receiver), new Bpl.IdentifierExpr(e.tok, etran.This, predef.RefType)));
              }
              for (int i = 0; i < e.Args.Count; i++) {
                Expression ee = e.Args[i];
                Formal ff = e.Function.Formals[i];
                allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(ee), new Bpl.IdentifierExpr(e.tok, ff.AssignUniqueName(currentDeclaration), TrType(ff.Type))));
              }
            }
            string hint;
            switch (e.CoCall) {
              case FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasSideEffects:
                hint = "note that only functions without side effects can be called co-recursively";
                break;
              case FunctionCallExpr.CoCallResolution.NoBecauseFunctionHasPostcondition:
                hint = "note that only functions without any ensures clause can be called co-recursively";
                break;
              case FunctionCallExpr.CoCallResolution.NoBecauseIsNotGuarded:
                hint = "note that the call is not sufficiently guarded to be used co-recursively";
                break;
              case FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsAreNotAllowedInThisContext:
                hint = "note that calls cannot be co-recursive in this context";
                break;
              case FunctionCallExpr.CoCallResolution.NoBecauseRecursiveCallsInDestructiveContext:
                hint = "note that a call can be co-recursive only if all intra-cluster calls are in non-destructive contexts";
                break;
              case FunctionCallExpr.CoCallResolution.No:
                hint = null;
                break;
              default:
                Contract.Assert(false);  // unexpected CoCallResolution
                goto case FunctionCallExpr.CoCallResolution.No;  // please the compiler
            }
            CheckCallTermination(expr.tok, contextDecreases, calleeDecreases, allowance, e.Receiver, substMap, etran, etran, builder,
              codeContext.InferredDecreases, hint);
          }

        }
        // all is okay, so allow this function application access to the function's axiom, except if it was okay because of the self-call allowance.
        Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
        List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null);
        Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
        builder.Add(new Bpl.AssumeCmd(expr.tok, allowance == null ? canCallFuncAppl : Bpl.Expr.Or(allowance, canCallFuncAppl)));

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          var arg = dtv.Arguments[i];
          CheckWellformed(arg, options, locals, builder, etran);

          // Cannot use the datatype's formals, so we substitute the inferred type args:
          var su = new Dictionary<TypeParameter, Type>();
          foreach (var p in dtv.Ctor.EnclosingDatatype.TypeArgs.Zip(dtv.InferredTypeArgs)) {
            su[p.Item1] = p.Item2;            
          }
          Type ty = Resolver.SubstType(formal.Type, su);
          CheckSubrange(arg.tok, etran.TrExpr(arg), ty, builder);
        }
      } else if (expr is OldExpr) {
        OldExpr e = (OldExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran.Old);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
        if (e is ConversionExpr) {
          var ee = (ConversionExpr)e;
          if (ee.ToType is IntType && ee.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
            // this operation is well-formed only if the real-based number represents an integer
            // assert ToReal(ToInt(e.E)) == e.E
            var arg = etran.TrExpr(e.E);
            Bpl.Expr isAnInt = new Bpl.NAryExpr(e.tok, new ArithmeticCoercion(e.tok, ArithmeticCoercion.CoercionType.ToInt), new List<Expr> { arg });
            isAnInt = new Bpl.NAryExpr(e.tok, new ArithmeticCoercion(e.tok, ArithmeticCoercion.CoercionType.ToReal), new List<Expr> { isAnInt });
            isAnInt = Bpl.Expr.Binary(e.tok, BinaryOperator.Opcode.Eq, isAnInt, arg);
            builder.Add(Assert(expr.tok, isAnInt, "the real-based number must be an integer (if you want truncation, apply .Trunc to the real-based number)"));
          }
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
          case BinaryExpr.ResolvedOpcode.Mod: {
              Bpl.Expr zero = e.E1.Type.IsNumericBased(Type.NumericPersuation.Real) ? Bpl.Expr.Literal(Basetypes.BigDec.ZERO) : Bpl.Expr.Literal(0);
              CheckWellformed(e.E1, options, locals, builder, etran);
              builder.Add(Assert(expr.tok, Bpl.Expr.Neq(etran.TrExpr(e.E1), zero), "possible division by zero", options.AssertKv));
            }
            break;
          default:
            CheckWellformed(e.E1, options, locals, builder, etran);
            break;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        foreach (var ee in e.SubExpressions) {
          CheckWellformed(ee, options, locals, builder, etran);
        }
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            builder.Add(Assert(expr.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E0)), "prefix-equality limit must be at least 0", options.AssertKv));

            break;
          default:
            Contract.Assert(false);  // unexpected ternary expression
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          var substMap = SetupBoundVarsAsLocals(e.BoundVars.ToList<BoundVar>(), builder, locals, etran);
          Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
          for (int i = 0; i < e.LHSs.Count; i++) {
            var pat = e.LHSs[i];
            var rhs = e.RHSs[i];
            var nm = string.Format("let{0}#{1}", i, otherTmpVarCount);
            otherTmpVarCount++;
            var r = new Bpl.LocalVariable(pat.tok, new Bpl.TypedIdent(pat.tok, nm, TrType(rhs.Type)));
            locals.Add(r);
            var rIe = new Bpl.IdentifierExpr(pat.tok, r);
            CheckWellformedWithResult(e.RHSs[i], options, rIe, pat.Expr.Type, locals, builder, etran);
            CheckCasePatternShape(pat, rIe, builder);
            builder.Add(new Bpl.AssumeCmd(pat.tok, Bpl.Expr.Eq(etran.TrExpr(Substitute(pat.Expr, null, substMap)), rIe)));
          }
          CheckWellformedWithResult(Substitute(e.Body, null, substMap), options, result, resultType, locals, builder, etran);
          result = null;
        } else {
          // CheckWellformed(var b :| RHS(b); Body(b)) =
          //   var b where typeAntecedent;
          //   CheckWellformed(RHS(b));
          //   assert (exists b' :: typeAntecedent' && RHS(b'));
          //   assume RHS(b);
          //   CheckWellformed(Body(b));
          Contract.Assert(e.RHSs.Count == 1);  // this is true of all successfully resolved let-such-that expressions
          List<BoundVar> lhsVars = e.BoundVars.ToList<BoundVar>();
          var substMap = SetupBoundVarsAsLocals(lhsVars, builder, locals, etran);
          var rhs = Substitute(e.RHSs[0], null, substMap);
          CheckWellformed(rhs, options, locals, builder, etran);
          List<Tuple<List<BoundVar>, Expression>> partialGuesses = GeneratePartialGuesses(lhsVars, e.RHSs[0]);
          Bpl.Expr w = Bpl.Expr.False;
          foreach (var tup in partialGuesses) {
            var body = etran.TrExpr(tup.Item2);
            if (tup.Item1.Count != 0) {
              var bvs = new List<Variable>();
              var typeAntecedent = etran.TrBoundVariables(tup.Item1, bvs);
              body = new Bpl.ExistsExpr(e.tok, bvs, BplAnd(typeAntecedent, body));
            }
            w = BplOr(body, w);
          }
          builder.Add(Assert(e.tok, w, "cannot establish the existence of LHS values that satisfy the such-that predicate"));
          builder.Add(new Bpl.AssumeCmd(e.tok, etran.TrExpr(rhs)));
          var letBody = Substitute(e.Body, null, substMap);
          CheckWellformed(letBody, options, locals, builder, etran);
          // If we are supposed to assume "result" to equal this expression, then use the body of the let-such-that, not the generated $let#... function
          if (result != null) {
            Contract.Assert(resultType != null);
            var bResult = etran.TrExpr(letBody);
            CheckSubrange(letBody.tok, bResult, resultType, builder);
            builder.Add(new Bpl.AssumeCmd(letBody.tok, Bpl.Expr.Eq(result, bResult)));
            builder.Add(new Bpl.AssumeCmd(letBody.tok, CanCallAssumption(letBody, etran)));
            builder.Add(new CommentCmd("CheckWellformedWithResult: Let expression"));
            builder.Add(new Bpl.AssumeCmd(letBody.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
            builder.Add(new Bpl.AssumeCmd(letBody.tok, MkIs(result, resultType)));
            result = null;
          }
        }

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        CheckWellformedWithResult(e.Body, options, result, resultType, locals, builder, etran);
        if (e.Contract != null) {
          CheckWellformedWithResult(e.Contract, options, result, resultType, locals, builder, etran);
          var theSame = Bpl.Expr.Eq(etran.TrExpr(e.Body), etran.TrExpr(e.Contract));
          builder.Add(Assert(new ForceCheckToken(e.ReplacerToken), theSame, "replacement must be the same value"));
        }
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var q = e as QuantifierExpr;
        var lam = e as LambdaExpr;

        var typeMap = new Dictionary<TypeParameter, Type>();
        var copies = new List<TypeParameter>();
        if (q != null) {
          copies = Map(q.TypeArgs, tp => q.Refresh(tp, ref otherTmpVarCount));
          typeMap = Util.Dict(q.TypeArgs, Map(copies, tp => (Type)new UserDefinedType(tp)));
        }
        locals.AddRange(Map(copies,
          tp => new Bpl.LocalVariable(tp.tok, new TypedIdent(tp.tok, nameTypeParam(tp), predef.Ty))));
        var substMap = SetupBoundVarsAsLocals(e.BoundVars, builder, locals, etran, typeMap);
        var s = new Substituter(null, substMap, typeMap, this);
        var body = Substitute(e.Term, null, substMap, typeMap);
        List<FrameExpression> reads = null;

        var newOptions = options;
        var newEtran = etran;
        builder.Add(new Bpl.CommentCmd("Begin Comprehension WF check"));
        BplIfIf(e.tok, lam != null, null, builder, newBuilder => {

          if (lam != null) {
            // Havoc heap, unless oneShot
            if (!lam.OneShot) {
              Bpl.Expr oldHeap;
              locals.Add(BplLocalVar("$oldHeap#" + otherTmpVarCount++, predef.HeapType, out oldHeap));
              newBuilder.Add(BplSimplestAssign(oldHeap, etran.HeapExpr));
              newBuilder.Add(new HavocCmd(expr.tok, Singleton((Bpl.IdentifierExpr)etran.HeapExpr)));
              newBuilder.Add(new AssumeCmd(expr.tok,
                FunctionCall(expr.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr)));
              newBuilder.Add(new AssumeCmd(expr.tok, HeapSameOrSucc(oldHeap, etran.HeapExpr)));
            }

            // Set up a new frame
            var frameName = "$_Frame#l" + otherTmpVarCount++;
            reads = lam.Reads.ConvertAll(s.SubstFrameExpr);
            DefineFrame(e.tok, reads, newBuilder, locals, frameName);
            newEtran = new ExpressionTranslator(newEtran, frameName);

            // Check frame WF and that it read covers itself
            newOptions = new WFOptions(options.SelfCallsAllowance, true /* check reads clauses */, true /* delay reads checks */);

            CheckFrameWellFormed(newOptions, reads, locals, newBuilder, newEtran);

            // new options now contains the delayed reads checks
            locals.AddRange(newOptions.Locals);
            // assign locals to true, but at a scope above 
            Contract.Assert(newBuilder != builder);
            foreach (var a in newOptions.AssignLocals) {
              builder.Add(a);
            }

            // add asserts to the current builder (right after frame WF)
            foreach (var a in newOptions.Asserts) {
              newBuilder.Add(a);
            }

            // continue doing reads checks, but don't delay them
            newOptions = new WFOptions(options.SelfCallsAllowance, true, false);
          }

          // check requires/range
          Bpl.Expr guard = null;
          if (e.Range != null) {
            var range = Substitute(e.Range, null, substMap);
            CheckWellformed(range, newOptions, locals, newBuilder, newEtran);
            guard = etran.TrExpr(range);
          }

          BplIfIf(e.tok, guard != null, guard, newBuilder, b => {
            CheckWellformed(body, newOptions, locals, b, newEtran);
          });

          if (lam != null && !lam.OneShot) {
            // assume false (heap was havoced inside an if)
            Contract.Assert(newBuilder != builder);
            newBuilder.Add(new AssumeCmd(e.tok, Bpl.Expr.False));
          }
        });
        builder.Add(new Bpl.CommentCmd("End Comprehension WF check"));

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        TrStmt(e.S, builder, locals, etran);
        CheckWellformed(e.E, options, locals, builder, etran);

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        CheckWellformed(e.Test, options, locals, builder, etran);
        var bThen = new Bpl.StmtListBuilder();
        var bElse = new Bpl.StmtListBuilder();
        CheckWellformedWithResult(e.Thn, options, result, resultType, locals, bThen, etran);
        CheckWellformedWithResult(e.Els, options, result, resultType, locals, bElse, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.Test), bThen.Collect(expr.tok), null, bElse.Collect(expr.tok)));
        result = null;

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
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(me.tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0)
          {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
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

      } else if (expr is BoogieFunctionCall) {
        var e = (BoogieFunctionCall)expr;
        foreach (var arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (result != null) {
        Contract.Assert(resultType != null);
        var bResult = etran.TrExpr(expr);
        CheckSubrange(expr.tok, bResult, resultType, builder);
        builder.Add(new Bpl.AssumeCmd(expr.tok, Bpl.Expr.Eq(result, bResult)));
        builder.Add(new Bpl.AssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
        builder.Add(new CommentCmd("CheckWellformedWithResult: any expression"));
        builder.Add(new Bpl.AssumeCmd(expr.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
        builder.Add(new Bpl.AssumeCmd(expr.tok, MkIs(result, resultType)));
      }
    }

    void CheckFunctionSelectWF(string what, StmtListBuilder builder, ExpressionTranslator etran, Expression e, string hint) {
      Function fn = null;
      var sel = e as MemberSelectExpr;
      if (sel != null) {
        fn = sel.Member as Function;
      }
      if (fn != null) {
        builder.Add(Assert(e.tok, Bpl.Expr.Not(etran.HeightContext(fn)),
          "cannot use " + what + " in recursive setting." + hint));
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

    // Use trType to translate types in the args list
    Bpl.Expr ClassTyCon(UserDefinedType cl, List<Expr> args) {
      return ClassTyCon(cl.ResolvedClass, args);
    }

    Bpl.Expr ClassTyCon(TopLevelDecl cl, List<Expr> args) {
      Contract.Assert(cl != null);
      Contract.Assert(Contract.ForAll(args, a => a != null));
      return FunctionCall(cl.tok, GetClassTyCon(cl), predef.Ty, args);
    }

    // Takes a Bpl.Constant, which typically will be one from GetClass,
    // or some built-in type which has a class name, like Arrays or Arrows.
    // Note: Prefer to call ClassTyCon or TypeToTy instead.
    private string GetClassTyCon(TopLevelDecl dl) {
      Contract.Requires(dl != null);
      int n = dl.TypeArgs.Count; // arity
      string name;
      if (classConstants.TryGetValue(dl, out name)) {
        Contract.Assert(name != null);
      } else {
        name = AddTyAxioms(dl);
        classConstants.Add(dl, name);
      }
      return name;
    }

    public string Handle(int arity) {
      return "Handle" + arity;
    }

    public string Apply(int arity) {
      return "Apply" + arity;
    }

    public string Requires(int arity) {
      return "Requires" + arity;
    }

    public string Reads(int arity) {
      return "Reads" + arity;
    }

    public string RequiresName(Function f) {
      return f.FullSanitizedName + "#requires";
    }

    public string FunctionHandle(Function f) {
      Contract.Requires(f != null);
      string name;
      if (functionHandles.TryGetValue(f, out name)) {
        Contract.Assert(name != null);
      } else {
        name = f.FullSanitizedName + "#Handle";
        functionHandles[f] = name;
        var args = new List<Bpl.Expr>();
        var vars = MkTyParamBinders(GetTypeParams(f), out args);
        var formals = MkTyParamFormals(GetTypeParams(f), false);
        var tyargs = new List<Bpl.Expr>(); 
        foreach (var fm in f.Formals) {
          tyargs.Add(TypeToTy(fm.Type));
        }
        tyargs.Add(TypeToTy(f.ResultType));
        if (f.IsRecursive) {
          Bpl.Expr ly; vars.Add(BplBoundVar("$ly", predef.LayerType, out ly)); args.Add(ly);
          formals.Add(BplFormalVar(null, predef.LayerType, true));
        }

        var enclosingArrow = f.EnclosingClass as ArrowType.ArrowTypeDecl;
        var fromArrowType = enclosingArrow != null;

        Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocSelf = x => x;
        Expression selfExpr = null;
        Dictionary<IVariable, Expression> rhs_dict = null;
        if (!f.IsStatic) {
          var selfTy = fromArrowType ? predef.HandleType : predef.RefType;
          var self = BplBoundVar("$self", selfTy, vars);
          formals.Add(BplFormalVar(null, selfTy, true));
          SnocSelf = xs => Snoc(xs, self);
          selfExpr = new BoogieWrapper(self, fromArrowType ? f.Type : new ObjectType());
                                          // ^ is this an ok type for this wrapper?
          rhs_dict = new Dictionary<IVariable, Expression>();
        }

        // F#Handle(Ty, .., Ty, LayerType, ref) : HandleType
        sink.TopLevelDeclarations.Add(
          new Bpl.Function(f.tok, name, formals, BplFormalVar(null, predef.HandleType, false)));

        var bvars = new List<Bpl.Variable>();
        var lhs_args = new List<Bpl.Expr>();
        var rhs_args = new List<Bpl.Expr>();

        var i = 0;
        foreach (var fm in f.Formals) {
          var fe = BplBoundVar("x#" + i++, predef.BoxType, bvars);
          lhs_args.Add(fe);
          var be = UnboxIfBoxed(fe, fm.Type);
          rhs_args.Add(be);
          if (rhs_dict != null) {
            rhs_dict[fm] = new BoogieWrapper(be, fm.Type);
          }
        }

        var h = BplBoundVar("$heap", predef.HeapType, vars);

        int arity = f.Formals.Count;

        {
          // Apply(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN) 
          //   = [Box] F(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(args));
          var lhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(fhandle, Cons(h, lhs_args))));
          var rhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(Snoc(args, h)), rhs_args));
          var rhs_boxed = BoxIfUnboxed(rhs, f.ResultType);

          sink.TopLevelDeclarations.Add(new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs_boxed))));
        }

        {
          // Requires(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN) 
          //   = F#Requires(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)
          //   || Scramble(...)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(args));
          var lhs = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(tyargs, Cons(fhandle, Cons(h, lhs_args))));
          var rhs = BplOr(
            FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, Concat(SnocSelf(Snoc(args, h)), rhs_args)),
            MakeScrambler(f.tok, f.FullSanitizedName + "#lessReq", Concat(vars, bvars)));

          // In case this is the /requires/ or /reads/ function, then there is no precondition
          if (fromArrowType) {
            rhs = Bpl.Expr.True;
          }

          sink.TopLevelDeclarations.Add(new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }

        {
          // Reads(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)[Box(o)] 
          //   =  $Frame_F(args...)[o]
          // //  && Scramble(...)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(args));
          Bpl.Expr o; var oVar = BplBoundVar("o", predef.RefType, out o);
          Bpl.Expr lhs_inner = FunctionCall(f.tok, Reads(arity), Bpl.Type.Bool, Concat(tyargs, Cons(fhandle, Cons(h, lhs_args))));
          Bpl.Expr lhs = new Bpl.NAryExpr(f.tok, new Bpl.MapSelect(f.tok, 1),
            new List<Bpl.Expr> { lhs_inner, FunctionCall(f.tok, BuiltinFunction.Box, null, o) });

          var et = new ExpressionTranslator(this, predef, h);
          var rhs = InRWClause(f.tok, o, null, f.Reads, et, selfExpr, rhs_dict);
                           // MakeScrambler(f.tok, f.FullSanitizedName + "#extraReads", Cons(oVar, Concat(vars, bvars))));

          sink.TopLevelDeclarations.Add(new Axiom(f.tok,
            BplForall(Cons(oVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }
      }
      return name;
    }

    public Bpl.Expr MakeScrambler(IToken tk, string name, List<Variable> bvars) {
      var f = new Bpl.Function(tk, name,
        bvars.ConvertAll(bv => (Bpl.Variable)BplFormalVar(null, bv.TypedIdent.Type, true)),
        BplFormalVar(null, Bpl.Type.Bool, false));

      sink.TopLevelDeclarations.Add(f);
      return FunctionCall(tk, name, Bpl.Type.Bool, bvars.ConvertAll(bv => (Bpl.Expr)new Bpl.IdentifierExpr(tk, bv)));
    }

    private void AddArrowTypeAxioms(ArrowType.ArrowTypeDecl ad) {
      var arity = ad.Arity;
      var tok = ad.tok;

      // [Heap, Box, ..., Box]
      var map_args = Cons(predef.HeapType, Map(Enumerable.Range(0, arity), i => predef.BoxType));
      // [Heap, Box, ..., Box] Box
      var apply_ty = new Bpl.MapType(tok, new List<Bpl.TypeVariable>(), map_args, predef.BoxType);
      // [Heap, Box, ..., Box] Bool
      var requires_ty = new Bpl.MapType(tok, new List<Bpl.TypeVariable>(), map_args, Bpl.Type.Bool);
      // Set Box
      var objset_ty = TrType(new SetType(new ObjectType()));
      // [Heap, Box, ..., Box] (Set Box)
      var reads_ty = new Bpl.MapType(tok, new List<Bpl.TypeVariable>(), map_args, objset_ty);

      {
        // function HandleN([Heap, Box, ..., Box] Box, [Heap, Box, ..., Box] Bool) : HandleType
        var res = BplFormalVar(null, predef.HandleType, true);
        var arg = new List<Bpl.Variable> {
          BplFormalVar(null, apply_ty, true), 
          BplFormalVar(null, requires_ty, true),
          BplFormalVar(null, reads_ty, true)
        };
        sink.TopLevelDeclarations.Add(new Bpl.Function(Token.NoToken, Handle(arity), arg, res));
      }

      Action<string, Bpl.Type> SelectorFunction = (s, t) => {
        var args = new List<Bpl.Variable>();
        MapM(Enumerable.Range(0, arity + 1), i => args.Add(BplFormalVar(null, predef.Ty, true)));
        args.Add(BplFormalVar(null, predef.HandleType, true));
        args.Add(BplFormalVar(null, predef.HeapType, true));
        MapM(Enumerable.Range(0, arity), i => args.Add(BplFormalVar(null, predef.BoxType, true)));
        sink.TopLevelDeclarations.Add(new Bpl.Function(Token.NoToken, s, args, BplFormalVar(null, t, false)));
      };

      // function ApplyN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Box
      SelectorFunction(Apply(arity), predef.BoxType);
      // function RequiresN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Bool
      SelectorFunction(Requires(arity), Bpl.Type.Bool);
      // function ReadsN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Set Box
      SelectorFunction(Reads(arity), objset_ty);

      {
        // forall t1, .., tN+1 : Ty, p: [Heap, Box, ..., Box] Box, heap : Heap, b1, ..., bN : Box 
        //      :: RequriesN(...) ==> ApplyN(t1, .. tN+1, HandleN(h, r, rd), heap, b1, ..., bN) = h[heap, b1, ..., bN]
        //
        // no precondition for these, but:
        // for requires, we add: RequiresN(...) <== r[heap, b1, ..., bN] 
        // for reads, we could:  ReadsN(...)[bx] ==> rd[heap, b1, ..., bN][bx] , but we don't
        Action<string, Bpl.Type, string, Bpl.Type, string, Bpl.Type> SelectorSemantics = (selector, selectorTy, selectorVar, selectorVarTy, precond, precondTy) => {
          Contract.Assert((precond == null) == (precondTy == null));
          var bvars = new List<Bpl.Variable>();

          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));

          var heap = BplBoundVar("heap", predef.HeapType, bvars);

          var handleargs = new List<Bpl.Expr> {
            BplBoundVar("h", apply_ty, bvars),
            BplBoundVar("r", requires_ty, bvars),
            BplBoundVar("rd", reads_ty, bvars)
          };

          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var lhsargs = Concat(types, Cons(FunctionCall(tok, Handle(arity), predef.HandleType, handleargs), Cons(heap, boxes)));
          Bpl.Expr lhs = FunctionCall(tok, selector, selectorTy, lhsargs);
          Func<Bpl.Expr, Bpl.Expr> pre = x => x;
          if (precond != null) {
            pre = x => FunctionCall(tok, precond, precondTy, lhsargs);
          }

          Bpl.Expr rhs = new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, arity + 1),
            Cons(new Bpl.IdentifierExpr(tok, selectorVar, selectorVarTy), Cons(heap, boxes)));
          Func<Bpl.Expr, Bpl.Expr, Bpl.Expr> op = Bpl.Expr.Eq;
          if (selectorVar == "rd") {
            var bx = BplBoundVar("bx", predef.BoxType, bvars);
            lhs = new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> { lhs, bx });
            rhs = new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> { rhs, bx });
            // op = Bpl.Expr.Imp;
          }
          if (selectorVar == "r") {
            op = (u, v) => Bpl.Expr.Imp(v, u);
          }
          sink.TopLevelDeclarations.Add(new Axiom(tok,
            BplForall(bvars, BplTrigger(lhs), op(lhs, rhs))));
        };
        SelectorSemantics(Apply(arity), predef.BoxType, "h", apply_ty, Requires(arity), requires_ty);
        SelectorSemantics(Requires(arity), Bpl.Type.Bool, "r", requires_ty, null, null);
        SelectorSemantics(Reads(arity), objset_ty, "rd", reads_ty, null, null);

        // function {:inline true} 
        //   FuncN._requires(G...G G: Ty, H:Heap, f:Handle, x ... x :Box): bool 
        //   { RequiresN(f, H, x...x) }
        // function {:inline true} 
        //   FuncN._requires#canCall(G...G G: Ty, H:Heap, f:Handle, x ... x :Box): bool 
        //   { true }
        // + similar for Reads
        Action<string, Function> UserSelectorFunction = (fname, f) => {
          var formals = new List<Bpl.Variable>();
          var rhsargs = new List<Bpl.Expr>();

          MapM(Enumerable.Range(0, arity + 1), i => rhsargs.Add(BplFormalVar("t" + i, predef.Ty, true, formals)));

          var heap = BplFormalVar("heap", predef.HeapType, true, formals);
          rhsargs.Add(BplFormalVar("f", predef.HandleType, true, formals));
          rhsargs.Add(heap);

          MapM(Enumerable.Range(0, arity), i => rhsargs.Add(BplFormalVar("bx" + i, predef.BoxType, true, formals)));

          Action<string, Bpl.Type, Bpl.Expr> sink_function = (nm, res_ty, body) =>
            sink.TopLevelDeclarations.Add(
              new Bpl.Function(f.tok, nm, new List<TypeVariable>(), formals,
                BplFormalVar(null, res_ty, false), null,
                new QKeyValue(f.tok, "inline", new List<object> { Bpl.Expr.True }, null)) {
                  Body = body
                });

          sink_function(f.FullSanitizedName, TrType(f.ResultType), FunctionCall(f.tok, fname, Bpl.Type.Bool, rhsargs));
          sink_function(f.FullSanitizedName + "#canCall", Bpl.Type.Bool, Bpl.Expr.True);
        };

        UserSelectorFunction(Requires(ad.Arity), ad.Requires);
        UserSelectorFunction(Reads(ad.Arity), ad.Reads);

        // frame axiom
        /*

          forall t0..tN+1 : Ty, h0, h1 : Heap, f : Handle, bx1 .. bxN : Box,
            HeapSucc(h0, h1) && GoodHeap(h0) && GoodHeap(h1)
            && Is&IsAllocBox(bxI, tI, h0)              // in h0, not hN
            && Is&IsAlloc(f, Func(t1,..,tN, tN+1), h0) // in h0, not hN
            && 
            (forall o : ref::
                 o != null && h0[o, alloc] && h1[o, alloc] && 
                 Reads(h,hN,bxs)[Box(o)]             // for hN in h0 and h1
              ==> h0[o,field] == h1[o,field])
          ==>  Reads(..h0..) == Reads(..h1..) 
           AND Requires(f,h0,bxs) == Requires(f,h1,bxs) // which is needed for the next
           AND  Apply(f,h0,bxs) == Apply(f,h0,bxs)
        
         */
        {
          var bvars = new List<Bpl.Variable>();

          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));

          var h0 = BplBoundVar("h0", predef.HeapType, bvars);
          var h1 = BplBoundVar("h1", predef.HeapType, bvars);
          var heapSucc = FunctionCall(tok, BuiltinFunction.HeapSucc, null, h0, h1);
          var goodHeaps = BplAnd(
            FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h0),
            FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h1));

          var f = BplBoundVar("f", predef.HandleType, bvars);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var isness = BplAnd(
            Snoc(Map(Enumerable.Range(0, arity), i =>
              BplAnd(MkIs(boxes[i], types[i], true), 
                     MkIsAlloc(boxes[i], types[i], h0, true))),
            BplAnd(MkIs(f, ClassTyCon(ad, types)), 
                   MkIsAlloc(f, ClassTyCon(ad, types), h0))));

          Action<Bpl.Expr, string> AddFrameForFunction = (hN, fname) => {

            // inner forall vars
            var ivars = new List<Bpl.Variable>();
            var o = BplBoundVar("o", predef.RefType, ivars);
            var a = new TypeVariable(tok, "a");
            var fld = BplBoundVar("fld", predef.FieldName(tok, a), ivars);

            var inner_forall = new Bpl.ForallExpr(tok, Singleton(a), ivars, BplImp(
              BplAnd(new List<Expr> {
                Bpl.Expr.Neq(o, predef.Null),
                IsAlloced(tok, h0, o),
                IsAlloced(tok, h1, o),
                new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> {
                  FunctionCall(tok, Reads(ad.Arity), objset_ty, Concat(types, Cons(f, Cons(hN, boxes)))),
                  FunctionCall(tok, BuiltinFunction.Box, null, o)
                })
              }),
              Bpl.Expr.Eq(ReadHeap(tok, h0, o, fld), ReadHeap(tok, h1, o, fld))));

            Func<Bpl.Expr, Bpl.Expr> fn = h => FunctionCall(tok, fname, Bpl.Type.Bool, Concat(types, Cons(f, Cons<Bpl.Expr>(h, boxes))));

            sink.TopLevelDeclarations.Add(new Axiom(tok,
              BplForall(bvars,
                new Bpl.Trigger(tok, true, new List<Bpl.Expr> {heapSucc, fn(h1)}),
                BplImp(
                  BplAnd(BplAnd(BplAnd(heapSucc, goodHeaps), isness), inner_forall),
                  Bpl.Expr.Eq(fn(h0), fn(h1))))));
          };

          AddFrameForFunction(h0, Reads(ad.Arity)); 
          AddFrameForFunction(h1, Reads(ad.Arity));
          AddFrameForFunction(h0, Requires(ad.Arity));
          AddFrameForFunction(h1, Requires(ad.Arity));
          AddFrameForFunction(h0, Apply(ad.Arity));
          AddFrameForFunction(h1, Apply(ad.Arity));
        }

        // consequence axiom
        /*

          forall t0..tN+1 : Ty, h : Heap, f : Handle, bx1 .. bxN : Box,
            GoodHeap(h)
            && Is&IsAllocBox(bxI, tI, h)              
            && Is&IsAlloc(f, Func(t1,..,tN, tN+1), h) 
          ==> Is&IsAllocBox(Apply(f,h0,bxs)))
        
         */
        {
          var bvars = new List<Bpl.Variable>();

          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));

          var h = BplBoundVar("h", predef.HeapType, bvars);
          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);

          var f = BplBoundVar("f", predef.HandleType, bvars);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var isness = BplAnd(
            Snoc(Map(Enumerable.Range(0, arity), i =>
              BplAnd(MkIs(boxes[i], types[i], true), 
                     MkIsAlloc(boxes[i], types[i], h, true))),
            BplAnd(MkIs(f, ClassTyCon(ad, types)), 
                   MkIsAlloc(f, ClassTyCon(ad, types), h))));

          var applied = FunctionCall(tok, Apply(ad.Arity), predef.BoxType, Concat(types, Cons(f, Cons<Bpl.Expr>(h, boxes))));

          var applied_is = BplAnd(MkIs(applied, types[ad.Arity], true), MkIsAlloc(applied, types[ad.Arity], h, true));

          sink.TopLevelDeclarations.Add(new Axiom(tok,
            BplForall(bvars,
              new Bpl.Trigger(tok, true, new List<Bpl.Expr> {applied}),
              BplImp(BplAnd(goodHeap, isness), applied_is))));
        }
      }
    }

    private string AddTyAxioms(TopLevelDecl td) {
      IToken tok = td.tok;
      var ty_repr =
        td is ArrowType.ArrowTypeDecl ? predef.HandleType :
        td is DatatypeDecl ? predef.DatatypeType :
        predef.RefType;
      var arity = td.TypeArgs.Count;
      var inner_name = GetClass(td).TypedIdent.Name;
      string name = "T" + inner_name;
      // Create the type constructor
      {
        Bpl.Variable tyVarOut = BplFormalVar(null, predef.Ty, false);
        List<Bpl.Variable> args = new List<Bpl.Variable>(
          Enumerable.Range(0, arity).Select(i =>
            (Bpl.Variable)BplFormalVar(null, predef.Ty, true)));
        var func = new Bpl.Function(tok, name, args, tyVarOut);
        sink.TopLevelDeclarations.Add(func);
      }

      // Helper action to create variables and the function call.
      Action<Action<List<Bpl.Expr>, List<Bpl.Variable>, Bpl.Expr>> Helper = K => {
        List<Bpl.Expr> argExprs;
        var args = MkTyParamBinders(td.TypeArgs, out argExprs);
        var inner = FunctionCall(tok, name, predef.Ty, argExprs);
        K(argExprs, args, inner);
      };

      // Create the Tag and calling Tag on this type constructor
      /* 
         const unique TagList: TyTag;
         axiom (forall t0: Ty :: { List(t0) } Tag(List(t0)) == TagList);
      */
      Helper((argExprs, args, inner) => {
        Bpl.TypedIdent tag_id = new Bpl.TypedIdent(tok, "Tag" + inner_name, predef.TyTag);
        Bpl.Constant tag = new Bpl.Constant(tok, tag_id, true);
        Bpl.Expr tag_expr = new Bpl.IdentifierExpr(tok, tag);
        Bpl.Expr tag_call = FunctionCall(tok, "Tag", predef.TyTag, inner);
        Bpl.Expr qq = BplForall(args, BplTrigger(inner), Bpl.Expr.Eq(tag_call, tag_expr));
        sink.TopLevelDeclarations.Add(new Axiom(tok, qq, name + " Tag"));
        sink.TopLevelDeclarations.Add(tag);
      });

      // Create the injectivity axiom and its function
      /* 
         function List_0(Ty) : Ty;
         axiom (forall t0: Ty :: { List(t0) } List_0(List(t0)) == t0);
      */
      for (int i = 0; i < arity; i++) {
        Helper((argExprs, args, inner) => {
          Bpl.Variable tyVarIn = BplFormalVar(null, predef.Ty, true);
          Bpl.Variable tyVarOut = BplFormalVar(null, predef.Ty, false);
          var injname = name + "_" + i;
          var injfunc = new Bpl.Function(tok, injname, Singleton(tyVarIn), tyVarOut);
          var outer = FunctionCall(tok, injname, args[i].TypedIdent.Type, inner);
          Bpl.Expr qq = BplForall(args, BplTrigger(inner), Bpl.Expr.Eq(outer, argExprs[i]));
          sink.TopLevelDeclarations.Add(new Axiom(tok, qq, name + " injectivity " + i));
          sink.TopLevelDeclarations.Add(injfunc);
        });
      }

      // Boxing axiom (important for the properties of unbox)
      /*
         axiom (forall T: Ty, bx: Box :: 
           { $IsBox(bx, List(T)) } 
           $IsBox(bx, List(T))
              ==> $Box($Unbox(bx): DatatypeType) == bx
               && $Is($Unbox(bx): DatatypeType, List(T)));
      */
      Helper((argExprs, args, _inner) => {
        Bpl.Expr bx; var bxVar = BplBoundVar("bx", predef.BoxType, out bx);
        var ty = FunctionCall(tok, name, predef.Ty, argExprs);
        var unbox = FunctionCall(tok, BuiltinFunction.Unbox, ty_repr, bx);
        var box_is = MkIs(bx, ty, true);
        var unbox_is = MkIs(unbox, ty, false);
        var box_unbox = FunctionCall(tok, BuiltinFunction.Box, null, unbox);
        sink.TopLevelDeclarations.Add(
          new Axiom(tok,
            BplForall(Snoc(args, bxVar), BplTrigger(box_is),
              BplImp(box_is, BplAnd(Bpl.Expr.Eq(box_unbox, bx), unbox_is))),
            "Box/unbox axiom for " + name));
      });

      return name;
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
        cc = new Bpl.Constant(cl.tok, new Bpl.TypedIdent(cl.tok, "class." + cl.FullSanitizedName, predef.ClassNameType), !cl.Module.IsFacade);
        classes.Add(cl, cc);
      }
      return cc;
    }

    Bpl.Constant GetFieldNameFamily(string n) {
      Contract.Requires(n != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);
      Bpl.Constant cc;
      if (fieldConstants.TryGetValue(n, out cc)) {
        Contract.Assert(cc != null);
      } else {
        cc = new Bpl.Constant(Token.NoToken, new Bpl.TypedIdent(Token.NoToken, "field$" + n, predef.NameFamilyType), true);
        fieldConstants.Add(n, cc);
      }
      return cc;
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
        // const f: Field ty;
        Bpl.Type ty = predef.FieldName(f.tok, TrType(f.Type));
        fc = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, f.FullSanitizedName, ty), false);
        fields.Add(f, fc);
        // axiom FDim(f) == 0 && FieldOfDecl(C, name) == f &&
        //       $IsGhostField(f);    // if the field is a ghost field
        // OR:
        //       !$IsGhostField(f);    // if the field is not a ghost field
        Bpl.Expr fdim = Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.FDim, ty, Bpl.Expr.Ident(fc)), Bpl.Expr.Literal(0));
        Bpl.Expr declType = Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.FieldOfDecl, ty, new Bpl.IdentifierExpr(f.tok, GetClass(cce.NonNull(f.EnclosingClass))), new Bpl.IdentifierExpr(f.tok, GetFieldNameFamily(f.Name))), Bpl.Expr.Ident(fc));
        Bpl.Expr cond = Bpl.Expr.And(fdim, declType);
        var ig = FunctionCall(f.tok, BuiltinFunction.IsGhostField, ty, Bpl.Expr.Ident(fc));
        cond = Bpl.Expr.And(cond, f.IsGhost ? ig : Bpl.Expr.Not(ig));
        Bpl.Axiom ax = new Bpl.Axiom(f.tok, cond);
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
        } else if (f.EnclosingClass == null && f.Name == "Trunc") { // link directly to the function in the prelude.
          fieldFunctions.Add(f, predef.RealTrunc);
          return predef.RealTrunc;
        }
        // function f(Ref): ty;
        Bpl.Type ty = TrType(f.Type);
        List<Variable> args = new List<Variable>();
        Bpl.Type receiverType = f.EnclosingClass is ClassDecl ? predef.RefType : predef.DatatypeType;
        args.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, receiverType), true));
        Bpl.Formal result = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, ty), false);
        ff = new Bpl.Function(f.tok, f.FullSanitizedName, args, result);

        if (InsertChecksums) {
          var dt = f.EnclosingClass as DatatypeDecl;
          if (dt != null) {
            InsertChecksum(dt, ff);
          }
          // TODO(wuestholz): Do we need to handle more cases?
        }

        fieldFunctions.Add(f, ff);
        // treat certain fields specially
        if (f.EnclosingClass is ArrayClassDecl) {
          // add non-negative-range axioms for array Length fields
          // axiom (forall o: Ref :: 0 <= array.Length(o));
          Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "o", predef.RefType));
          Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(f.tok, oVar);
          Bpl.Expr body = Bpl.Expr.Le(Bpl.Expr.Literal(0), new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o }));
          Bpl.Expr qq = new Bpl.ForallExpr(f.tok, new List<Variable> { oVar }, body);
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(f.tok, qq));
        }
      }
      return ff;
    }

    Bpl.Expr GetField(MemberSelectExpr fse)
    {
      Contract.Requires(fse != null);
      Contract.Requires(fse.Member != null && fse.Member is Field && ((Field)(fse.Member)).IsMutable);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return new Bpl.IdentifierExpr(fse.tok, GetField((Field)fse.Member));
    }

    /// <summary>
    /// This method is expected to be called just once for each function in the program.
    /// </summary>
    void AddFunction(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(predef != null && sink != null);

      // declare the function
      if (!f.IsBuiltin) {
        var typeParams = TrTypeParamDecls(f.TypeArgs);
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f)));
        if (f.IsRecursive) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType), true));
        }
        formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType), true));
        }
        foreach (var p in f.Formals) {
          formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
        var func = new Bpl.Function(f.tok, f.FullSanitizedName, typeParams, formals, res, "function declaration for " + f.FullName);
        if (InsertChecksums) {
          InsertChecksum(f, func);
        }
        sink.TopLevelDeclarations.Add(func);
      }

      // declare the corresponding canCall function
      {
        var typeParams = TrTypeParamDecls(GetTypeParams(f));
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f)));
        formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType), true));
        }
        foreach (var p in f.Formals) {
          formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
        var canCallF = new Bpl.Function(f.tok, f.FullSanitizedName + "#canCall", typeParams, formals, res);
        sink.TopLevelDeclarations.Add(canCallF);
      }
    }

    /// <summary>
    /// A method can have several translations, suitable for different purposes.
    /// SpecWellformedness
    ///    This procedure is suitable for the wellformedness check of the
    ///    method's specification.
    ///    This means the pre- and postconditions are not filled in, since the
    ///    body of the procedure is going to check that these are well-formed in
    ///    the first place.
    /// InterModuleCall
    ///    This procedure is suitable for inter-module callers.
    ///    This means that predicate definitions are not inlined.
    /// IntraModuleCall
    ///    This procedure is suitable for non-co-call intra-module callers.
    ///    This means that predicates can be inlined in the usual way.
    /// CoCall
    ///    This procedure is suitable for (intra-module) co-calls.
    ///    In these calls, some uses of copredicates may be replaced by
    ///    proof certificates.  Note, unless the method is a colemma, there
    ///    is no reason to include a procedure for co-calls.
    /// Implementation
    ///    This procedure is suitable for checking the implementation of the
    ///    method.
    ///    If the method has no body, there is no reason to include this kind
    ///    of procedure.
    ///
    /// Note that SpecWellformedness and Implementation have procedure implementations
    /// but no callers, and vice versa for InterModuleCall, IntraModuleCall, and CoCall.
    /// </summary>
    enum MethodTranslationKind { SpecWellformedness, InterModuleCall, IntraModuleCall, CoCall, Implementation, OverrideCheck }

    /// <summary>
    /// This method is expected to be called at most once for each parameter combination, and in particular
    /// at most once for each value of "kind".
    /// </summary>    
    Bpl.Procedure AddMethod(Method m, MethodTranslationKind kind)
    {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(predef != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);

      currentModule = m.EnclosingClass.Module;
      codeContext = m;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);

      List<Variable> inParams, outParams;
      GenerateMethodParameters(m.tok, m, kind, etran, out inParams, out outParams);

      var req = new List<Bpl.Requires>();    
      var mod = new List<Bpl.IdentifierExpr>();
      var ens = new List<Bpl.Ensures>();
      // FREE PRECONDITIONS
      if (kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation || kind== MethodTranslationKind.OverrideCheck) {  // the other cases have no need for a free precondition
        // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
        req.Add(Requires(m.tok, true, etran.HeightContext(m), null, null));
      }
      mod.Add((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr);
      mod.Add(etran.Tick());

      var bodyKind = kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation;

      if (kind != MethodTranslationKind.SpecWellformedness && kind != MethodTranslationKind.OverrideCheck)
      {
        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined preconditions";
        foreach (var p in m.Req) {
          if (p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
            req.Add(Requires(p.E.tok, true, etran.TrExpr(p.E), null, comment));
            comment = null;
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, kind == MethodTranslationKind.InterModuleCall ? 0 : int.MaxValue, true /* kind == MethodTranslationKind.Implementation */, out splitHappened)) {
              if ((kind == MethodTranslationKind.IntraModuleCall || kind == MethodTranslationKind.CoCall) && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this precondition was inherited into this module, so just ignore it
              } else if (s.IsOnlyChecked && bodyKind) {
                // don't include in split
              } else if (s.IsOnlyFree && !bodyKind) {
                // don't include in split -- it would be ignored, anyhow
              } else {
                req.Add(Requires(s.E.tok, s.IsOnlyFree, s.E, null, comment));
                comment = null;
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }
        comment = "user-defined postconditions";
        foreach (var p in m.Ens) {
          ens.Add(Ensures(p.E.tok, true, CanCallAssumption(p.E, etran), null, comment));
          comment = null;
          if (p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
            ens.Add(Ensures(p.E.tok, true, etran.TrExpr(p.E), null, null));
          } else {
            bool splitHappened;  // we actually don't care
            foreach (var s in TrSplitExpr(p.E, etran, kind == MethodTranslationKind.InterModuleCall ? 0 : int.MaxValue, true /* kind == MethodTranslationKind.Implementation */ , out splitHappened)) {
              var post = s.E;
              if (kind == MethodTranslationKind.Implementation && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this postcondition was inherited into this module, so make it into the form "$_reverifyPost ==> s.E"
                post = Bpl.Expr.Imp(new Bpl.IdentifierExpr(s.E.tok, "$_reverifyPost", Bpl.Type.Bool), post);
              }
              if (s.IsOnlyFree && bodyKind) {
                // don't include in split -- it would be ignored, anyhow
              } else if (s.IsOnlyChecked && !bodyKind) {
                // don't include in split
              } else {
                ens.Add(Ensures(s.E.tok, s.IsOnlyFree, post, null, null));
              }
            }
          }
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, etran.Old, etran, etran.Old)) {
          ens.Add(Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
        }
      }

      var typeParams = TrTypeParamDecls(GetTypeParams(m));
      var name = MethodName(m, kind);
      var proc = new Bpl.Procedure(m.tok, name, typeParams, inParams, outParams, req, mod, ens, etran.TrAttributes(m.Attributes, null));

      if (InsertChecksums)
      {
        InsertChecksum(m, proc, true);
      }

      currentModule = null;
      codeContext = null;

      return proc;
    }

    static string MethodName(ICodeContext m, MethodTranslationKind kind) {
      Contract.Requires(m != null);
      switch (kind) {
        case MethodTranslationKind.SpecWellformedness:
          return "CheckWellformed$$" + m.FullSanitizedName;
        case MethodTranslationKind.InterModuleCall:
          return "InterModuleCall$$" + m.FullSanitizedName;
        case MethodTranslationKind.IntraModuleCall:
          return "IntraModuleCall$$" + m.FullSanitizedName;
        case MethodTranslationKind.CoCall:
          return "CoCall$$" + m.FullSanitizedName;
        case MethodTranslationKind.Implementation:
          return "Impl$$" + m.FullSanitizedName;
        case MethodTranslationKind.OverrideCheck:
          return "OverrideCheck$$" + m.FullSanitizedName;
        default:
          Contract.Assert(false);  // unexpected kind
          throw new cce.UnreachableException();
      }
    }

    private void AddMethodRefinementCheck(MethodCheck methodCheck) {
      Contract.Requires(methodCheck != null);
      Contract.Requires(methodCheck.Refined != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);

      // First, we generate the declaration of the procedure. This procedure has the same
      // pre and post conditions as the refined method. The body implementation will be a call
      // to the refining method.
      Method m = methodCheck.Refined;
      currentModule = m.EnclosingClass.Module;
      codeContext = m;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, m.tok);

      List<Variable> inParams, outParams;
      GenerateMethodParameters(m.tok, m, MethodTranslationKind.Implementation, etran, out inParams, out outParams);

      var req = new List<Bpl.Requires>();
      List<Bpl.IdentifierExpr> mod = new List<Bpl.IdentifierExpr>();
      var ens = new List<Bpl.Ensures>();

      req.Add(Requires(m.tok, true, etran.HeightContext(m), null, null));

      mod.Add((Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr);
      mod.Add(etran.Tick());

      foreach (MaybeFreeExpression p in m.Req) {
        if ((p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating)) {
          req.Add(Requires(p.E.tok, true, etran.TrExpr(p.E), null, null));
        } else {
          bool splitHappened;  // we actually don't care
          foreach (var s in TrSplitExpr(p.E, etran, true, out splitHappened)) {
            req.Add(Requires(s.E.tok, s.IsOnlyFree, s.E, null, null));
          }
        }
      }
      foreach (MaybeFreeExpression p in m.Ens) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(p.E, etran, true, out splitHappened)) {
          ens.Add(Ensures(s.E.tok, s.IsOnlyFree, s.E, "Error: postcondition of refined method may be violated", null));
        }
      }
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, etran.Old, etran, etran.Old)) {
        ens.Add(Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
      }

      // Generate procedure, and then add it to the sink
      List<TypeVariable> typeParams = TrTypeParamDecls(m.TypeArgs);
      string name = "CheckRefinement$$" + m.FullSanitizedName + "$" + methodCheck.Refining.FullSanitizedName;
      var proc = new Bpl.Procedure(m.tok, name, typeParams, inParams, outParams, req, mod, new List<Bpl.Ensures>(), etran.TrAttributes(m.Attributes, null));

      sink.TopLevelDeclarations.Add(proc);


      // Generate the implementation
      typeParams = TrTypeParamDecls(m.TypeArgs);
      inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

      var builder = new Bpl.StmtListBuilder();
      var localVariables = new List<Variable>();
      GenerateImplPrelude(m, true, inParams, outParams, builder, localVariables);

      // Generate the call to the refining method
      Method method = methodCheck.Refining;
      Expression receiver = new ThisExpr(Token.NoToken);
      var ins = new List<Bpl.Expr>();
      if (!method.IsStatic) {
        ins.Add(etran.TrExpr(receiver));
      }

      // Ideally, the modifies and decreases checks would be done after the precondition check,
      // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
      // store the actual parameters.
      // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
      var substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < method.Ins.Count; i++) {
        var p = method.Ins[i];
        var local = new LocalVariable(p.tok, p.tok, p.Name + "#", p.Type, p.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(methodCheck.Refining));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(p, ie);
        localVariables.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(methodCheck.Refining), TrType(local.Type))));

        var param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
        var bActual = new Bpl.IdentifierExpr(Token.NoToken, m.Ins[i].AssignUniqueName(methodCheck.Refining), TrType(m.Ins[i].Type));
        var cmd = Bpl.Cmd.SimpleAssign(p.tok, param, CondApplyUnbox(Token.NoToken, bActual, cce.NonNull( m.Ins[i].Type),p.Type));
        builder.Add(cmd);
        ins.Add(param);
      }

      // Check modifies clause of a subcall is a subset of the current frame.
      CheckFrameSubset(method.tok, method.Mod.Expressions, receiver, substMap, etran, builder, "call may modify locations not in the refined method's modifies clause", null);

      // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
      var outs = new List<Bpl.IdentifierExpr>();
      var tmpOuts = new List<Bpl.IdentifierExpr>();
      for (int i = 0; i < m.Outs.Count; i++) {
        var bLhs = m.Outs[i];
        if (!ModeledAsBoxType(method.Outs[i].Type) && ModeledAsBoxType(bLhs.Type)) {
          // we need an Box
          Bpl.LocalVariable var = new Bpl.LocalVariable(bLhs.tok, new Bpl.TypedIdent(bLhs.tok, "$tmp##" + otherTmpVarCount, TrType(method.Outs[i].Type)));
          otherTmpVarCount++;
          localVariables.Add(var);
          Bpl.IdentifierExpr varIdE = new Bpl.IdentifierExpr(bLhs.tok, var.Name, TrType(method.Outs[i].Type));
          tmpOuts.Add(varIdE);
          outs.Add(varIdE);
        } else {
          tmpOuts.Add(null);
          outs.Add(new Bpl.IdentifierExpr(Token.NoToken, bLhs.AssignUniqueName(methodCheck.Refining), TrType(bLhs.Type)));
        }
      }

      // Make the call
      builder.Add(new Bpl.CallCmd(method.tok, method.FullSanitizedName, ins, outs));

      for (int i = 0; i < m.Outs.Count; i++) {
        var bLhs = m.Outs[i];
        var tmpVarIdE = tmpOuts[i];
        if (tmpVarIdE != null) {
          // e := Box(tmpVar);
          Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(Token.NoToken, new Bpl.IdentifierExpr(Token.NoToken, bLhs.AssignUniqueName(methodCheck.Refining), TrType(bLhs.Type)), FunctionCall(Token.NoToken, BuiltinFunction.Box, null, tmpVarIdE));
          builder.Add(cmd);
        }
      }

      foreach (var p in m.Ens) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(p.E, etran, true, out splitHappened)) {
          var assert = new Bpl.AssertCmd(method.tok, s.E, ErrorMessageAttribute(s.E.tok, "This is the postcondition that may not hold."));
          assert.ErrorData = "Error: A postcondition of the refined method may not hold.";
          builder.Add(assert);
        }
      }
      var stmts = builder.Collect(method.tok); // this token is for the implict return, which should be for the refining method,
                                               // as this is where the error is.

      var impl = new Bpl.Implementation(m.tok, proc.Name,
        typeParams, inParams, outParams,
        localVariables, stmts, etran.TrAttributes(m.Attributes, null));
      sink.TopLevelDeclarations.Add(impl);

      // Clean up
      currentModule = null;
      codeContext = null;
      otherTmpVarCount = 0;
      _tmpIEs.Clear();
    }

    private static QKeyValue ErrorMessageAttribute(IToken t, string error) {
      var l = new List<object>(1);
      l.Add(error);
      return new QKeyValue(t, "msg", l, null);
    }
    private static QKeyValue ErrorMessageAttribute(IToken t, string error, QKeyValue qv) {
      var l = new List<object>(1);
      l.Add(error);
      return new QKeyValue(t, "msg", l, qv);
    }

    private void AddFunctionRefinementCheck(FunctionCheck functionCheck) {
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null);
      Contract.Ensures(currentModule == null);

      Function f = functionCheck.Refined;
      Function function = functionCheck.Refining;
      currentModule = function.EnclosingClass.Module;

      ExpressionTranslator etran = new ExpressionTranslator(this, predef, f.tok);
      // parameters of the procedure
      List<Variable> inParams = new List<Variable>();
      Bpl.Formal layer;
      if (f.IsRecursive) {
        layer = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType), true);
        inParams.Add(layer);
      } else {
        layer = null;
      }
      if (!f.IsStatic) {
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), predef.Null),
          etran.GoodRef(f.tok, new Bpl.IdentifierExpr(f.tok, "this", predef.RefType), Resolver.GetReceiverType(f.tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", predef.RefType, wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in f.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(functionCheck.Refining), varType), p.Type, etran);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(functionCheck.Refining), varType, wh), true));
      }
      List<TypeVariable> typeParams = TrTypeParamDecls(GetTypeParams(f));
      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      req.Add(Requires(f.tok, true, etran.HeightContext(function), null, null));

      foreach (Expression p in f.Req) {
        req.Add(Requires(p.tok, true, etran.TrExpr(p), null, null));
      }

      // check that postconditions hold
      var ens = new List<Bpl.Ensures>();
      foreach (Expression p in f.Ens) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(p, etran, true, out splitHappened)) {
          if (s.IsChecked) {
            ens.Add(Ensures(s.E.tok, false, s.E, null, null));
          }
        }
      }
      Bpl.Procedure proc = new Bpl.Procedure(function.tok, "CheckIsRefinement$$" + f.FullSanitizedName + "$" + functionCheck.Refining.FullSanitizedName, typeParams, inParams, new List<Variable>(),
        req, new List<Bpl.IdentifierExpr>(), ens, etran.TrAttributes(function.Attributes, null));
      sink.TopLevelDeclarations.Add(proc);

      List<Variable> implInParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      List<Variable> locals = new List<Variable>();
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();

      Bpl.FunctionCall funcOriginal = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
      Bpl.FunctionCall funcRefining = new Bpl.FunctionCall(new Bpl.IdentifierExpr(functionCheck.Refining.tok, functionCheck.Refining.FullSanitizedName, TrType(f.ResultType)));
      List<Bpl.Expr> args = new List<Bpl.Expr>();
      List<Bpl.Expr> argsCanCall = new List<Bpl.Expr>();
      if (layer != null) {
        args.Add(new Bpl.IdentifierExpr(f.tok, implInParams[0]));
        // don't add layer parameter to canCall's arguments
      }
      args.Add(etran.HeapExpr);
      argsCanCall.Add(etran.HeapExpr);
      for (int i = layer == null ? 0 : 1; i < implInParams.Count; i++) {
        args.Add(new Bpl.IdentifierExpr(f.tok, implInParams[i]));
        argsCanCall.Add(new Bpl.IdentifierExpr(f.tok, implInParams[i]));
      }
      Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, funcOriginal, args);
      Bpl.Expr funcAppl2 = new Bpl.NAryExpr(f.tok, funcRefining, args);

      Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < function.Formals.Count; i++) {
        Formal p = function.Formals[i];
        IdentifierExpr ie = new IdentifierExpr(f.Formals[i].tok, f.Formals[i].AssignUniqueName(functionCheck.Refining));
        ie.Var = f.Formals[i]; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(p, ie);
      }
      // add canCall
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(Token.NoToken, function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr canCall = new Bpl.NAryExpr(Token.NoToken, new Bpl.FunctionCall(canCallFuncID), argsCanCall);
      builder.Add(new AssumeCmd(function.tok, canCall));

      // check that the preconditions for the call hold
      foreach (Expression p in function.Req) {
        Expression precond = Substitute(p, new ThisExpr(Token.NoToken), substMap);
        var assert = new AssertCmd(p.tok, etran.TrExpr(precond));
        assert.ErrorData = "Error: the refining function is not allowed to add preconditions";
        builder.Add(assert);
      }
      builder.Add(new AssumeCmd(f.tok, Bpl.Expr.Eq(funcAppl, funcAppl2)));

      foreach (Expression p in f.Ens) {
        var s = new FunctionCallSubstituter(new ThisExpr(Token.NoToken), substMap, f, function, this);
        Expression precond = s.Substitute(p);
        var assert = new AssertCmd(p.tok, etran.TrExpr(precond));
        assert.ErrorData = "Error: A postcondition of the refined function may not hold";
        builder.Add(assert);
      }
      Bpl.Implementation impl = new Bpl.Implementation(function.tok, proc.Name,
        typeParams, implInParams, new List<Variable>(),
        locals, builder.Collect(function.tok), etran.TrAttributes(function.Attributes, null));
      sink.TopLevelDeclarations.Add(impl);

      Contract.Assert(currentModule == function.EnclosingClass.Module);
      currentModule = null;
    }

    private void GenerateMethodParameters(IToken tok, Method m, MethodTranslationKind kind, ExpressionTranslator etran, out List<Variable> inParams, out List<Variable> outParams) {
      GenerateMethodParametersChoose(tok, m, kind, !m.IsStatic, true, true, etran, out inParams, out outParams);
    }

    private void GenerateMethodParametersChoose(IToken tok, IMethodCodeContext m, MethodTranslationKind kind, bool includeReceiver, bool includeInParams, bool includeOutParams,
      ExpressionTranslator etran, out List<Variable> inParams, out List<Variable> outParams) {
      inParams = new List<Bpl.Variable>();
      outParams = new List<Variable>();      
      // Add type parameters first, always!
      inParams.AddRange(MkTyParamFormals(GetTypeParams(m)));
      if (includeReceiver) {
        var receiverType = m is MemberDecl ? Resolver.GetReceiverType(tok, (MemberDecl)m) : Resolver.GetThisType(tok, (IteratorDecl)m);
        Bpl.Expr wh = Bpl.Expr.And(
          Bpl.Expr.Neq(new Bpl.IdentifierExpr(tok, "this", predef.RefType), predef.Null),
          etran.GoodRef(tok, new Bpl.IdentifierExpr(tok, "this", predef.RefType), receiverType));
        Bpl.Formal thVar = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", predef.RefType, wh), true);
        inParams.Add(thVar);
      }      
      if (includeInParams) {        
        foreach (Formal p in m.Ins) {
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetExtendedWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(currentDeclaration), varType), p.Type, etran);
          inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration), varType, wh), true));
        }
      }
      if (includeOutParams) {
        foreach (Formal p in m.Outs) {
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(currentDeclaration), varType), p.Type, etran);
          outParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration), varType, wh), false));
        }
        if (kind == MethodTranslationKind.Implementation) {
          outParams.Add(new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "$_reverifyPost", Bpl.Type.Bool), false));
        }
      }
    }

    class BoilerplateTriple
    {  // a triple that is now a quintuple
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
    List<BoilerplateTriple/*!*/>/*!*/ GetTwoStateBoilerplate(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ modifiesClause, bool isGhostContext, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
    {
      Contract.Requires(tok != null);
      Contract.Requires(modifiesClause != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(etran != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<BoilerplateTriple>>()));

      var boilerplate = new List<BoilerplateTriple>();
      if (isGhostContext && modifiesClause.Count == 0) {
        // plain and simple:  S1 == S2
        boilerplate.Add(new BoilerplateTriple(tok, true, Bpl.Expr.Eq(etranPre.HeapExpr, etran.HeapExpr), null, "frame condition"));
      } else {
        // the frame condition, which is free since it is checked with every heap update and call
        boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, isGhostContext, etranPre, etran, etranMod), null, "frame condition"));
        // HeapSucc(S1, S2) or HeapSuccGhost(S1, S2)
        Bpl.Expr heapSucc = FunctionCall(tok, isGhostContext ? BuiltinFunction.HeapSuccGhost : BuiltinFunction.HeapSucc, null, etranPre.HeapExpr, etran.HeapExpr);
        boilerplate.Add(new BoilerplateTriple(tok, true, heapSucc, null, "boilerplate"));
      }
      return boilerplate;
    }

    /// <summary>
    /// There are 3 states of interest when generating a frame condition:
    ///  S0. the beginning of the method/loop, which is where the modifies clause is interpreted
    ///  S1. the pre-state of the two-state interval
    ///  S2. the post-state of the two-state interval
    /// This method assumes that etranPre denotes S1, etran denotes S2, and that etranMod denotes S0.
    /// </summary>
    Bpl.Expr/*!*/ FrameCondition(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ modifiesClause, bool isGhostContext, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
    {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(cce.NonNullElements(modifiesClause));
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // generate:
      //  (forall<alpha> o: ref, f: Field alpha :: { $Heap[o,f] }
      //      o != null
      //      && old($Heap)[o,alloc]                     // include only in non-ghost contexts
      //      ==>
      //        $Heap[o,f] == PreHeap[o,f] ||
      //        (o,f) in modifiesClause)
      var alpha = new Bpl.TypeVariable(tok, "alpha");
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);
      var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      var f = new Bpl.IdentifierExpr(tok, fVar);

      Bpl.Expr heapOF = ReadHeap(tok, etran.HeapExpr, o, f);
      Bpl.Expr preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f);
      Bpl.Expr ante = Bpl.Expr.Neq(o, predef.Null);
      if (!isGhostContext) {
        ante = Bpl.Expr.And(ante, etranMod.IsAlloced(tok, o));
      }
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = Bpl.Expr.Or(consequent, InRWClause(tok, o, f, modifiesClause, etranMod, null, null));

      var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, Bpl.Expr.Imp(ante, consequent));
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

      Bpl.Expr heapOF = ReadHeap(tok, etran.HeapExpr, o, f);
      Bpl.Expr preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etranPre.IsAlloced(tok, o));
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = Bpl.Expr.Or(consequent, Bpl.Expr.SelectTok(tok, etranMod.TheFrame(tok), o, f));

      Bpl.Trigger tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, Bpl.Expr.Imp(ante, consequent));
    }
    // ----- Type ---------------------------------------------------------------------------------
    // Translates a type into the representation Boogie type,
    // c.f. TypeToTy which translates a type to its Boogie expression
    // to be used in $Is and $IsAlloc.
    Bpl.Type TrType(Type type)
     {
      Contract.Requires(type != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Type>() != null);

      while (true) {
        type = type.NormalizeExpand();
        if (type is TypeProxy) {
          // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
          return predef.RefType;
        }
        var d = type.AsDerivedType;
        if (d == null) {
          break;
        } else {
          type = d.BaseType;  // the Boogie type to be used for the derived type is the same as for the base type
        }
      }

      if (type is BoolType) {
        return Bpl.Type.Bool;
      } else if (type is IntType) {
        return Bpl.Type.Int;
      } else if (type is RealType) {
        return Bpl.Type.Real;
      } else if (type is IteratorDecl.EverIncreasingType) {
        return Bpl.Type.Int;
      } else if (type is ArrowType) {
        return predef.HandleType;
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

    List<TypeVariable> TrTypeParamDecls(List<TypeParameter/*!*/>/*!*/ tps)
    {
      Contract.Requires(cce.NonNullElements(tps));
      Contract.Ensures(Contract.Result<List<TypeVariable>>() != null);

      List<TypeVariable> typeParams = new List<TypeVariable>();
      return typeParams;
    }

    public Bpl.Expr CondApplyBox(IToken tok, Bpl.Expr e, Type fromType, Type toType) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (!ModeledAsBoxType(fromType) && (toType == null || ModeledAsBoxType(toType))) {
        return FunctionCall(tok, BuiltinFunction.Box, null, e);
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
        return FunctionCall(tok, BuiltinFunction.Unbox, TrType(toType), e);
      } else {
        return e;
      }
    }

    /// <summary>
    ///   If the type is not normally boxed, insert a box around it.
    ///   For lambda functions.
    /// </summary>
    public Bpl.Expr BoxIfUnboxed(Bpl.Expr e, Type t) {
      if (!ModeledAsBoxType(t)) {
        return FunctionCall(e.tok, BuiltinFunction.Box, null, e);
      } else {
        return e;
      }
    }

    /// <summary>
    ///   If the expression is boxed, but the type is not boxed, this unboxes it.
    ///   For lambda functions.
    /// </summary>
    public Bpl.Expr UnboxIfBoxed(Bpl.Expr e, Type t) {
      if (!ModeledAsBoxType(t)) {
        return FunctionCall(e.tok, BuiltinFunction.Unbox, TrType(t), e);
      } else {
        return e;
      }
    }

    public static bool ModeledAsBoxType(Type t) {
      Contract.Requires(t != null);
      t = t.NormalizeExpand();
      if (t is TypeProxy) {
        // unresolved proxy
        return false;
      }
      var res = t.IsTypeParameter;
      Contract.Assert(t is ArrowType ? !res : true);
      return res;
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

    Bpl.PredicateCmd Assert(Bpl.IToken tok, Bpl.Expr condition, string errorMessage) {
      return Assert(tok, condition, errorMessage, tok);
    }

    Bpl.PredicateCmd Assert(Bpl.IToken tok, Bpl.Expr condition, string errorMessage, Bpl.IToken refinesToken, Bpl.QKeyValue kv = null) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Requires(errorMessage != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (assertAsAssume || (RefinementToken.IsInherited(refinesToken, currentModule) && (codeContext == null || !codeContext.MustReverify))) {
        // produce an assume instead
        return new Bpl.AssumeCmd(tok, condition, kv);
      } else {
        var cmd = new Bpl.AssertCmd(ForceCheckToken.Unwrap(tok), condition, kv);
        cmd.ErrorData = "Error: " + errorMessage;
        return cmd;
      }
    }
    Bpl.PredicateCmd AssertNS(Bpl.IToken tok, Bpl.Expr condition, string errorMessage) {
      return AssertNS(tok, condition, errorMessage, tok, null);
    }
    Bpl.PredicateCmd AssertNS(Bpl.IToken tok, Bpl.Expr condition, string errorMessage, Bpl.IToken refinesTok, Bpl.QKeyValue kv)
    {
      Contract.Requires(tok != null);
      Contract.Requires(errorMessage != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (RefinementToken.IsInherited(refinesTok, currentModule) && (codeContext == null || !codeContext.MustReverify)) {
        // produce a "skip" instead
        return new Bpl.AssumeCmd(tok, Bpl.Expr.True, kv);
      } else {
        tok = ForceCheckToken.Unwrap(tok);
        var args = new List<object>();
        args.Add(Bpl.Expr.Literal(0));
        Bpl.AssertCmd cmd = new Bpl.AssertCmd(tok, condition, new Bpl.QKeyValue(tok, "subsumption", args, kv));
        cmd.ErrorData = "Error: " + errorMessage;
        return cmd;
      }
    }

    Bpl.PredicateCmd Assert(Bpl.IToken tok, Bpl.Expr condition, string errorMessage, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(errorMessage != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      if (assertAsAssume || (RefinementToken.IsInherited(tok, currentModule) && (codeContext == null || !codeContext.MustReverify))) {
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

    Bpl.StmtList TrStmt2StmtList(Bpl.StmtListBuilder builder, Statement block, List<Variable> locals, ExpressionTranslator etran)
    {
      Contract.Requires(builder != null);
      Contract.Requires(block != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.StmtList>() != null);

      TrStmt(block, builder, locals, etran);
      return builder.Collect(block.Tok);  // TODO: would be nice to have an end-curly location for "block"
    }

    void TrStmt(Statement stmt, Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
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
          var ss = TrSplitExpr(s.Expr, etran, true, out splitHappened);
          if (!splitHappened) {
            var tok = enclosingToken == null ? s.Expr.tok : new NestedToken(enclosingToken, s.Expr.tok);
            builder.Add(Assert(tok, etran.TrExpr(s.Expr), "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));
          } else {
            foreach (var split in ss) {
              if (split.IsChecked) {
                var tok = enclosingToken == null ? split.E.tok : new NestedToken(enclosingToken, split.E.tok);
                builder.Add(AssertNS(tok, split.E, "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));  // attributes go on every split
              }
            }
            builder.Add(new Bpl.AssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
          }
        } else if (stmt is AssumeStmt) {
          AddComment(builder, stmt, "assume statement");
          AssumeStmt s = (AssumeStmt)stmt;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
          builder.Add(new Bpl.AssumeCmd(stmt.Tok, etran.TrExpr(s.Expr), etran.TrAttributes(stmt.Attributes, null)));
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
        builder.Add(new GotoCmd(s.Tok, new List<String> { "after_" + s.TargetStmt.Labels.Data.UniqueId }));
      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        AddComment(builder, stmt, "return statement");
        if (s.ReverifyPost) {
          // $_reverifyPost := true;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, new Bpl.IdentifierExpr(s.Tok, "$_reverifyPost", Bpl.Type.Bool), Bpl.Expr.True));
        }
        if (s.hiddenUpdate != null) {
          TrStmt(s.hiddenUpdate, builder, locals, etran);
        }
        builder.Add(new Bpl.ReturnCmd(stmt.Tok));
      } else if (stmt is YieldStmt) {
        var s = (YieldStmt)stmt;
        AddComment(builder, s, "yield statement");
        Contract.Assert(codeContext is IteratorDecl);
        var iter = (IteratorDecl)codeContext;
        // if the yield statement has arguments, do them first
        if (s.hiddenUpdate != null) {
          TrStmt(s.hiddenUpdate, builder, locals, etran);
        }
        // this.ys := this.ys + [this.y];
        var th = new ThisExpr(iter.tok);
        th.Type = Resolver.GetThisType(iter.tok, iter);  // resolve here
        Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
        for (int i = 0; i < iter.OutsFields.Count; i++) {
          var y = iter.OutsFields[i];
          var dafnyY = new MemberSelectExpr(s.Tok, th, y.Name);
          dafnyY.Member = y; dafnyY.Type = y.Type;  // resolve here
          var ys = iter.OutsHistoryFields[i];
          var dafnyYs = new MemberSelectExpr(s.Tok, th, ys.Name);
          dafnyYs.Member = ys; dafnyYs.Type = ys.Type;  // resolve here
          var dafnySingletonY = new SeqDisplayExpr(s.Tok, new List<Expression>() { dafnyY });
          dafnySingletonY.Type = ys.Type;  // resolve here
          var rhs = new BinaryExpr(s.Tok, BinaryExpr.Opcode.Add, dafnyYs, dafnySingletonY);
          rhs.ResolvedOp = BinaryExpr.ResolvedOpcode.Concat;
          rhs.Type = ys.Type;  // resolve here
          var cmd = Bpl.Cmd.SimpleAssign(s.Tok, (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr,
            ExpressionTranslator.UpdateHeap(s.Tok, etran.HeapExpr, etran.TrExpr(th), new Bpl.IdentifierExpr(s.Tok, GetField(ys)), etran.TrExpr(rhs)));
          builder.Add(cmd);
        }
        // yieldCount := yieldCount + 1;  assume yieldCount == |ys|;
        var yc = new Bpl.IdentifierExpr(s.Tok, yieldCountVariable);
        var incYieldCount = Bpl.Cmd.SimpleAssign(s.Tok, yc, Bpl.Expr.Binary(s.Tok, Bpl.BinaryOperator.Opcode.Add, yc, Bpl.Expr.Literal(1)));
        builder.Add(incYieldCount);
        builder.Add(new Bpl.AssumeCmd(s.Tok, YieldCountAssumption(iter, etran)));
        // assume $IsGoodHeap($Heap);
        builder.Add(AssumeGoodHeap(s.Tok, etran));
        // assert YieldEnsures[subst];  // where 'subst' replaces "old(E)" with "E" being evaluated in $_OldIterHeap
        var yeEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, new Bpl.IdentifierExpr(s.Tok, "$_OldIterHeap", predef.HeapType));
        foreach (var p in iter.YieldEnsures) {
          if (p.IsFree && !DafnyOptions.O.DisallowSoundnessCheating) {
            // do nothing
          } else {
            bool splitHappened;  // actually, we don't care
            var ss = TrSplitExpr(p.E, yeEtran, true, out splitHappened);
            foreach (var split in ss) {
              if (RefinementToken.IsInherited(split.E.tok, currentModule)) {
                // this postcondition was inherited into this module, so just ignore it
              } else if (split.IsChecked) {
                var yieldToken = new NestedToken(s.Tok, split.E.tok);
                builder.Add(AssertNS(yieldToken, split.E, "possible violation of yield-ensures condition", stmt.Tok, null));
              }
            }
            builder.Add(new Bpl.AssumeCmd(stmt.Tok, yeEtran.TrExpr(p.E)));
          }
        }
        YieldHavoc(iter.tok, iter, builder, etran);
        builder.Add(CaptureState(s));

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

          List<Tuple<List<BoundVar>, Expression>> partialGuesses = GeneratePartialGuesses(bvars, Substitute(s.Expr, null, substMap));
          Bpl.Expr w = Bpl.Expr.False;
          foreach (var tup in partialGuesses) {
            var body = etran.TrExpr(tup.Item2);
            if (tup.Item1.Count != 0) {
              var bvs = new List<Variable>();
              var typeAntecedent = etran.TrBoundVariables(tup.Item1, bvs);
              body = new Bpl.ExistsExpr(s.Tok, bvs, BplAnd(typeAntecedent, body));
            }
            w = BplOr(body, w);
          }
          builder.Add(Assert(s.Tok, w, "cannot establish the existence of LHS values that satisfy the such-that predicate"));
        }
        // End by doing the assume
        builder.Add(new Bpl.AssumeCmd(s.Tok, etran.TrExpr(s.Expr)));
        builder.Add(CaptureState(s));  // just do one capture state--here, at the very end (that is, don't do one before the assume)

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
          builder.Add(CaptureState(s));
        }

      } else if (stmt is AssignStmt) {
        AddComment(builder, stmt, "assignment statement");
        AssignStmt s = (AssignStmt)stmt;
        TrAssignment(stmt, s.Lhs.Resolved, s.Rhs, builder, locals, etran);

      } else if (stmt is CallStmt) {
        AddComment(builder, stmt, "call statement");
        TrCallStmt((CallStmt)stmt, builder, locals, etran, null);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        TrStmtList(s.Body, builder, locals, etran);
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
            if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is Bpl.IfCmd) {
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

      } else if (stmt is ModifyStmt) {
        AddComment(builder, stmt, "modify statement");
        var s = (ModifyStmt)stmt;
        // check that the modifies is a subset
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, "modify statement may violate context's modifies clause", null);
        // cause the change of the heap according to the given frame
        int modifyId = loopHeapVarCount;
        loopHeapVarCount++;
        string modifyFrameName = "#_Frame#" + modifyId;
        var preModifyHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreModifyHeap" + modifyId, predef.HeapType));
        locals.Add(preModifyHeapVar);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, modifyFrameName);
        if (s.Body == null) {
          var preModifyHeap = new Bpl.IdentifierExpr(s.Tok, preModifyHeapVar);
          // preModifyHeap := $Heap;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preModifyHeap, etran.HeapExpr));
          // havoc $Heap;
          builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
          // assume $HeapSucc(preModifyHeap, $Heap);   OR $HeapSuccGhost
          builder.Add(new Bpl.AssumeCmd(s.Tok, FunctionCall(s.Tok, s.IsGhost ? BuiltinFunction.HeapSuccGhost : BuiltinFunction.HeapSucc, null, preModifyHeap, etran.HeapExpr)));
          // assume nothing outside the frame was changed
          var etranPreLoop = new ExpressionTranslator(this, predef, preModifyHeap);
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          builder.Add(new Bpl.AssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
        } else {
          // do the body, but with preModifyHeapVar as the governing frame
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          TrStmt(s.Body, builder, locals, updatedFrameEtran);
        }
        builder.Add(CaptureState(stmt));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        if (s.Kind == ForallStmt.ParBodyKind.Assign) {
          AddComment(builder, stmt, "forall statement (assign)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (AssignStmt)s.S0;
            var definedness = new Bpl.StmtListBuilder();
            var updater = new Bpl.StmtListBuilder();
            TrForallAssign(s, s0, definedness, updater, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, updater.Collect(s.Tok)));
            builder.Add(CaptureState(stmt));
          }

        } else if (s.Kind == ForallStmt.ParBodyKind.Call) {
          AddComment(builder, stmt, "forall statement (call)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            Contract.Assert(LiteralExpr.IsTrue(s.Range));  // follows from the invariant of ForallStmt
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (CallStmt)s.S0;
            var definedness = new Bpl.StmtListBuilder();
            var exporter = new Bpl.StmtListBuilder();
            TrForallStmtCall(s.Tok, s.BoundVars, s.Range, null, s0, definedness, exporter, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
            builder.Add(CaptureState(stmt));
          }

        } else if (s.Kind == ForallStmt.ParBodyKind.Proof) {
          AddComment(builder, stmt, "forall statement (proof)");
          var definedness = new Bpl.StmtListBuilder();
          var exporter = new Bpl.StmtListBuilder();
          TrForallProof(s, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
          builder.Add(CaptureState(stmt));

        } else {
          Contract.Assert(false);  // unexpected kind
        }

      } else if (stmt is CalcStmt) {
        /* Translate into:
        if (*) {
            assert wf(line0);
        } else if (*) {
            assume wf(line0);
            // if op is ==>: assume line0;
            hint0;
            assert wf(line1);
            assert line0 op line1;
            assume false;
        } else if (*) { ...
        } else if (*) {
            assume wf(line<n-1>);
            // if op is ==>: assume line<n-1>;
            hint<n-1>;
            assert wf(line<n>);
            assert line<n-1> op line<n>;
            assume false;
        }
        assume line<0> op line<n>;
        */
        var s = (CalcStmt)stmt;
        Contract.Assert(s.Steps.Count == s.Hints.Count); // established by the resolver
        AddComment(builder, stmt, "calc statement");
        if (s.Lines.Count > 0) {
          Bpl.IfCmd ifCmd = null;
          Bpl.StmtListBuilder b;
          // if the dangling hint is empty, do not generate anything for the dummy step
          var stepCount = s.Hints.Last().Body.Count == 0 ? s.Steps.Count - 1 : s.Steps.Count;
          // check steps:
          for (int i = stepCount; 0 <= --i; ) {
            b = new Bpl.StmtListBuilder();
            // assume wf[line<i>]:
            AddComment(b, stmt, "assume wf[lhs]");
            assertAsAssume = true;
            TrStmt_CheckWellformed(CalcStmt.Lhs(s.Steps[i]), b, locals, etran, false);
            assertAsAssume = false;
            if (s.Steps[i] is BinaryExpr && (((BinaryExpr)s.Steps[i]).ResolvedOp == BinaryExpr.ResolvedOpcode.Imp)) {
              // assume line<i>:
              AddComment(b, stmt, "assume lhs");
              b.Add(new Bpl.AssumeCmd(s.Tok, etran.TrExpr(CalcStmt.Lhs(s.Steps[i]))));
            }
            // hint:
            AddComment(b, stmt, "Hint" + i.ToString());
            TrStmt(s.Hints[i], b, locals, etran);
            if (i < s.Steps.Count - 1) { // non-dummy step
              // check well formedness of the goal line:
              AddComment(b, stmt, "assert wf[rhs]");
              if (s.Steps[i] is TernaryExpr) {
                // check the prefix-equality limit
                var index = ((TernaryExpr) s.Steps[i]).E0;
                b.Add(AssertNS(index.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(index)), "prefix-equality limit must be at least 0"));
              }
              TrStmt_CheckWellformed(CalcStmt.Rhs(s.Steps[i]), b, locals, etran, false);
              bool splitHappened;
              var ss = TrSplitExpr(s.Steps[i], etran, true, out splitHappened);
              // assert step:
              AddComment(b, stmt, "assert line" + i.ToString() + " " + s.StepOps[i].ToString() + " line" + (i + 1).ToString());
              if (!splitHappened) {
                b.Add(AssertNS(s.Lines[i + 1].tok, etran.TrExpr(s.Steps[i]), "the calculation step between the previous line and this line might not hold"));
              } else {
                foreach (var split in ss) {
                  if (split.IsChecked) {
                    b.Add(AssertNS(s.Lines[i + 1].tok, split.E, "the calculation step between the previous line and this line might not hold"));
                  }
                }
              }
            }
            b.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));
            ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
          }
          // check well formedness of the first line:
          b = new Bpl.StmtListBuilder();
          AddComment(b, stmt, "assert wf[initial]");
          Contract.Assert(s.Result != null); // established by the resolver
          TrStmt_CheckWellformed(CalcStmt.Lhs(s.Result), b, locals, etran, false);
          b.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));
          ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
          builder.Add(ifCmd);
          // assume result:
          if (s.Steps.Count > 1) {
            builder.Add(new Bpl.AssumeCmd(s.Tok, etran.TrExpr(s.Result)));
          }
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
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(s.Tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0)
          {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
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
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(mc, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0)
          {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(mc.tok, havocIds));
          }

          // translate the body into b
          TrStmtList(mc.Body, b, locals, etran);

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(mc.tok, guard, b.Collect(mc.tok), ifCmd, els);
          els = null;
        }
        Contract.Assert(ifCmd != null);  // follows from the fact that s.Cases.Count + s.MissingCases.Count != 0.
        builder.Add(ifCmd);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        foreach (var local in s.Locals) {
          Bpl.Type varType = TrType(local.Type);
          Bpl.Expr wh = GetWhereClause(local.Tok, new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration), varType), local.Type, etran);
          Bpl.LocalVariable var = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration), varType, wh));
          var.Attributes = etran.TrAttributes(local.Attributes, null); ;
          locals.Add(var);
          if (Attributes.Contains(local.Attributes, "assumption"))
          {
            builder.Add(new AssumeCmd(local.Tok, new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration), varType), new QKeyValue(local.Tok, "assumption_variable_initialization", new List<object>(), null)));
          }
        }
        if (s.Update != null) {
          TrStmt(s.Update, builder, locals, etran);
        }

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    void TrStmtList(List<Statement> stmts, Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmts != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      foreach (Statement ss in stmts) {
        TrStmt(ss, builder, locals, etran);
        if (ss.Labels != null) {
          builder.AddLabelCmd("after_" + ss.Labels.Data.UniqueId);
        }
      }
    }

    /// <summary>
    /// Generate:
    ///   havoc Heap \ {this} \ _reads \ _new;
    ///   assume this.Valid();
    ///   assume YieldRequires;
    ///   $_OldIterHeap := Heap;
    /// </summary>
    void YieldHavoc(IToken tok, IteratorDecl iter, StmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      // havoc Heap \ {this} \ _reads \ _new;
      var th = new ThisExpr(tok);
      th.Type = Resolver.GetThisType(tok, iter);  // resolve here
      var rds = new MemberSelectExpr(tok, th, iter.Member_Reads.Name);
      rds.Member = iter.Member_Reads;  // resolve here
      rds.Type = iter.Member_Reads.Type;  // resolve here
      var nw = new MemberSelectExpr(tok, th, iter.Member_New.Name);
      nw.Member = iter.Member_New;  // resolve here
      nw.Type = iter.Member_New.Type;  // resolve here
      builder.Add(new Bpl.CallCmd(tok, "$YieldHavoc",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(nw) },
        new List<Bpl.IdentifierExpr>()));
      // assume YieldRequires;
      foreach (var p in iter.YieldRequires) {
        builder.Add(new Bpl.AssumeCmd(tok, etran.TrExpr(p.E)));
      }
      // $_OldIterHeap := Heap;
      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, "$_OldIterHeap", predef.HeapType), etran.HeapExpr));
    }

    List<Tuple<List<BoundVar>, Expression>> GeneratePartialGuesses(List<BoundVar> bvars, Expression expression) {
      if (bvars.Count == 0) {
        var tup = new Tuple<List<BoundVar>, Expression>(new List<BoundVar>(), expression);
        return new List<Tuple<List<BoundVar>, Expression>>() { tup };
      }
      var result = new List<Tuple<List<BoundVar>, Expression>>();
      var x = bvars[0];
      var otherBvars = bvars.GetRange(1, bvars.Count - 1);
      foreach (var tup in GeneratePartialGuesses(otherBvars, expression)) {
        // in the special case that x does not even occur in expression, we can just ignore x
        if (!ContainsFreeVariable(tup.Item2, false, x)) {
          result.Add(tup);
          continue;
        }
        // one possible result is to quantify over all the variables
        var vs = new List<BoundVar>() { x };
        vs.AddRange(tup.Item1);
        result.Add(new Tuple<List<BoundVar>, Expression>(vs, tup.Item2));
        // other possibilities involve guessing a value for x
        foreach (var guess in GuessWitnesses(x, tup.Item2)) {
          var substMap = new Dictionary<IVariable, Expression>();
          substMap.Add(x, guess);
          var g = Substitute(tup.Item2, null, substMap);
          var subrange = SubrangeConstraint(x.tok, guess, x.Type);
          if (subrange != null) {
            g = Expression.CreateAnd(subrange, g);
          }
          result.Add(new Tuple<List<BoundVar>, Expression>(tup.Item1, g));
        }
      }
      return result;
    }

    IEnumerable<Expression> GuessWitnesses(BoundVar x, Expression expr) {
      Contract.Requires(x != null);
      Contract.Requires(expr != null);
      var xType = x.Type.NormalizeExpand();
      if (xType is BoolType) {
        var lit = new LiteralExpr(x.tok, false);
        lit.Type = Type.Bool;  // resolve here
        yield return lit;
        lit = new LiteralExpr(x.tok, true);
        lit.Type = Type.Bool;  // resolve here
        yield return lit;
        yield break;  // there are no more possible witnesses for booleans
      } else if (xType.IsRefType) {
        var lit = new LiteralExpr(x.tok);  // null
        lit.Type = xType;
        yield return lit;
      } else if (xType.IsDatatype) {
        var dt = xType.AsDatatype;
        Expression zero = Zero(x.tok, xType);
        if (zero != null) {
          yield return zero;
        }
        foreach (var ctor in dt.Ctors) {
          if (ctor.Formals.Count == 0) {
            var v = new DatatypeValue(x.tok, dt.Name, ctor.Name, new List<Expression>());
            v.Ctor = ctor;  // resolve here
            v.InferredTypeArgs = xType.TypeArgs; // resolved here.
            v.Type = new UserDefinedType(x.tok, dt.Name, dt, new List<Type>());  // resolve here
            yield return v;
          }
        }
      } else if (xType is SetType) {
        var empty = new SetDisplayExpr(x.tok, new List<Expression>());
        empty.Type = xType;
        yield return empty;
      } else if (xType is MultiSetType) {
        var empty = new MultiSetDisplayExpr(x.tok, new List<Expression>());
        empty.Type = xType;
        yield return empty;
      } else if (xType is SeqType) {
        var empty = new SeqDisplayExpr(x.tok, new List<Expression>());
        empty.Type = xType;
        yield return empty;
      } else if (xType.IsNumericBased(Type.NumericPersuation.Int)) {
        var lit = new LiteralExpr(x.tok, 0);
        lit.Type = xType;  // resolve here
        yield return lit;
      } else if (xType.IsNumericBased(Type.NumericPersuation.Real)) {
        var lit = new LiteralExpr(x.tok, Basetypes.BigDec.ZERO);
        lit.Type = xType;  // resolve here
        yield return lit;
      }

      var missingBounds = new List<BoundVar>();
      var bounds = Resolver.DiscoverBounds(x.tok, new List<BoundVar>() { x }, expr, true, true, missingBounds);
      if (missingBounds.Count == 0) {
        foreach (var bound in bounds) {
          if (bound is ComprehensionExpr.IntBoundedPool) {
            var bnd = (ComprehensionExpr.IntBoundedPool)bound;
            if (bnd.LowerBound != null) yield return bnd.LowerBound;
            if (bnd.UpperBound != null) yield return Expression.CreateDecrement(bnd.UpperBound, 1);
          } else if (bound is ComprehensionExpr.SubSetBoundedPool) {
            var bnd = (ComprehensionExpr.SubSetBoundedPool)bound;
            yield return bnd.UpperBound;
          } else if (bound is ComprehensionExpr.SuperSetBoundedPool) {
            var bnd = (ComprehensionExpr.SuperSetBoundedPool)bound;
            yield return bnd.LowerBound;
          } else if (bound is ComprehensionExpr.SetBoundedPool) {
            var st = ((ComprehensionExpr.SetBoundedPool)bound).Set.Resolved;
            if (st is DisplayExpression) {
              var display = (DisplayExpression)st;
              foreach (var el in display.Elements) {
                yield return el;
              }
            } else if (st is MapDisplayExpr) {
              var display = (MapDisplayExpr)st;
              foreach (var maplet in display.Elements) {
                yield return maplet.A;
              }
            }
          } else if (bound is ComprehensionExpr.SeqBoundedPool) {
            var sq = ((ComprehensionExpr.SeqBoundedPool)bound).Seq.Resolved;
            var display = sq as DisplayExpression;
            if (display != null) {
              foreach (var el in display.Elements) {
                yield return el;
              }
            }
          }
        }
      }
    }

    /// <summary>
    /// Return a zero-equivalent value for "typ", or return null (for any reason whatsoever).
    /// </summary>
    Expression Zero(Bpl.IToken tok, Type typ) {
      Contract.Requires(tok != null);
      Contract.Requires(typ != null);
      return null;  // TODO: this can be improved
    }

    void TrForallAssign(ForallStmt s, AssignStmt s0,
      Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder updater, List<Variable> locals, ExpressionTranslator etran) {
      // The statement:
      //   forall (x,y | Range(x,y)) {
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
      //         { $Heap[o,F] }
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == E(x,y) && F = f));
      //       assume (forall x,y ::  Range ==> $Heap[ E[$Heap:=oldHeap], F] == G[$Heap:=oldHeap]); (**)
      //     (b)
      //       assume (forall<alpha> o: ref, F: Field alpha ::
      //         { $Heap[o,F] }
      //         $Heap[o,F] = oldHeap[o,F] ||
      //         (exists x,y :: Range(x,y) && o == A(x,y) && F = Index(I0,I1,...)));
      //       assume (forall x,y ::  Range ==> $Heap[ A[$Heap:=oldHeap], Index(I0,I1,...)] == G[$Heap:=oldHeap]); (**)
      //   }
      //
      // Note: In order to get a good trigger for the quantifiers (**), we will attempt to make the parameters
      // that select from $Heap in the LHS of the equalities as plain as possible.  This involves taking the inverse
      // of an expression, which isn't always easy or possible, so we settle for handling some common cases.  In
      // particular, we change:
      //   0: forall i | R(i) { F(i).f := E(i); }
      //   1: forall i | R(i) { A[F(i)] := E(i); }
      //   2: forall i | R(i) { F(i)[N] := E(i); }
      // where f is some field and A and N are expressions that do not depend on i, into:
      //   0: forall j | Q(j) { j.f := E(F-1(j)); }
      //   1: forall j | Q(j) { A[j] := E(F-1(j)); }
      //   2: forall j | Q(j) { j[N] := E(F-1(j)); }
      // where we ensure that, for all i and j:
      //   R(i) && j == F(i)    <==>    Q(j) && F-1(j) == i
      // If the transformation succeeds, we use, respectively, j.f, A[j], and j[N] (each evaluated in the new heap) as
      // the trigger of the quantifier generated.

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
        if (lhs is MemberSelectExpr) {
          lhsType = ((MemberSelectExpr)lhs).Type;
        } else if (lhs is SeqSelectExpr) {
          lhsType = ((SeqSelectExpr)lhs).Type;
        } else {
          lhsType = ((MultiSelectExpr)lhs).Type;
        }
        var translatedRhs = etran.TrExpr(rhs);
        CheckSubrange(r.Tok, translatedRhs, lhsType, definedness);
        if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          Check_NewRestrictions(fse.tok, obj, field, translatedRhs, definedness, etran);
        }
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
        "left-hand sides for different forall-statement bound variables may refer to the same location"));

      definedness.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the translation of the update itself

      Bpl.IdentifierExpr prevHeap = GetPrevHeapVar_IdExpr(s.Tok, locals);
      var prevEtran = new ExpressionTranslator(this, predef, prevHeap);
      updater.Add(Bpl.Cmd.SimpleAssign(s.Tok, prevHeap, etran.HeapExpr));
      updater.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
      updater.Add(new Bpl.AssumeCmd(s.Tok, FunctionCall(s.Tok, BuiltinFunction.HeapSucc, null, prevHeap, etran.HeapExpr)));

      // Here comes:
      //   assume (forall<alpha> o: ref, f: Field alpha ::
      //     { $Heap[o,f] }
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
      List<Variable> xBvars = new List<Variable>();
      var xBody = etran.TrBoundVariables(s.BoundVars, xBvars);
      xBody = BplAnd(xBody, prevEtran.TrExpr(s.Range));
      Bpl.Expr xObj, xField;
      GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out xObj, out xField);
      xBody = BplAnd(xBody, Bpl.Expr.Eq(o, xObj));
      xBody = BplAnd(xBody, Bpl.Expr.Eq(f, xField));
      Bpl.Expr xObjField = new Bpl.ExistsExpr(s.Tok, xBvars, xBody);
      Bpl.Expr body = Bpl.Expr.Or(Bpl.Expr.Eq(heapOF, oldHeapOF), xObjField);
      var tr = new Trigger(s.Tok, true, new List<Expr>() { heapOF });
      Bpl.Expr qq = new Bpl.ForallExpr(s.Tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, body);
      updater.Add(new Bpl.AssumeCmd(s.Tok, qq));

      if (s0.Rhs is ExprRhs) {
        Expression Fi = null;
        Func<Expression,Expression> lhsBuilder = null;
        lhs = s0.Lhs.Resolved;
        var i = s.BoundVars[0];
        if (s.BoundVars.Count == 1) {
          //var lhsContext = null;
          // Detect the following cases:
          //   0: forall i | R(i) { F(i).f := E(i); }
          //   1: forall i | R(i) { A[F(i)] := E(i); }
          //   2: forall i | R(i) { F(i)[N] := E(i); }
          if (lhs is MemberSelectExpr) {
            var ll = (MemberSelectExpr)lhs;
            Fi = ll.Obj;
            lhsBuilder = e => { var l = new MemberSelectExpr(ll.tok, e, ll.MemberName); l.Member = ll.Member; l.Type = ll.Type; return l; };
          } else if (lhs is SeqSelectExpr) {
            var ll = (SeqSelectExpr)lhs;
            Contract.Assert(ll.SelectOne);
            if (!ContainsFreeVariable(ll.Seq, false, i)) {
              Fi = ll.E0;
              lhsBuilder = e => { var l = new SeqSelectExpr(ll.tok, true, ll.Seq, e, null); l.Type = ll.Type; return l; };
            } else if (!ContainsFreeVariable(ll.E0, false, i)) {
              Fi = ll.Seq;
              lhsBuilder = e => { var l = new SeqSelectExpr(ll.tok, true, e, ll.E0, null); l.Type = ll.Type; return l; };
            }
          }
        }
        var rhs = ((ExprRhs)s0.Rhs).Expr;
        bool usedInversion = false;
        if (Fi != null) {
          var j = new BoundVar(i.tok, i.Name + "#inv", Fi.Type);
          var jj = Expression.CreateIdentExpr(j);
          var jList = new List<BoundVar>() { j };
          var vals = InvertExpression(i, j, s.Range, Fi);
#if DEBUG_PRINT
          Console.WriteLine("DEBUG: Trying to invert:");
          Console.WriteLine("DEBUG:   " + Printer.ExprToString(s.Range) + " && " + j.Name + " == " + Printer.ExprToString(Fi));
          if (vals == null) {
            Console.WriteLine("DEBUG: Can't");
          } else {
            Console.WriteLine("DEBUG: The inverse is the disjunction of the following:");
            foreach (var val in vals) {
              Console.WriteLine("DEBUG:   " + Printer.ExprToString(val.Range) + " && " + Printer.ExprToString(val.FInverse) + " == " + i.Name);
            }
          }
#endif
          if (vals != null) {
            foreach (var val in vals) {
              qq = TrForall_NewValueAssumption(s.Tok, jList, val.Range, lhsBuilder(jj), Substitute(rhs, i, val.FInverse), true, etran, prevEtran);
              updater.Add(new Bpl.AssumeCmd(s.Tok, qq));
            }
            usedInversion = true;
          }
        }
        if (!usedInversion) {
          qq = TrForall_NewValueAssumption(s.Tok, s.BoundVars, s.Range, lhs, rhs, false, etran, prevEtran);
          updater.Add(new Bpl.AssumeCmd(s.Tok, qq));
        }
      }
    }

    /// <summary>
    /// Generate:
    ///   assume (forall x,y :: Range(x,y)[$Heap:=oldHeap] ==>
    ///                         $Heap[ Object(x,y)[$Heap:=oldHeap], Field(x,y)[$Heap:=oldHeap] ] == G[$Heap:=oldHeap] ));
    /// where
    ///   x,y           represent boundVars
    ///   Object(x,y)   is the first part of lhs
    ///   Field(x,y)    is the second part of lhs
    ///   G             is rhs
    /// If lhsAsTrigger is true, then use the LHS of the equality above as the trigger; otherwise, don't specify any trigger.
    /// </summary>
    private Bpl.Expr TrForall_NewValueAssumption(IToken tok, List<BoundVar> boundVars, Expression range, Expression lhs, Expression rhs, bool lhsAsTrigger, ExpressionTranslator etran, ExpressionTranslator prevEtran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(range != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(etran != null);
      Contract.Requires(prevEtran != null);

      var xBvars = new List<Variable>();
      Bpl.Expr xAnte = etran.TrBoundVariables(boundVars, xBvars);
      xAnte = BplAnd(xAnte, prevEtran.TrExpr(range));
      var g = prevEtran.TrExpr(rhs);
      Bpl.Expr obj, field;
      GetObjFieldDetails(lhs, prevEtran, out obj, out field);
      var xHeapOF = ExpressionTranslator.ReadHeap(tok, etran.HeapExpr, obj, field);

      Type lhsType = lhs is MemberSelectExpr ? ((MemberSelectExpr)lhs).Type : null;
      g = CondApplyBox(rhs.tok, g, rhs.Type, lhsType);

      Trigger tr = lhsAsTrigger ? new Trigger(tok, true, new List<Bpl.Expr>() { xHeapOF }) : null;
      return new Bpl.ForallExpr(tok, xBvars, tr, Bpl.Expr.Imp(xAnte, Bpl.Expr.Eq(xHeapOF, g)));
    }

    class ForallStmtTranslationValues
    {
      public readonly Expression Range;
      public readonly Expression FInverse;
      public ForallStmtTranslationValues(Expression range, Expression fInverse) {
        Contract.Requires(range != null);
        Contract.Requires(fInverse != null);
        Range = range;
        FInverse = fInverse;
      }
      public ForallStmtTranslationValues Subst(IVariable j, Expression e, Translator translator) {
        Contract.Requires(j != null);
        Contract.Requires(e != null);
        Contract.Requires(translator != null);
        var substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(j, e);
        var v = new ForallStmtTranslationValues(translator.Substitute(Range, null, substMap), translator.Substitute(FInverse, null, substMap));
        return v;
      }
    }

    /// <summary>
    /// Find piecewise inverse of F under R.  More precisely, find lists of expressions P and F-1
    /// such that
    ///     R(i) && j == F(i)
    /// holds iff the disjunction of the following predicates holds:
    ///     P_0(j) && F-1_0(j) == i
    ///     ...
    ///     P_{n-1}(j) && F-1_{n-1}(j) == i
    /// If no such disjunction is found, return null.
    /// If such a disjunction is found, return for each disjunct:
    ///     * The predicate P_k(j), which is an expression that may have free occurrences of j (but no free occurrences of i)
    ///     * The expression F-1_k(j), which also may have free occurrences of j but not of i
    /// </summary>
    private List<ForallStmtTranslationValues> InvertExpression(BoundVar i, BoundVar j, Expression R, Expression F) {
      Contract.Requires(i != null);
      Contract.Requires(j != null);
      Contract.Requires(R != null);
      Contract.Requires(F != null);
      var vals = new List<ForallStmtTranslationValues>(InvertExpressionIter(i, j, R, F));
      if (vals.Count == 0) {
        return null;
      } else {
        return vals;
      }
    }
    /// <summary>
    /// See InvertExpression.
    /// </summary>
    private IEnumerable<ForallStmtTranslationValues> InvertExpressionIter(BoundVar i, BoundVar j, Expression R, Expression F) {
      Contract.Requires(i != null);
      Contract.Requires(j != null);
      Contract.Requires(R != null);
      Contract.Requires(F != null);
      F = F.Resolved;
      if (!ContainsFreeVariable(F, false, i)) {
        // We're looking at R(i) && j == K.
        // We cannot invert j == K, but if we're lucky, R(i) contains a conjunct i==G.
        Expression r = Expression.CreateBoolLiteral(R.tok, true);
        Expression G = null;
        foreach (var c in Expression.Conjuncts(R)) {
          if (G == null && c is BinaryExpr) {
            var bin = (BinaryExpr)c;
            if (BinaryExpr.IsEqualityOp(bin.ResolvedOp)) {
              var id = bin.E0.Resolved as IdentifierExpr;
              if (id != null && id.Var == i) {
                G = bin.E1;
                continue;
              }
              id = bin.E1.Resolved as IdentifierExpr;
              if (id != null && id.Var == i) {
                G = bin.E0;
                continue;
              }
            }
          }
          r = Expression.CreateAnd(r, c);
        }
        if (G != null) {
          var jIsK = Expression.CreateEq(Expression.CreateIdentExpr(j), F, j.Type);
          var rr = Substitute(r, i, G);
          yield return new ForallStmtTranslationValues(Expression.CreateAnd(rr, jIsK), G);
        }
      } else if (F is IdentifierExpr) {
        var e = (IdentifierExpr)F;
        if (e.Var == i) {
          // We're looking at R(i) && j == i, which is particularly easy to invert:  R(j) && j == i
          var jj = Expression.CreateIdentExpr(j);
          yield return new ForallStmtTranslationValues(Substitute(R, i, jj), jj);
        }
      } else if (F is BinaryExpr) {
        var bin = (BinaryExpr)F;
        if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
          if (!ContainsFreeVariable(bin.E1, false, i)) {
            // We're looking at:  R(i) && j == f(i) + K.
            // By a recursive call, we'll ask to invert:  R(i) && j' == f(i).
            // For each P_0(j') && f-1_0(j') == i we get back, we yield:
            // P_0(j - K) && f-1_0(j - K) == i
            var jMinusK = Expression.CreateSubtract(Expression.CreateIdentExpr(j), bin.E1);
            foreach (var val in InvertExpression(i, j, R, bin.E0)) {
              yield return val.Subst(j, jMinusK, this);
            }
          } else if (!ContainsFreeVariable(bin.E0, false, i)) {
            // We're looking at:  R(i) && j == K + f(i)
            // Do as in previous case, but with operands reversed.
            var jMinusK = Expression.CreateSubtract(Expression.CreateIdentExpr(j), bin.E0);
            foreach (var val in InvertExpression(i, j, R, bin.E1)) {
              yield return val.Subst(j, jMinusK, this);
            }
          }
        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub) {
          if (!ContainsFreeVariable(bin.E1, false, i)) {
            // We're looking at:  R(i) && j == f(i) - K
            // Recurse on f(i) and then replace j := j + K
            var jPlusK = Expression.CreateAdd(Expression.CreateIdentExpr(j), bin.E1);
            foreach (var val in InvertExpression(i, j, R, bin.E0)) {
              yield return val.Subst(j, jPlusK, this);
            }
          } else if (!ContainsFreeVariable(bin.E0, false, i)) {
            // We're looking at:  R(i) && j == K - f(i)
            // Recurse on f(i) and then replace j := K - j
            var kMinusJ = Expression.CreateAdd(Expression.CreateIdentExpr(j), bin.E0);
            foreach (var val in InvertExpression(i, j, R, bin.E1)) {
              yield return val.Subst(j, kMinusJ, this);
            }
          }
        }
      } else if (F is ITEExpr) {
        var ife = (ITEExpr)F;
        // We're looking at R(i) && j == if A(i) then B(i) else C(i), which is equivalent to the disjunction of:
        //   R(i) && A(i) && j == B(i)
        //   R(i) && !A(i) && j == C(i)
        // We recurse on each one, yielding the results
        var r = Expression.CreateAnd(R, ife.Test);
        var valsThen = InvertExpression(i, j, r, ife.Thn);
        if (valsThen != null) {
          r = Expression.CreateAnd(R, Expression.CreateNot(ife.tok, ife.Test));
          var valsElse = InvertExpression(i, j, r, ife.Els);
          if (valsElse != null) {
            foreach (var val in valsThen) { yield return val; }
            foreach (var val in valsElse) { yield return val; }
          }
        }
      }
    }

    delegate Bpl.Expr ExpressionConverter(Dictionary<IVariable, Expression> substMap, ExpressionTranslator etran);

    void TrForallStmtCall(IToken tok, List<BoundVar> boundVars, Expression range, ExpressionConverter additionalRange, CallStmt s0,
      Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
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
      //   forall (x,y | Range(x,y)) {
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
        if (boundVars.Count != 0) {
          // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
          // here (rather than a TrBoundVariables).  However, there is currently no way to apply
          // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
          List<Variable> bvars = new List<Variable>();
          var ante = etran.TrBoundVariables(boundVars, bvars, true);
          locals.AddRange(bvars);
          var havocIds = new List<Bpl.IdentifierExpr>();
          foreach (Bpl.Variable bv in bvars) {
            havocIds.Add(new Bpl.IdentifierExpr(tok, bv));
          }
          definedness.Add(new Bpl.HavocCmd(tok, havocIds));
          definedness.Add(new Bpl.AssumeCmd(tok, ante));
        }
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
        var initHeapVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, "$initHeapForallStmt#" + otherTmpVarCount, predef.HeapType));
        otherTmpVarCount++;
        locals.Add(initHeapVar);
        var initHeap = new Bpl.IdentifierExpr(tok, initHeapVar);
        var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr);
        // initHeap := $Heap;
        exporter.Add(Bpl.Cmd.SimpleAssign(tok, initHeap, etran.HeapExpr));
        var heapIdExpr = (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr;
        // advance $Heap, Tick;
        exporter.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { heapIdExpr, etran.Tick() }));
        Contract.Assert(s0.Method.Mod.Expressions.Count == 0);  // checked by the resolver
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(tok, new List<FrameExpression>(), s0.IsGhost, initEtran, etran, initEtran)) {
          if (tri.IsFree) {
            exporter.Add(new Bpl.AssumeCmd(tok, tri.Expr));
          }
        }
        if (codeContext is IteratorDecl) {
          var iter = (IteratorDecl)codeContext;
          RecordNewObjectsIn_New(tok, iter, initHeap, heapIdExpr, exporter, locals, etran);
        }

        var bvars = new List<Variable>();
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
          var arg = Substitute(s0.Args[i], null, substMap, s0.TypeArgumentSubstitutions);  // substitute the renamed bound variables for the declared ones
          argsSubstMap.Add(s0.Method.Ins[i], new BoogieWrapper(initEtran.TrExpr(arg), s0.Args[i].Type));
        }
        var receiver = new BoogieWrapper(initEtran.TrExpr(Substitute(s0.Receiver, null, substMap, s0.TypeArgumentSubstitutions)), s0.Receiver.Type);
        var callEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, initHeap);
        Bpl.Expr post = Bpl.Expr.True;
        foreach (var ens in s0.Method.Ens) {
          var p = Substitute(ens.E, receiver, argsSubstMap, s0.TypeArgumentSubstitutions);  // substitute the call's actuals for the method's formals
          post = BplAnd(post, callEtran.TrExpr(p));
        }

        Bpl.Expr qq = new Bpl.ForallExpr(tok, bvars, Bpl.Expr.Imp(ante, post));
        exporter.Add(new Bpl.AssumeCmd(tok, qq));
      }
    }

    void RecordNewObjectsIn_New(IToken tok, IteratorDecl iter, Bpl.Expr initHeap, Bpl.IdentifierExpr currentHeap,
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(initHeap != null);
      Contract.Requires(currentHeap != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      // Add all newly allocated objects to the set this._new
      var updatedSet = new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, "$iter_newUpdate" + otherTmpVarCount, predef.SetType(iter.tok, predef.BoxType)));
      otherTmpVarCount++;
      locals.Add(updatedSet);
      var updatedSetIE = new Bpl.IdentifierExpr(iter.tok, updatedSet);
      // call $iter_newUpdate := $IterCollectNewObjects(initHeap, $Heap, this, _new);
      var th = new Bpl.IdentifierExpr(iter.tok, etran.This, predef.RefType);
      var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
      Bpl.Cmd cmd = new CallCmd(iter.tok, "$IterCollectNewObjects",
        new List<Bpl.Expr>() { initHeap, etran.HeapExpr, th, nwField },
        new List<Bpl.IdentifierExpr>() { updatedSetIE });
      builder.Add(cmd);
      // $Heap[this, _new] := $iter_newUpdate;
      cmd = Bpl.Cmd.SimpleAssign(iter.tok, currentHeap, ExpressionTranslator.UpdateHeap(iter.tok, currentHeap, th, nwField, updatedSetIE));
      builder.Add(cmd);
      // assume $IsGoodHeap($Heap)
      builder.Add(AssumeGoodHeap(tok, etran));
    }

    void TrForallProof(ForallStmt s, Bpl.StmtListBuilder definedness, Bpl.StmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
      // Translate:
      //   forall (x,y | Range(x,y))
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

      if (s.BoundVars.Count != 0) {
        // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
        // here (rather than a TrBoundVariables).  However, there is currently no way to apply
        // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
        var bVars = new List<Variable>();
        var typeAntecedent = etran.TrBoundVariables(s.BoundVars, bVars, true);
        locals.AddRange(bVars);
        var havocIds = new List<Bpl.IdentifierExpr>();
        foreach (Bpl.Variable bv in bVars) {
          havocIds.Add(new Bpl.IdentifierExpr(s.Tok, bv));
        }
        definedness.Add(new Bpl.HavocCmd(s.Tok, havocIds));
        definedness.Add(new Bpl.AssumeCmd(s.Tok, typeAntecedent));
      }
      TrStmt_CheckWellformed(s.Range, definedness, locals, etran, false);
      definedness.Add(new Bpl.AssumeCmd(s.Range.tok, etran.TrExpr(s.Range)));

      if (s.Body != null) {
        TrStmt(s.Body, definedness, locals, etran);

        // check that postconditions hold
        foreach (var ens in s.Ens) {
          if (!ens.IsFree) {
            bool splitHappened;  // we actually don't care
            foreach (var split in TrSplitExpr(ens.E, etran, true, out splitHappened)) {
              if (split.IsChecked) {
                definedness.Add(Assert(split.E.tok, split.E, "possible violation of postcondition of forall statement"));
              }
            }
          }
        }
      }

      definedness.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the other branch, where the ensures clauses are exported.

      var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$initHeapForallStmt#" + otherTmpVarCount, predef.HeapType));
      otherTmpVarCount++;
      locals.Add(initHeapVar);
      var initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
      var initEtran = new ExpressionTranslator(this, predef, initHeap, etran.Old.HeapExpr);
      // initHeap := $Heap;
      exporter.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
      // advance $Heap;
      exporter.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr, etran.Tick() }));
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, new List<FrameExpression>(), s.IsGhost, initEtran, etran, initEtran)) {
        if (tri.IsFree) {
          exporter.Add(new Bpl.AssumeCmd(s.Tok, tri.Expr));
        }
      }

      var bvars = new List<Variable>();
      Dictionary<IVariable, Expression> substMap;
      var ante = initEtran.TrBoundVariablesRename(s.BoundVars, bvars, out substMap);
      var range = Substitute(s.Range, null, substMap);
      ante = BplAnd(ante, initEtran.TrExpr(range));

      Bpl.Expr post = Bpl.Expr.True;
      foreach (var ens in s.Ens) {
        var p = Substitute(ens.E, null, substMap);
        post = BplAnd(post, etran.TrExpr(p));
      }

      Bpl.Expr qq = Bpl.Expr.Imp(ante, post);
      if (bvars.Count != 0) {
        qq = new Bpl.ForallExpr(s.Tok, bvars, qq);
      }
      exporter.Add(new Bpl.AssumeCmd(s.Tok, qq));
    }

    private string GetObjFieldDetails(Expression lhs, ExpressionTranslator etran, out Bpl.Expr obj, out Bpl.Expr F) {
      string description;
      if (lhs is MemberSelectExpr) {
        var fse = (MemberSelectExpr)lhs;
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
                Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(s != null);
      Contract.Requires(bodyTr != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      int loopId = loopHeapVarCount;
      loopHeapVarCount++;

      var theDecreases = s.Decreases.Expressions;

      Bpl.LocalVariable preLoopHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreLoopHeap" + loopId, predef.HeapType));
      locals.Add(preLoopHeapVar);
      Bpl.IdentifierExpr preLoopHeap = new Bpl.IdentifierExpr(s.Tok, preLoopHeapVar);
      ExpressionTranslator etranPreLoop = new ExpressionTranslator(this, predef, preLoopHeap);
      ExpressionTranslator updatedFrameEtran;
      string loopFrameName = "#_Frame#" + loopId;
      if (s.Mod.Expressions != null)
        updatedFrameEtran = new ExpressionTranslator(etran, loopFrameName);
      else
        updatedFrameEtran = etran;

      if (s.Mod.Expressions != null) { // check that the modifies is a subset
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
      builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { w }));

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
          var ss = TrSplitExpr(loopInv.E, etran, false, out splitHappened);
          if (!splitHappened) {
            var wInv = Bpl.Expr.Imp(w, etran.TrExpr(loopInv.E));
            invariants.Add(Assert(loopInv.E.tok, wInv, "loop invariant violation"));
          } else {
            foreach (var split in ss) {
              var wInv = Bpl.Expr.Binary(split.E.tok, BinaryOperator.Opcode.Imp, w, split.E);
              if (split.IsChecked) {
                invariants.Add(Assert(split.E.tok, wInv, "loop invariant violation"));  // TODO: it would be fine to have this use {:subsumption 0}
              } else {
                invariants.Add(new Bpl.AssumeCmd(split.E.tok, wInv));
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
      if (codeContext is IMethodCodeContext) {
        var modifiesClause = ((IMethodCodeContext)codeContext).Modifies.Expressions;
        // include boilerplate invariants
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, modifiesClause, s.IsGhost, etranPreLoop, etran, etran.Old)) {
          if (tri.IsFree) {
            invariants.Add(new Bpl.AssumeCmd(s.Tok, tri.Expr));
          } else {
            Contract.Assert(tri.ErrorMessage != null);  // follows from BoilerplateTriple invariant
            invariants.Add(Assert(s.Tok, tri.Expr, tri.ErrorMessage));
          }
        }
        // add a free invariant which says that the heap hasn't changed outside of the modifies clause.
        invariants.Add(new Bpl.AssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
      }

      // include a free invariant that says that all completed iterations so far have only decreased the termination metric
      if (initDecr != null) {
        var toks = new List<IToken>();
        var types = new List<Type>();
        var decrs = new List<Expr>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          types.Add(e.Type.NormalizeExpand());
          decrs.Add(etran.TrExpr(e));
        }
        Bpl.Expr decrCheck = DecreasesCheck(toks, types, types, decrs, initDecr, null, null, true, false);
        invariants.Add(new Bpl.AssumeCmd(s.Tok, decrCheck));
      }

      Bpl.StmtListBuilder loopBodyBuilder = new Bpl.StmtListBuilder();
      loopBodyBuilder.Add(CaptureState(s.Tok, true, "after some loop iterations"));
      // as the first thing inside the loop, generate:  if (!w) { CheckWellformed(inv); assume false; }
      invDefinednessBuilder.Add(new Bpl.AssumeCmd(s.Tok, Bpl.Expr.False));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, Bpl.Expr.Not(w), invDefinednessBuilder.Collect(s.Tok), null, null));
      // generate:  CheckWellformed(guard); if (!guard) { break; }
      Bpl.Expr guard = null;
      if (Guard != null) {
        TrStmt_CheckWellformed(Guard, loopBodyBuilder, locals, etran, true);
        guard = Bpl.Expr.Not(etran.TrExpr(Guard));
      }
      Bpl.StmtListBuilder guardBreak = new Bpl.StmtListBuilder();
      guardBreak.Add(new Bpl.BreakCmd(s.Tok, null));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, guard, guardBreak.Collect(s.Tok), null, null));

      // termination checking
      if (Contract.Exists(theDecreases, e => e is WildcardExpr)) {
        // omit termination checking for this loop
        bodyTr(loopBodyBuilder, updatedFrameEtran);
      } else {
        List<Bpl.Expr> oldBfs = RecordDecreasesValue(theDecreases, loopBodyBuilder, locals, etran, "$decr" + loopId + "$");
        // time for the actual loop body
        bodyTr(loopBodyBuilder, updatedFrameEtran);
        // check definedness of decreases expressions
        var toks = new List<IToken>();
        var types = new List<Type>();
        var decrs = new List<Expr>();
        foreach (Expression e in theDecreases) {
          toks.Add(e.tok);
          types.Add(e.Type.NormalizeExpand());
          decrs.Add(etran.TrExpr(e));
        }
        Bpl.Expr decrCheck = DecreasesCheck(toks, types, types, decrs, oldBfs, loopBodyBuilder, " at end of loop iteration", false, false);
        string msg;
        if (s.InferredDecreases) {
          msg = "cannot prove termination; try supplying a decreases clause for the loop";
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
    }

    void TrAlternatives(List<GuardedAlternative> alternatives, Bpl.Cmd elseCase0, Bpl.StructuredCmd elseCase1,
                        Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
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

    void TrCallStmt(CallStmt s, Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, Bpl.Expr actualReceiver) {
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
        builder.Add(new CommentCmd("TrCallStmt: Adding lhs " + lhs + " with type " + lhs.Type));
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
      Bpl.IdentifierExpr initHeap = null;
      if (codeContext is IteratorDecl) {
        // var initHeap := $Heap;
        var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$initHeapCallStmt#" + otherTmpVarCount, predef.HeapType));
        otherTmpVarCount++;
        locals.Add(initHeapVar);
        initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
        // initHeap := $Heap;
        builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
      }
      builder.Add(new CommentCmd("TrCallStmt: Before ProcessCallStmt"));
      ProcessCallStmt(s.Tok, s.TypeArgumentSubstitutions, GetTypeParams(s.Method), s.Receiver, actualReceiver, s.Method, s.Args, bLhss, lhsTypes, builder, locals, etran);
      builder.Add(new CommentCmd("TrCallStmt: After ProcessCallStmt"));
      for (int i = 0; i < lhsBuilders.Count; i++) {
        var lhs = s.Lhs[i];
        Type lhsType = null;
        if (lhs is IdentifierExpr) {
          lhsType = lhs.Type;
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          lhsType = field.Type;
        }

        Bpl.Expr bRhs = bLhss[i];  // the RHS (bRhs) of the assignment to the actual call-LHS (lhs) was a LHS (bLhss[i]) in the Boogie call statement
        if (lhsType != null) {
          builder.Add(new CommentCmd("TrCallStmt: Checking bRhs " + bRhs + " to have type " + lhs.Type));
          CheckSubrange(lhs.tok, bRhs, lhs.Type, builder);
        }
        bRhs = CondApplyBox(lhs.tok, bRhs, lhs.Type, lhsType);

        lhsBuilders[i](bRhs, builder, etran);
      }
      if (codeContext is IteratorDecl) {
        var iter = (IteratorDecl)codeContext;
        Contract.Assert(initHeap != null);
        RecordNewObjectsIn_New(s.Tok, iter, initHeap, (Bpl.IdentifierExpr/*TODO: this cast is dubious*/)etran.HeapExpr, builder, locals, etran);
      }
      builder.Add(CaptureState(s));
    }

    List<Bpl.Expr> trTypeArgs(Dictionary<TypeParameter, Type> tySubst, List<TypeParameter> tyArgs) {
      var res = new List<Bpl.Expr>();
      foreach (var p in tyArgs) {
        res.Add(TypeToTy(tySubst[p]));
      }
      return res;
    }

    void ProcessCallStmt(IToken tok,
      Dictionary<TypeParameter, Type> tySubst, List<TypeParameter> tyArgs,
      Expression dafnyReceiver, Bpl.Expr bReceiver,
      Method method, List<Expression> Args,
      List<Bpl.IdentifierExpr> Lhss, List<Type> LhsTypes,
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {

      Contract.Requires(tok != null);
      Contract.Requires(dafnyReceiver != null || bReceiver != null);
      Contract.Requires(method != null);
      Contract.Requires(Args != null);
      Contract.Requires(Lhss != null);
      Contract.Requires(LhsTypes != null);
      Contract.Requires(method.Outs.Count == Lhss.Count);
      Contract.Requires(method.Outs.Count == LhsTypes.Count);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(tySubst != null);
      Contract.Requires(tyArgs != null);
      Contract.Requires(tySubst.Count == tyArgs.Count);

      // Figure out if the call is recursive or not, which will be used below to determine the need for a
      // termination check and the need to include an implicit _k-1 argument.
      bool isRecursiveCall = false;
      // consult the call graph to figure out if this is a recursive call
      var module = method.EnclosingClass.Module;
      if (codeContext != null && module == currentModule) {
        // Note, prefix lemmas are not recorded in the call graph, but their corresponding colemmas are.
        // Similarly, an iterator is not recorded in the call graph, but its MoveNext method is.
        ICallable cllr =
          codeContext is PrefixLemma ? ((PrefixLemma)codeContext).Co :
          codeContext is IteratorDecl ? ((IteratorDecl)codeContext).Member_MoveNext :
          codeContext;
        if (ModuleDefinition.InSameSCC(method, cllr)) {
          isRecursiveCall = true;
        }
      }

      MethodTranslationKind kind;
      var callee = method;
      if (method is CoLemma && isRecursiveCall) {
        kind = MethodTranslationKind.CoCall;
        callee = ((CoLemma)method).PrefixLemma;
      } else if (method is PrefixLemma) {
        // an explicit call to a prefix lemma is allowed only inside the SCC of the corresponding colemma,
        // so we consider this to be a co-call
        kind = MethodTranslationKind.CoCall;
      } else if (module == currentModule) {
        kind = MethodTranslationKind.IntraModuleCall;
      } else {
        kind = MethodTranslationKind.InterModuleCall;
      }


      var ins = new List<Bpl.Expr>();
      // Add type arguments
      ins.AddRange(trTypeArgs(tySubst, tyArgs));

      // Translate receiver argument, if any
      Expression receiver = bReceiver == null ? dafnyReceiver : new BoogieWrapper(bReceiver, dafnyReceiver.Type);      
      if (!method.IsStatic) {
        if (bReceiver == null && !(dafnyReceiver is ThisExpr)) {
          CheckNonNull(dafnyReceiver.tok, dafnyReceiver, builder, etran, null);
        }
        ins.Add(etran.TrExpr(receiver));
      }

      // Ideally, the modifies and decreases checks would be done after the precondition check,
      // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
      // store the actual parameters.
      // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
      var substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < callee.Ins.Count; i++) {
        var formal = callee.Ins[i];
        var local = new LocalVariable(formal.tok, formal.tok, formal.Name + "#", formal.Type, formal.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(formal, ie);
        locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration), TrType(local.Type))));

        var param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
        Bpl.Expr bActual;
        if (i == 0 && method is CoLemma && isRecursiveCall) {
          // Treat this call to M(args) as a call to the corresponding prefix lemma M#(_k - 1, args), so insert an argument here.
          var k = ((PrefixLemma)codeContext).K;
          bActual = Bpl.Expr.Sub(new Bpl.IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration), Bpl.Type.Int), Bpl.Expr.Literal(1));
        } else {
          Expression actual;
          if (method is CoLemma && isRecursiveCall) {
            actual = Args[i - 1];
          } else {
            actual = Args[i];
          }
          TrStmt_CheckWellformed(actual, builder, locals, etran, true);
          builder.Add(new CommentCmd("ProcessCallStmt: CheckSubrange"));
          // Check the subrange without boxing 
          var beforeBox = etran.TrExpr(actual);
          CheckSubrange(actual.tok, beforeBox, Resolver.SubstType(formal.Type, tySubst), builder);
          bActual = CondApplyBox(actual.tok, beforeBox, actual.Type, formal.Type);
        }
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(formal.tok, param, bActual);
        builder.Add(cmd);
        ins.Add(param);
      }

      // Check modifies clause of a subcall is a subset of the current frame.
      if (codeContext is IMethodCodeContext) {
        CheckFrameSubset(tok, callee.Mod.Expressions, receiver, substMap, etran, builder, "call may violate context's modifies clause", null);
      }

      // Check termination
      if (isRecursiveCall) {
        Contract.Assert(codeContext != null);
        List<Expression> contextDecreases = codeContext.Decreases.Expressions;
        List<Expression> calleeDecreases = callee.Decreases.Expressions;
        CheckCallTermination(tok, contextDecreases, calleeDecreases, null, receiver, substMap, etran, etran.Old, builder, codeContext.InferredDecreases, null);
      }

      // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
      var outs = new List<Bpl.IdentifierExpr>();
      var tmpOuts = new List<Bpl.IdentifierExpr>();
      for (int i = 0; i < Lhss.Count; i++) {
        var bLhs = Lhss[i];
        if (ModeledAsBoxType(callee.Outs[i].Type) && !ModeledAsBoxType(LhsTypes[i])) {
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

      builder.Add(new CommentCmd("ProcessCallStmt: Make the call"));
      // Make the call
      Bpl.CallCmd call = new Bpl.CallCmd(tok, MethodName(callee, kind), ins, outs);
      if (module != currentModule && RefinementToken.IsInherited(tok, currentModule) && (codeContext == null || !codeContext.MustReverify)) {
        // The call statement is inherited, so the refined module already checked that the precondition holds.  Note,
        // preconditions are not allowed to be strengthened, except if they use a predicate whose body has been strengthened.
        // But if the callee sits in a different module, then any predicate it uses will be treated as opaque (that is,
        // uninterpreted) anyway, so the refined module will have checked the call precondition for all possible definitions
        // of the predicate.
        call.IsFree = true;
      }
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
          Bpl.Cmd cmd = new Bpl.HavocCmd(bLhs.tok, new List<Bpl.IdentifierExpr> { bLhs });
          builder.Add(cmd);
          cmd = new Bpl.AssumeCmd(bLhs.tok, Bpl.Expr.Eq(bLhs, FunctionCall(bLhs.tok, BuiltinFunction.Unbox, TrType(LhsTypes[i]), tmpVarIdE)));
          builder.Add(cmd);
        }
      }
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, Dictionary<TypeParameter, Type> typeMap = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      if (typeMap == null) {
        typeMap = new Dictionary<TypeParameter, Type>();
      }
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (BoundVar bv in boundVars) {
        LocalVariable local = new LocalVariable(bv.tok, bv.tok, bv.Name, Resolver.SubstType(bv.Type, typeMap), bv.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(bv, ie);
        Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration), TrType(local.Type)));
        locals.Add(bvar);
        var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
        builder.Add(new Bpl.HavocCmd(bv.tok, new List<Bpl.IdentifierExpr> { bIe }));
        Bpl.Expr wh = GetWhereClause(bv.tok, bIe, local.Type, etran);
        if (wh != null) {
          builder.Add(new Bpl.AssumeCmd(bv.tok, wh));
        }
      }
      return substMap;
    }

    List<Bpl.Expr> RecordDecreasesValue(List<Expression> decreases, Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, string varPrefix)
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
    void CheckCallTermination(IToken tok, List<Expression> contextDecreases, List<Expression> calleeDecreases,
                              Bpl.Expr allowance,
                              Expression receiverReplacement, Dictionary<IVariable,Expression> substMap,
                              ExpressionTranslator etranCurrent, ExpressionTranslator etranInitial, Bpl.StmtListBuilder builder, bool inferredDecreases, string hint) {
      Contract.Requires(tok != null);
      Contract.Requires(cce.NonNullElements(contextDecreases));
      Contract.Requires(cce.NonNullElements(calleeDecreases));
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(etranCurrent != null);
      Contract.Requires(etranInitial != null);
      Contract.Requires(builder != null);

      // The interpretation of the given decreases-clause expression tuples is as a lexicographic tuple, extended into
      // an infinite tuple by appending TOP elements.  The TOP element is strictly larger than any other value given
      // by a Dafny expression.  Each Dafny types has its own ordering, and these orderings are combined into a partial
      // order where elements from different Dafny types are incomparable.  Thus, as an optimization below, if two
      // components from different types are compared, the answer is taken to be false.

      if (Contract.Exists(calleeDecreases, e => e is WildcardExpr)) {
        // no check needed
        return;
      }

      int N = Math.Min(contextDecreases.Count, calleeDecreases.Count);
      var toks = new List<IToken>();
      var types0 = new List<Type>();
      var types1 = new List<Type>();
      var callee = new List<Expr>();
      var caller = new List<Expr>();
      if (RefinementToken.IsInherited(tok, currentModule) && contextDecreases.All(e => !RefinementToken.IsInherited(e.tok, currentModule))) {
        // the call site is inherited but all the context decreases expressions are new
        tok = new ForceCheckToken(tok);
      }
      for (int i = 0; i < N; i++) {
        Expression e0 = Substitute(calleeDecreases[i], receiverReplacement, substMap);
        Expression e1 = contextDecreases[i];
        if (!CompatibleDecreasesTypes(e0.Type, e1.Type)) {
          N = i;
          break;
        }
        toks.Add(new NestedToken(tok, e1.tok));
        types0.Add(e0.Type.NormalizeExpand());
        types1.Add(e1.Type.NormalizeExpand());
        callee.Add(etranCurrent.TrExpr(e0));
        caller.Add(etranInitial.TrExpr(e1));
      }
      bool endsWithWinningTopComparison = N == contextDecreases.Count && N < calleeDecreases.Count;
      Bpl.Expr decrExpr = DecreasesCheck(toks, types0, types1, callee, caller, builder, "", endsWithWinningTopComparison, false);
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
    /// Requires all types in types0 and types1 to be non-proxy non-synonym types (that is, callers should invoke NormalizeExpand)
    /// </summary>
    Bpl.Expr DecreasesCheck(List<IToken> toks, List<Type> types0, List<Type> types1, List<Bpl.Expr> ee0, List<Bpl.Expr> ee1,
                            Bpl.StmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound)
    {
      Contract.Requires(cce.NonNullElements(toks));
      Contract.Requires(cce.NonNullElements(types0));
      Contract.Requires(cce.NonNullElements(types1));
      Contract.Requires(cce.NonNullElements(ee0));
      Contract.Requires(cce.NonNullElements(ee1));
      Contract.Requires(predef != null);
      Contract.Requires(types0.Count == types1.Count && types0.Count == ee0.Count && ee0.Count == ee1.Count);
      Contract.Requires(builder == null || suffixMsg != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      int N = types0.Count;

      // compute eq and less for each component of the lexicographic pair
      List<Bpl.Expr> Eq = new List<Bpl.Expr>(N);
      List<Bpl.Expr> Less = new List<Bpl.Expr>(N);
      for (int i = 0; i < N; i++) {
        Bpl.Expr less, atmost, eq;
        ComputeLessEq(toks[i], types0[i], types1[i], ee0[i], ee1[i], out less, out atmost, out eq, includeLowerBound);
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
          };

          Bpl.Expr zero = null;
          string zeroStr = null;
          if (types0[k].IsNumericBased(Type.NumericPersuation.Int)) {
            zero = Bpl.Expr.Literal(0);
            zeroStr = "0";
          } else if (types0[k].IsNumericBased(Type.NumericPersuation.Real)) {
            zero = Bpl.Expr.Literal(Basetypes.BigDec.ZERO);
            zeroStr = "0.0";
          }
          if (zero != null) {
            Bpl.Expr bounded = Bpl.Expr.Le(zero, ee1[k]);
            for (int i = 0; i < k; i++) {
              bounded = Bpl.Expr.Or(bounded, Less[i]);
            }
            string component = N == 1 ? "" : " (component " + k + ")";
            Bpl.Cmd cmd = Assert(toks[k], Bpl.Expr.Or(bounded, Eq[k]), "decreases expression" + component + " must be bounded below by " + zeroStr + suffixMsg);
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
      t = t.NormalizeExpand();
      u = u.NormalizeExpand();
      if (t is BoolType) {
        return u is BoolType;
      } else if (t.IsNumericBased(Type.NumericPersuation.Int)) {
        // we can allow different kinds of int-based types
        return u.IsNumericBased(Type.NumericPersuation.Int);
      } else if (t.IsNumericBased(Type.NumericPersuation.Real)) {
        // we can allow different kinds of real-based types
        return u.IsNumericBased(Type.NumericPersuation.Real);
      } else if (t is SetType) {
        return u is SetType;
      } else if (t is SeqType) {
        return u is SeqType || u.IsIndDatatype;
      } else if (t.IsDatatype) {
        return u.IsDatatype || (t.IsIndDatatype && u is SeqType);
      } else if (t.IsRefType) {
        return u.IsRefType;
      } else if (t is MultiSetType) {
        return u is MultiSetType;
      } else if (t is MapType) {
        return u is MapType;
      } else if (t is ArrowType) {
        return u is ArrowType;
      } else {
        Contract.Assert(t.IsTypeParameter);
        return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
      }
    }

    Nullable<BuiltinFunction> RankFunction(Type/*!*/ ty)
    {
      Contract.Ensures(ty != null);
      if (ty is SeqType)      return BuiltinFunction.SeqRank;
      else if (ty.IsDatatype) return BuiltinFunction.DtRank;
      else return null;
    }

    /// <summary>
    /// Requires ty0 and ty1 to be non-proxy non-synonym types (that is, caller is expected have have invoked NormalizeExpand)
    /// </summary>
    void ComputeLessEq(IToken tok, Type ty0, Type ty1, Bpl.Expr e0, Bpl.Expr e1, out Bpl.Expr less, out Bpl.Expr atmost, out Bpl.Expr eq, bool includeLowerBound)
    {
      Contract.Requires(tok != null);
      Contract.Requires(ty0 != null);
      Contract.Requires(ty1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ValueAtReturn(out less)!=null);
      Contract.Ensures(Contract.ValueAtReturn(out atmost)!=null);
      Contract.Ensures(Contract.ValueAtReturn(out eq)!=null);

      var rk0 = RankFunction(ty0);
      var rk1 = RankFunction(ty1);
      if (rk0 != null && rk1 != null && rk0 != rk1) {
        eq = Bpl.Expr.False;
        Bpl.Expr b0 = FunctionCall(tok, rk0.Value, null, e0);
        Bpl.Expr b1 = FunctionCall(tok, rk1.Value, null, e1);
        less = Bpl.Expr.Lt(b0, b1);
        atmost = Bpl.Expr.Le(b0, b1);
      } else if (ty0 is BoolType) {
        eq = Bpl.Expr.Iff(e0, e1);
        less = Bpl.Expr.And(Bpl.Expr.Not(e0), e1);
        atmost = Bpl.Expr.Imp(e0, e1);
      } else if (ty0.IsNumericBased(Type.NumericPersuation.Int) || ty0 is SeqType || ty0.IsDatatype) {
        Bpl.Expr b0, b1;
        if (ty0.IsNumericBased(Type.NumericPersuation.Int)) {
          b0 = e0;
          b1 = e1;
        } else if (ty0 is SeqType) {
          b0 = FunctionCall(tok, BuiltinFunction.SeqRank, null, e0);
          b1 = FunctionCall(tok, BuiltinFunction.SeqRank, null, e1);
        } else if (ty0.IsDatatype) {
          b0 = FunctionCall(tok, BuiltinFunction.DtRank, null, e0);
          b1 = FunctionCall(tok, BuiltinFunction.DtRank, null, e1);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
        eq = Bpl.Expr.Eq(b0, b1);
        less = Bpl.Expr.Lt(b0, b1);
        atmost = Bpl.Expr.Le(b0, b1);
        if (ty0.IsNumericBased(Type.NumericPersuation.Int) && includeLowerBound) {
          less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), less);
          atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), atmost);
        }

      } else if (ty0.IsNumericBased(Type.NumericPersuation.Real)) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.Le(e0, Bpl.Expr.Sub(e1, Bpl.Expr.Literal(Basetypes.BigDec.FromInt(1))));
        atmost = Bpl.Expr.Le(e0, e1);
        if (includeLowerBound) {
          less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(Basetypes.BigDec.ZERO), e0), less);
          atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(Basetypes.BigDec.ZERO), e0), atmost);
        }

      } else if (ty0 is IteratorDecl.EverIncreasingType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.Gt(e0, e1);
        atmost = Bpl.Expr.Ge(e0, e1);

      } else if (ty0 is SetType || ty0 is MapType) {
        Bpl.Expr b0, b1;
        if (ty0 is SetType) {
          b0 = e0;
          b1 = e1;
        } else if (ty0 is MapType) {
          // for maps, compare their domains as sets
          b0 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType(tok, predef.BoxType, predef.BoxType), e0);
          b1 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType(tok, predef.BoxType, predef.BoxType), e1);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();
        }
        eq = FunctionCall(tok, BuiltinFunction.SetEqual, null, b0, b1);
        less = ProperSubset(tok, b0, b1);
        atmost = FunctionCall(tok, BuiltinFunction.SetSubset, null, b0, b1);

      } else if (ty0 is MultiSetType) {
        eq = FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
        less = ProperMultiset(tok, e0, e1);
        atmost = FunctionCall(tok, BuiltinFunction.MultiSetSubset, null, e0, e1);

      } else if (ty0 is ArrowType) {
        // TODO: ComputeLessEq for arrow types
        // what!?
        eq = Bpl.Expr.False;
        less = Bpl.Expr.False;
        atmost = Bpl.Expr.False;

      } else {
        // reference type
        Contract.Assert(ty0.IsRefType);  // otherwise, unexpected type
        var b0 = Bpl.Expr.Neq(e0, predef.Null);
        var b1 = Bpl.Expr.Neq(e1, predef.Null);
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

    /// <summary>
    /// Therefore, these properties are applied to method in-parameters. 
    /// For now, this only allows you to case split on incoming data type values.
    /// This used to add IsGood[Multi]Set_Extendend, but that is always 
    /// added for sets & multisets now in the prelude.
    /// </summary>
    Bpl.Expr GetExtendedWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      var r = GetWhereClause(tok, x, type, etran);
      type = type.NormalizeExpand();
      if (type.IsDatatype) {
        UserDefinedType udt = (UserDefinedType)type;
        var oneOfTheCases = FunctionCall(tok, "$IsA#" + udt.ResolvedClass.FullSanitizedName, Bpl.Type.Bool, x);
        return BplAnd(r, oneOfTheCases);
      } else {
        return r;
      }
    }

    /// <summary>
    /// Translates an AST Type to a Boogie expression of type Ty.
    /// </summary>
    Bpl.Expr TypeToTy(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      type = type.NormalizeExpand();

      if (type is SetType) {
        return FunctionCall(Token.NoToken, "TSet", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MultiSetType) {
        return FunctionCall(Token.NoToken, "TMultiSet", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is SeqType) {
        return FunctionCall(Token.NoToken, "TSeq", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MapType) {
        return FunctionCall(Token.NoToken, "TMap", predef.Ty, 
          TypeToTy(((MapType)type).Domain),
          TypeToTy(((MapType)type).Range)); 
      } else if (type is BoolType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TBool", predef.Ty);
      } else if (type is RealType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TReal", predef.Ty);
      } else if (type is NatType) {
        // (Nat needs to come before Int)
        return new Bpl.IdentifierExpr(Token.NoToken, "TNat", predef.Ty);
      } else if (type is IntType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TInt", predef.Ty);
      } else if (type.IsTypeParameter) {
        var args = type.TypeArgs.ConvertAll(TypeToTy);
        return trTypeParam(type.AsTypeParameter, args);
      } else if (type is ObjectType) {
        return ClassTyCon(program.BuiltIns.ObjectDecl, new List<Bpl.Expr>());
      } else if (type is UserDefinedType) {
        // Classes, (co-)datatypes
        var args = type.TypeArgs.ConvertAll(TypeToTy);
        return ClassTyCon(((UserDefinedType)type), args);      
      } else if (type is ParamTypeProxy) {
        return trTypeParam(((ParamTypeProxy)type).orig, null);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    static string nameTypeParam(TypeParameter x) {
      Contract.Requires(x != null);
      if (x.Parent != null) {
        return x.Parent.FullName + "$" + x.Name;
      } else {
        // This happens for builtins, like arrays, that don't have a parent
        return "#$" + x.Name;
      }
    }
   
    Bpl.Expr trTypeParam(TypeParameter x, List<Bpl.Expr> tyArguments) {
      Contract.Requires(x != null);
      var nm = nameTypeParam(x);
      var opaqueType = x as OpaqueType_AsParameter;
      if (tyArguments != null && tyArguments.Count != 0) {
        return FunctionCall(x.tok, nm, predef.Ty, tyArguments);
      } else {
        // return an identifier denoting a constant
        return new Bpl.IdentifierExpr(x.tok, nm, predef.Ty);
      }
    }

    public List<TypeParameter> GetTypeParams(IMethodCodeContext cc) {
      if (cc is Method) {
        Method m = (Method)cc;
        return Concat(GetTypeParams(m.EnclosingClass), m.TypeArgs);
      } else if (cc is IteratorDecl) {
        return cc.TypeArgs; // This one cannot be enclosed in a class
      } else {
        Contract.Assert(false);
        return null;
      }
    }

    static public List<TypeParameter> GetTypeParams(TopLevelDecl d) {
      if (d is ClassDecl) {
        return Concat(GetTypeParams(d.Module), d.TypeArgs);
      } else if (d is DatatypeDecl) {
        return Concat(GetTypeParams(d.Module), d.TypeArgs);      
      } else if (d is ModuleDefinition) {       
        return new List<TypeParameter>();
      } else {
        Contract.Assert(false);
        return null;
      }
    }

    static List<TypeParameter> GetTypeParams(Function f) {
      if (f.EnclosingClass == null) {
        return f.TypeArgs;
      } else {
        return Concat(GetTypeParams(f.EnclosingClass), f.TypeArgs);
      }
    }

    // Boxes, if necessary 
    Bpl.Expr MkIs(Bpl.Expr x, Type t) {
      return MkIs(x, TypeToTy(t), ModeledAsBoxType(t));
    }

    Bpl.Expr MkIs(Bpl.Expr x, Bpl.Expr t, bool box = false) {
      if (box) {
        return FunctionCall(x.tok, BuiltinFunction.IsBox, null, x, t);
      } else {
        return FunctionCall(x.tok, BuiltinFunction.Is, null, x, t);
      }
    }

    // Boxes, if necessary
    Bpl.Expr MkIsAlloc(Bpl.Expr x, Type t, Bpl.Expr h)
    {
      return MkIsAlloc(x, TypeToTy(t), h, ModeledAsBoxType(t));
    }

    Bpl.Expr MkIsAlloc(Bpl.Expr x, Bpl.Expr t, Bpl.Expr h, bool box = false) {
      if (box) {
        return FunctionCall(x.tok, BuiltinFunction.IsAllocBox, null, x, t, h);
      } else {
        return FunctionCall(x.tok, BuiltinFunction.IsAlloc, null, x, t, h);
      }
    }


    Bpl.Expr GetWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      type = type.NormalizeExpand();
      if (type is TypeProxy) {
        // Unresolved proxy
        // Omit where clause (in other places, unresolved proxies are treated as a reference type; we could do that here too, but
        // we might as well leave out the where clause altogether).
        return null;
      }

      if (type is NatType) {
        // nat:
        // 0 <= x
        return Bpl.Expr.Le(Bpl.Expr.Literal(0), x);
      } else if (type is BoolType || type is IntType || type is RealType) {
        // nothing to do
        return null;
      /* } else if (type is ArrowType) {
        // dubious, but nothing to do?!
        return null;
        */
      } else {
        return BplAnd(MkIs(x, type), MkIsAlloc(x, type, etran.HeapExpr));
      }
    }

    Bpl.Expr GetBoolBoxCondition(Expr box, Type type) {
      Contract.Requires(box != null);
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (type.IsBoolType) {
        return FunctionCall(box.tok, BuiltinFunction.IsCanonicalBoolBox, null, box);
      } else {
        return Bpl.Expr.True;
      }
    }

    /// <summary>
    /// "lhs" is expected to be a resolved form of an expression, i.e., not a conrete-syntax expression.
    /// </summary>
    void TrAssignment(Statement stmt, Expression lhs, AssignmentRhs rhs,
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(lhs != null);
      Contract.Requires(!(lhs is ConcreteSyntaxExpression));
      Contract.Requires(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // these were once allowed, but their functionality is now provided by 'forall' statements
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
      builder.Add(CaptureState(stmt));
    }

    void ProcessRhss(List<AssignToLhs> lhsBuilder, List<Bpl.IdentifierExpr/*may be null*/> bLhss,
      List<Expression> lhss, List<AssignmentRhs> rhss,
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
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
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          lhsType = field.Type;
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
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
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
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          lhsType = field.Type;
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
              builder.Add(Assert(tok, Bpl.Expr.Imp(Bpl.Expr.True, Bpl.Expr.Eq(rhs[i], rhs[j])), string.Format("when left-hand sides {0} and {1} refer to the same location, they must be assigned the same value", j, i)));
            }
          }
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          // check that this LHS is not the same as any previous LHSs
          for (int j = 0; j < i; j++) {
            var prev = lhss[j] as MemberSelectExpr;
            var field = fse.Member as Field;
            Contract.Assert(field != null);
            var prevField = prev == null ? null : prev.Member as Field;
            if (prev != null && prevField == field) {
              builder.Add(Assert(tok, Bpl.Expr.Imp(Bpl.Expr.Eq(objs[j], objs[i]), Bpl.Expr.Eq(rhs[i], rhs[j])), string.Format("when left-hand sides {0} and {1} refer to the same location, they must be assigned the same value", j, i)));
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
                string.Format("when left-hand sides {0} and {1} may refer to the same location, they must be assigned the same value", j, i)));
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
                string.Format("when left-hand sides {0} and {1} refer to the same location, they must be assigned the same value", j, i)));
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
      Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
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
            bldr.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, rhs));
          });

        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          var obj = SaveInTemp(etran.TrExpr(fse.Obj), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          prevObj[i] = obj;
          // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj]);
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, GetField(fse)), "assignment may update an object not in the enclosing context's modifies clause"));

          if (checkDistinctness) {
            // check that this LHS is not the same as any previous LHSs
            for (int j = 0; j < i; j++) {
              var prev = lhss[j] as MemberSelectExpr;
              var prevField = prev == null ? null : prev.Member as Field;
              if (prevField != null && prevField == field) {
                builder.Add(Assert(tok, Bpl.Expr.Neq(prevObj[j], obj), string.Format("left-hand sides {0} and {1} may refer to the same location", j, i)));
              }
            }
          }

          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, Bpl.StmtListBuilder bldr, ExpressionTranslator et) {
            var fseField = fse.Member as Field;
            Contract.Assert(fseField != null);
            Check_NewRestrictions(tok, obj, fseField, rhs, bldr, et);
            var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, new Bpl.IdentifierExpr(tok, GetField(fseField)), rhs));
            bldr.Add(cmd);
            // assume $IsGoodHeap($Heap);
            bldr.Add(AssumeGoodHeap(tok, et));
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
            bldr.Add(cmd);
            // assume $IsGoodHeap($Heap);
            bldr.Add(AssumeGoodHeap(tok, et));
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
            bldr.Add(cmd);
            // assume $IsGoodHeap($Heap);
            bldr.Add(AssumeGoodHeap(tok, etran));
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
                                       Bpl.StmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
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
        bRhs = CondApplyBox(tok, bRhs, e.Expr.Type, lhsType);

        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, bRhs);
        builder.Add(cmd);

      } else if (rhs is HavocRhs) {
        builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { bLhs }));
        var isNat = CheckSubrange_Expr(tok, bLhs, checkSubrangeType);
        if (isNat != null) {
          builder.Add(new Bpl.AssumeCmd(tok, isNat));
        }
      } else {
        // x := new Something
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
        builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { nw }));
        // assume $nw != null && !$Heap[$nw, alloc] && dtype($nw) == RHS;
        Bpl.Expr nwNotNull = Bpl.Expr.Neq(nw, predef.Null);
        Bpl.Expr rightType;
        rightType = etran.GoodRef_(tok, nw, tRhs.EType, true);
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
        if (codeContext is IteratorDecl) {
          var iter = (IteratorDecl)codeContext;
          // $Heap[this, _new] := Set#UnionOne<BoxType>($Heap[this, _new], $Box($nw));
          var th = new Bpl.IdentifierExpr(tok, etran.This, predef.RefType);
          var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
          var thisDotNew = ReadHeap(tok, etran.HeapExpr, th, nwField);
          var unionOne = FunctionCall(tok, BuiltinFunction.SetUnionOne, predef.BoxType, thisDotNew, FunctionCall(tok, BuiltinFunction.Box, null, nw));
          var heapRhs = ExpressionTranslator.UpdateHeap(tok, etran.HeapExpr, th, nwField, unionOne);
          builder.Add(Bpl.Cmd.SimpleAssign(tok, heap, heapRhs));
        }
        // assume $IsGoodHeap($Heap);
        builder.Add(AssumeGoodHeap(tok, etran));
        if (tRhs.InitCall != null) {
          AddComment(builder, tRhs.InitCall, "init call statement");
          TrCallStmt(tRhs.InitCall, builder, locals, etran, nw);
        }
        // bLhs := $nw;
        builder.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, CondApplyBox(tok, nw, tRhs.Type, lhsType)));
      }
      return bLhs;
    }

    void CheckSubrange(IToken tok, Bpl.Expr bRhs, Type tp, StmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(bRhs != null);
      Contract.Requires(tp != null);
      Contract.Requires(builder != null);

      var cre = CheckSubrange_Expr(tok, bRhs, tp);
      var msg = (tp.NormalizeExpand() is NatType) ?
                                  "value assigned to a nat must be non-negative" :
                                  "value does not satisfy the subrange criteria";
      builder.Add(Assert(tok, cre, msg));
    }

    Bpl.Expr CheckSubrange_Expr(IToken tok, Bpl.Expr bRhs, Type tp) {
      Contract.Requires(tok != null);
      Contract.Requires(bRhs != null);
      Contract.Requires(tp != null);

      // Only need to check this for natural numbers for now.
      // We should always be able to use  Is, but this is an optimisation.
      if (tp.NormalizeExpand() is NatType) {
        return MkIs(bRhs, tp);
      } else {
        return Bpl.Expr.True; 
      }

    }

    // This one is only used for guessing, which should be fine for now.
    Expression SubrangeConstraint(IToken tok, Expression e, Type tp) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(tp != null);


      if (tp is NatType) {
        return Expression.CreateAtMost(Expression.CreateIntLiteral(tok, 0), e);
      }
      return null;

    }

    void Check_NewRestrictions(IToken tok, Bpl.Expr obj, Field f, Bpl.Expr rhs, StmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(obj != null);
      Contract.Requires(f != null);
      Contract.Requires(rhs != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      var iter = f.EnclosingClass as IteratorDecl;
      if (iter != null && f == iter.Member_New) {
        // Assignments to an iterator _new field is only allowed to shrink the set, so:
        // assert Set#Subset(rhs, obj._new);
        var fId = new Bpl.IdentifierExpr(tok, GetField(f));
        var subset = FunctionCall(tok, BuiltinFunction.SetSubset, null, rhs, ReadHeap(tok, etran.HeapExpr, obj, fId));
        builder.Add(Assert(tok, subset, "an assignment to " + f.Name + " is only allowed to shrink the set"));
      }
    }

    Bpl.AssumeCmd AssumeGoodHeap(IToken tok, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<AssumeCmd>() != null);

      return new Bpl.AssumeCmd(tok, FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr));
    }

    /// <summary>
    /// Fills in, if necessary, the e.translationDesugaring field, and returns it.
    /// Also, makes sure that letSuchThatExprInfo maps e to something.
    /// </summary>
    Expression LetDesugaring(LetExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(!e.Exact);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (e.translationDesugaring == null) {
        // For let-such-that expression:
        //   var x:X, y:Y :| P(x,y,g); F(...)
        // where g has type G, declare a function for each bound variable:
        //   function $let$x(G): X;
        //   function $let$y(G): Y;
        //   function $let_canCall(G): bool;
        // and add an axiom about these functions:
        //   axiom (forall g:G ::
        //            { $let$x(g) }
        //            { $let$y(g) }
        //            $let$_canCall(g)) ==>
        //            P($let$x(g), $let$y(g), g));
        // and create the desugaring:
        //   var x:X, y:Y := $let$x(g), $let$y(g); F(...)

        // First, determine "g" as a list of Dafny variables FVs plus possibly this, $Heap, and old($Heap)
        LetSuchThatExprInfo info;
        {
          var FVs = new HashSet<IVariable>();
          bool usesHeap = false, usesOldHeap = false;
          Type usesThis = null;
          ComputeFreeVariables(e.RHSs[0], FVs, ref usesHeap, ref usesOldHeap, ref usesThis, false);
          foreach (var bv in e.BoundVars) {
            FVs.Remove(bv);
          }
          var FTVs = new HashSet<TypeParameter>();
          ComputeFreeTypeVariables(e.RHSs[0], FTVs);
          info = new LetSuchThatExprInfo(e.tok, letSuchThatExprInfo.Count, FVs.ToList(), FTVs.ToList(), usesHeap, usesOldHeap, usesThis, currentDeclaration);
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

          sink.TopLevelDeclarations.Add(fn);
        }
        // add canCall function
        {
          Bpl.Variable resType = new Bpl.Formal(e.tok, new Bpl.TypedIdent(e.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
          Bpl.Expr ante;
          List<Variable> formals = info.GAsVars(this, true, out ante, null);
          var fn = new Bpl.Function(e.tok, info.CanCallFunctionName(), formals, resType);

          if (InsertChecksums) {
            InsertChecksum(e.Body, fn);
          }

          sink.TopLevelDeclarations.Add(fn);
        }

        {
          var etranCC = new ExpressionTranslator(this, predef, info.HeapExpr(this, false), info.HeapExpr(this, true));
          Bpl.Expr typeAntecedents;  // later ignored
          List<Variable> gg = info.GAsVars(this, false, out typeAntecedents, etranCC);
          var gExprs = new List<Bpl.Expr>();
          foreach (Bpl.Variable g in gg) {
            gExprs.Add(new Bpl.IdentifierExpr(g.tok, g));
          }
          Bpl.Trigger tr = null;
          Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
          foreach (var bv in e.BoundVars) {
            // create a call to $let$x(g)
            var call = FunctionCall(e.tok, info.SkolemFunctionName(bv), TrType(bv.Type), gExprs);
            tr = new Bpl.Trigger(e.tok, true, new List<Bpl.Expr> { call }, tr);
            substMap.Add(bv, new BoogieWrapper(call, bv.Type));
          }
          var i = info.FTVs.Count + (info.UsesHeap ? 1 : 0) + (info.UsesOldHeap ? 1 : 0);
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
          Bpl.Expr ax = Bpl.Expr.Imp(canCall, etranCC.TrExpr(p));
          ax = BplForall(gg, tr, ax);
          sink.TopLevelDeclarations.Add(new Bpl.Axiom(e.tok, ax));
        }

        // now that we've declared the functions and axioms, let's prepare the let-such-that desugaring
        {
          var etran = new ExpressionTranslator(this, predef, e.tok);
          var rhss = new List<Expression>();
          foreach (var bv in e.BoundVars) {
            var args = info.SkolemFunctionArgs(bv, this, etran);
            var rhs = new BoogieFunctionCall(bv.tok, info.SkolemFunctionName(bv), info.UsesHeap, info.UsesOldHeap, args.Item1, args.Item2);
            rhs.Type = bv.Type;
            rhss.Add(rhs);
          }
          e.translationDesugaring = new LetExpr(e.tok, e.LHSs, rhss, e.Body, true);
          e.translationDesugaring.Type = e.Type;  // resolve here
        }
      }
      return e.translationDesugaring;
    }

    class LetSuchThatExprInfo
    {
      public readonly IToken Tok;
      public readonly int LetId;
      public readonly List<IVariable> FVs;
      public readonly List<Expression> FV_Exprs;  // these are what initially were the free variables, but they may have undergone substitution so they are here Expression's.
      public readonly List<TypeParameter> FTVs;
      public readonly List<Type> FTV_Types;
      public readonly bool UsesHeap;
      public readonly bool UsesOldHeap;
      public readonly Type ThisType;  // null if 'this' is not used
      public LetSuchThatExprInfo(IToken tok, int uniqueLetId, 
      List<IVariable> freeVariables, List<TypeParameter> freeTypeVars,
      bool usesHeap, bool usesOldHeap, Type thisType, Declaration currentDeclaration) {
        Tok = tok;
        LetId = uniqueLetId;
        FTVs = freeTypeVars;
        FTV_Types = Map(freeTypeVars, tt => (Type)new UserDefinedType(tt));
        FVs = freeVariables;
        FV_Exprs = new List<Expression>();
        foreach (var v in FVs) {
          var idExpr = new IdentifierExpr(v.Tok, v.AssignUniqueName(currentDeclaration));
          idExpr.Var = v; idExpr.Type = v.Type;  // resolve here
          FV_Exprs.Add(idExpr);
        }
        UsesHeap = true;  // note, we ignore "usesHeap" and always record it as "true", because various type antecedents need access to the heap (hopefully, this is okay in the contexts in which the let-such-that expression is used)
        UsesOldHeap = usesOldHeap;
        ThisType = thisType;
      }
      public LetSuchThatExprInfo(LetSuchThatExprInfo template, Translator translator,
           Dictionary<IVariable, Expression> substMap,
           Dictionary<TypeParameter, Type> typeMap) {
        Contract.Requires(template != null);
        Contract.Requires(translator != null);
        Contract.Requires(substMap != null);
        Tok = template.Tok;
        LetId = template.LetId;  // reuse the ID, which ensures we get the same $let functions
        FTVs = template.FTVs;
        FTV_Types = template.FTV_Types.ConvertAll(t => Resolver.SubstType(t, typeMap)); 
        FVs = template.FVs;
        FV_Exprs = template.FV_Exprs.ConvertAll(e => translator.Substitute(e, null, substMap, typeMap));
        UsesHeap = template.UsesHeap;
        UsesOldHeap = template.UsesOldHeap;
        ThisType = template.ThisType;
      }
      public Tuple<List<Expression>, List<Type>> SkolemFunctionArgs(BoundVar bv, Translator translator, ExpressionTranslator etran) {
        Contract.Requires(bv != null);
        Contract.Requires(translator != null);
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
      public Bpl.Expr CanCallFunctionCall(Translator translator, ExpressionTranslator etran) {
        Contract.Requires(translator != null);
        Contract.Requires(etran != null);
        var gExprs = new List<Bpl.Expr>();
        gExprs.AddRange(Map(FTV_Types, tt => translator.TypeToTy(tt)));
        if (UsesHeap) {
          gExprs.Add(etran.HeapExpr);
        }
        if (UsesOldHeap) {
          gExprs.Add(etran.Old.HeapExpr);
        }
        if (ThisType != null) {
          var th = new Bpl.IdentifierExpr(Tok, etran.This, translator.predef.RefType);
          gExprs.Add(th);
        }
        foreach (var v in FV_Exprs) {
          gExprs.Add(etran.TrExpr(v));
        }
        return translator.FunctionCall(Tok, CanCallFunctionName(), Bpl.Type.Bool, gExprs);
      }
      public string CanCallFunctionName() {
        return string.Format("$let#{0}$canCall", LetId);
      }
      public Bpl.Expr HeapExpr(Translator translator, bool old) {
        Contract.Requires(translator != null);
        return new Bpl.IdentifierExpr(Tok, old ? "$heap$old" : "$heap", translator.predef.HeapType);
      }
      /// <summary>
      /// "wantFormals" means the returned list will consist of all in-parameters.
      /// "!wantFormals" means the returned list will consist of all bound variables.
      /// Guarantees that, in the list returned, "this" is the parameter immediately following
      /// the (0, 1, or 2) heap arguments, if there is a "this" parameter at all.
      /// Note, "typeAntecedents" is meaningfully filled only if "etran" is not null.
      /// </summary>
      public List<Variable> GAsVars(Translator translator, bool wantFormals, out Bpl.Expr typeAntecedents, ExpressionTranslator etran) {
        Contract.Requires(translator != null);
        var vv = new List<Variable>();
        // first, add the type variables
        vv.AddRange(Map(FTVs, tp => NewVar(nameTypeParam(tp), translator.predef.Ty, wantFormals)));
        typeAntecedents = Bpl.Expr.True;
        if (UsesHeap) {
          var nv = NewVar("$heap", translator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var isGoodHeap = translator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        if (UsesOldHeap) {
          var nv = NewVar("$heap$old", translator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var isGoodHeap = translator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        if (ThisType != null) {
          var nv = NewVar("this", translator.TrType(ThisType), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var th = new Bpl.IdentifierExpr(Tok, nv);
            typeAntecedents = BplAnd(typeAntecedents, Bpl.Expr.Neq(th, translator.predef.Null));
            var wh = translator.GetWhereClause(Tok, th, ThisType, etran);
            if (wh != null) {
              typeAntecedents = BplAnd(typeAntecedents, wh);
            }
          }
        }
        foreach (var v in FVs) {
          var nv = NewVar(v.Name, translator.TrType(v.Type), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var wh = translator.GetWhereClause(Tok, new Bpl.IdentifierExpr(Tok, nv), v.Type, etran);
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
    private Declaration currentDeclaration;

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

    internal class BoogieFunctionCall : Expression
    {
      public readonly string FunctionName;
      public readonly bool UsesHeap;
      public readonly bool UsesOldHeap;
      public readonly List<Type> TyArgs; // Note: also has a bunch of type arguments 
      public readonly List<Expression> Args;
      public BoogieFunctionCall(IToken tok, string functionName, bool usesHeap, bool usesOldHeap, List<Expression> args, List<Type> tyArgs)
        : base(tok)
      {
        Contract.Requires(tok != null);
        Contract.Requires(functionName != null);
        Contract.Requires(args != null);
        FunctionName = functionName;
        UsesHeap = usesHeap;
        UsesOldHeap = usesOldHeap;
        Args = args;
        TyArgs = tyArgs;
      }
      public override IEnumerable<Expression> SubExpressions {
        get {
          foreach (var v in Args) {
            yield return v;
          }
        }
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
      public readonly Bpl.Expr layerInterCluster;     
      public readonly Bpl.Expr layerIntraCluster = null;  // a value of null says to do the same as for inter-cluster calls
      public int Statistics_CustomLayerFunctionCount = 0;
      public readonly bool ProducingCoCertificates = false;
      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(HeapExpr != null);
        Contract.Invariant(HeapExpr is Bpl.OldExpr || HeapExpr is Bpl.IdentifierExpr);
        Contract.Invariant(predef != null);
        Contract.Invariant(translator != null);
        Contract.Invariant(This != null);
        Contract.Invariant(modifiesFrame != null);
        Contract.Invariant(layerInterCluster != null);
        Contract.Invariant(0 <= Statistics_CustomLayerFunctionCount);
      }

      /// <summary>
      /// This is a general constructor, but takes the layerInterCluster as an int.
      /// </summary>
      ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, int layerInterCluster, Bpl.Expr layerIntraCluster, string modifiesFrame) {

        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(0 <= layerInterCluster);
        Contract.Requires(modifiesFrame != null);

        this.translator = translator;
        this.predef = predef;
        this.HeapExpr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimited_CurrentFunction;
        this.layerInterCluster = LayerN(layerInterCluster);
        this.layerIntraCluster = layerIntraCluster;
        this.modifiesFrame = modifiesFrame;
      }

      /// <summary>
      /// This is the most general constructor.  It is private and takes all the parameters.  Whenever
      /// one ExpressionTranslator is constructed from another, unchanged parameters are just copied in.
      /// </summary>
      ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, Bpl.Expr layerInterCluster, Bpl.Expr layerIntraCluster, string modifiesFrame) {

        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(layerInterCluster != null);
        Contract.Requires(modifiesFrame != null);

        this.translator = translator;
        this.predef = predef;
        this.HeapExpr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimited_CurrentFunction;
        this.layerInterCluster = layerInterCluster;
        if (layerIntraCluster == null) {
          this.layerIntraCluster = layerInterCluster;
        } else {
          this.layerIntraCluster = layerIntraCluster;
        }
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
        : this(translator, predef, heap, thisVar, null, 1, null, "$_Frame") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(heap != null);
        Contract.Requires(thisVar != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, Bpl.Expr heap) 
        : this(etran.translator, etran.predef, heap, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, etran.modifiesFrame)
      {
        Contract.Requires(etran != null);
        Contract.Requires(heap != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, string modifiesFrame)
        : this(etran.translator, etran.predef, etran.HeapExpr, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, modifiesFrame) {
        Contract.Requires(etran != null);
        Contract.Requires(modifiesFrame != null);
      }

      ExpressionTranslator oldEtran;
      public ExpressionTranslator Old {
        get {
          Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

          if (oldEtran == null) {
            oldEtran = new ExpressionTranslator(translator, predef, new Bpl.OldExpr(HeapExpr.tok, HeapExpr), This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame);
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

      public ExpressionTranslator WithLayer(Bpl.Expr layerArgument) 
      {
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return new ExpressionTranslator(translator, predef, HeapExpr, This, null, layerArgument, layerArgument, modifiesFrame);
      }

      public ExpressionTranslator LimitedFunctions(Function applyLimited_CurrentFunction, Bpl.Expr layerArgument) {
        Contract.Requires(applyLimited_CurrentFunction != null);
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return new ExpressionTranslator(translator, predef, HeapExpr, This, applyLimited_CurrentFunction, /* layerArgument */ layerInterCluster, layerArgument, modifiesFrame);
      }

      public ExpressionTranslator LayerOffset(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        var et = new ExpressionTranslator(translator, predef, HeapExpr, This, applyLimited_CurrentFunction, translator.LayerSucc(layerInterCluster, offset), layerIntraCluster, modifiesFrame);
        if (this.oldEtran != null) {
          var etOld = new ExpressionTranslator(translator, predef, Old.HeapExpr, This, applyLimited_CurrentFunction, translator.LayerSucc(layerInterCluster, offset), layerIntraCluster, modifiesFrame);
          etOld.oldEtran = etOld;
          et.oldEtran = etOld;
        }
        return et;
      }

      public Bpl.IdentifierExpr TheFrame(IToken tok)
      {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);

        Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "beta");
        Bpl.Type fieldAlpha = predef.FieldName(tok, alpha);
        Bpl.Type ty = new Bpl.MapType(tok, new List<TypeVariable> { alpha }, new List<Bpl.Type> { predef.RefType, fieldAlpha }, Bpl.Type.Bool);
        return new Bpl.IdentifierExpr(tok, this.modifiesFrame, ty);
      }

      public Bpl.IdentifierExpr Tick() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$Tick", predef.TickType);
      }

      public Bpl.IdentifierExpr ArbitraryBoxValue() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$ArbitraryBoxValue", predef.BoxType);
      }
      public Bpl.Expr ArbitraryValue(Type type) {
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        var bx = ArbitraryBoxValue();
        if (!ModeledAsBoxType(type)) {
          return translator.FunctionCall(Token.NoToken, BuiltinFunction.Unbox, translator.TrType(type), bx);
        } else {
          return bx;
        }
      }

      public Bpl.Expr LayerZero() {
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$LZ", predef.LayerType);
      }

      public Bpl.Expr LayerN(int n) {
        Contract.Requires(0 <= n);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return translator.LayerSucc(LayerZero(), n);
      }

      public Bpl.IdentifierExpr ModuleContextHeight() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$ModuleContextHeight", Bpl.Type.Int);
      }

      public Bpl.IdentifierExpr FunctionContextHeight() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$FunctionContextHeight", Bpl.Type.Int);
      }

      public Bpl.Expr HeightContext(ICallable m)
      {
        Contract.Requires(m != null);
        // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
        var module = m.EnclosingModule;
        Bpl.Expr context = Bpl.Expr.And(
          Bpl.Expr.Eq(Bpl.Expr.Literal(module.Height), ModuleContextHeight()),
          Bpl.Expr.Eq(Bpl.Expr.Literal(module.CallGraph.GetSCCRepresentativeId(m)), FunctionContextHeight()));
        return context;
      }

      public Expression GetSubstitutedBody(LetExpr e)
      {
        Contract.Requires(e != null);
        Contract.Requires(e.Exact);
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < e.LHSs.Count; i++) {
          translator.AddCasePatternVarSubstitutions(e.LHSs[i], TrExpr(e.RHSs[i]), substMap);
        }
        return translator.Substitute(e.Body, null, substMap);
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
            return translator.Lit(new Bpl.LiteralExpr(e.tok, (bool)e.Value));
          } else if (e.Value is BigInteger) {
            return translator.Lit(Bpl.Expr.Literal(Microsoft.Basetypes.BigNum.FromBigInt((BigInteger)e.Value)));
          } else if (e.Value is Basetypes.BigDec) {
            return translator.Lit(Bpl.Expr.Literal((Basetypes.BigDec)e.Value));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
          }

        } else if (expr is ThisExpr) {
          return new Bpl.IdentifierExpr(expr.tok, This, predef.RefType);

        } else if (expr is IdentifierExpr) {
          IdentifierExpr e = (IdentifierExpr)expr;
          Contract.Assert(e.Var != null);
          return translator.TrVar(expr.tok, e.Var);

        } else if (expr is BoogieWrapper) {
          var e = (BoogieWrapper)expr;
          return e.Expr;


        } else if (expr is BoogieFunctionCall) {
          var e = (BoogieFunctionCall)expr;
          var id = new Bpl.IdentifierExpr(e.tok, e.FunctionName, translator.TrType(e.Type));
          var args = new List<Bpl.Expr>();
          foreach (var arg in e.TyArgs) {
            args.Add(translator.TypeToTy(arg));
          }
          if (e.UsesHeap) {
            args.Add(HeapExpr);
          }
          if (e.UsesOldHeap) {
            args.Add(Old.HeapExpr);
          }
          foreach (var arg in e.Args) {
            args.Add(TrExpr(arg));
          }
          return new Bpl.NAryExpr(e.tok, new Bpl.FunctionCall(id), args);

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
          bool isLit = true;
           foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Bpl.Expr elt = BoxIfNecessary(expr.tok, rawElement, ee.Type);
            s = translator.FunctionCall(expr.tok, BuiltinFunction.SeqBuild, predef.BoxType, s, elt);
          }
          if (isLit) {
            s = translator.Lit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MapDisplayExpr) {
          MapDisplayExpr e = (MapDisplayExpr)expr;
          Bpl.Type maptype = predef.MapType(expr.tok, predef.BoxType, predef.BoxType);
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.MapEmpty, predef.BoxType);
          foreach (ExpressionPair p in e.Elements) {
            Bpl.Expr elt = BoxIfNecessary(expr.tok, TrExpr(p.A), cce.NonNull(p.A.Type));
            Bpl.Expr elt2 = BoxIfNecessary(expr.tok, TrExpr(p.B), cce.NonNull(p.B.Type));
            s = translator.FunctionCall(expr.tok, "Map#Build", maptype, s, elt, elt2);
          }
          return s;

        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          return e.MemberSelectCase(
            field => {
              Bpl.Expr obj = TrExpr(e.Obj);
              Bpl.Expr result;
              if (field.IsMutable) {
                result = ReadHeap(expr.tok, HeapExpr, obj, new Bpl.IdentifierExpr(expr.tok, translator.GetField(field)));
                return translator.CondApplyUnbox(expr.tok, result, field.Type, expr.Type);
              } else {
                result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(translator.GetReadonlyField(field)),
                  new List<Bpl.Expr> {obj});
                result = translator.CondApplyUnbox(expr.tok, result, field.Type, expr.Type);
                if (translator.IsLit(obj)) {
                  result = translator.Lit(result, translator.TrType(expr.Type));
                }
                return result;
              }
            },
            fn => {
              var args = new List<Bpl.Expr>();
              args.AddRange(e.TypeApplication.ConvertAll(translator.TypeToTy));
              if (fn.IsRecursive) {
                args.Add(layerInterCluster);
              }
              if (!fn.IsStatic) {
                args.Add(/* translator.BoxIfUnboxed */(TrExpr(e.Obj)/*, e.Type */));
              }
              return translator.FunctionCall(e.tok, translator.FunctionHandle(fn), predef.HandleType, args);
            });
        } else if (expr is SeqSelectExpr) {
          SeqSelectExpr e = (SeqSelectExpr)expr;
          Bpl.Expr seq = TrExpr(e.Seq);
          var seqType = e.Seq.Type.NormalizeExpand();
          Type elmtType = null;
          Type domainType = null;
          Contract.Assert(seqType != null);  // the expression has been successfully resolved
          if (seqType.IsArrayType) {
            domainType = Type.Int;
            elmtType = UserDefinedType.ArrayElementType(seqType);
          } else if (seqType is SeqType) {
            domainType = Type.Int;
            elmtType = ((SeqType)seqType).Arg;
          } else if (seqType is MapType) {
            domainType = ((MapType)seqType).Domain;
            elmtType = ((MapType)seqType).Range;
          } else if (seqType is MultiSetType) {
            domainType = ((MultiSetType)seqType).Arg;
            elmtType = Type.Int;
          } else { Contract.Assert(false); }
          Bpl.Type elType = translator.TrType(elmtType);
          Bpl.Type dType = translator.TrType(domainType);
          Bpl.Expr e0 = e.E0 == null ? null : TrExpr(e.E0);
          Bpl.Expr e1 = e.E1 == null ? null : TrExpr(e.E1);
          if (e.SelectOne) {
            Contract.Assert(e1 == null);
            Bpl.Expr x;
            if (seqType.IsArrayType) {
              Bpl.Expr fieldName = translator.FunctionCall(expr.tok, BuiltinFunction.IndexField, null, e0);
              x = ReadHeap(expr.tok, HeapExpr, TrExpr(e.Seq), fieldName);
            } else if (seqType is SeqType) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.BoxType, seq, e0);
            } else if (seqType is MapType) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.MapElements, predef.MapType(e.tok, predef.BoxType, predef.BoxType), seq);
              x = Bpl.Expr.Select(x, BoxIfNecessary(e.tok, e0, domainType));
            } else if (seqType is MultiSetType) {
              x = Bpl.Expr.SelectTok(expr.tok, TrExpr(e.Seq), BoxIfNecessary(expr.tok, e0, domainType));
            } else { Contract.Assert(false); x = null; }
            if (!ModeledAsBoxType(elmtType) && !(seqType is MultiSetType)) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, elType, x);
            }
            return x;
          } else {
            if (seqType.IsArrayType) {
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqFromArray, elType, HeapExpr, seq);
            }
            var isLit = translator.IsLit(seq);
            if (e1 != null) {
              isLit = isLit && translator.IsLit(e1);
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqTake, elType, seq, e1);
            }
            if (e0 != null) {
              isLit = isLit && translator.IsLit(e0);
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqDrop, elType, seq, e0);
            }
            // if e0 == null && e1 == null, then we have the identity operation seq[..] == seq;
            if (isLit && (e0 != null || e1 != null)) {
              // Lit-lift the expression
              seq = translator.Lit(seq, translator.TrType(expr.Type));
            }
            return seq;
          }

        } else if (expr is SeqUpdateExpr) {
          SeqUpdateExpr e = (SeqUpdateExpr)expr;
          if (e.ResolvedUpdateExpr != null)
          {
            return TrExpr(e.ResolvedUpdateExpr);
          }
          else
          {
            Bpl.Expr seq = TrExpr(e.Seq);
            var seqType = e.Seq.Type.NormalizeExpand();
            if (seqType is SeqType)
            {
              Type elmtType = cce.NonNull((SeqType)seqType).Arg;
              Bpl.Expr index = TrExpr(e.Index);
              Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), elmtType);
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqUpdate, predef.BoxType, seq, index, val);
            }
            else if (seqType is MapType)
            {
              MapType mt = (MapType)seqType;
              Bpl.Type maptype = predef.MapType(expr.tok, predef.BoxType, predef.BoxType);
              Bpl.Expr index = BoxIfNecessary(expr.tok, TrExpr(e.Index), mt.Domain);
              Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), mt.Range);
              return translator.FunctionCall(expr.tok, "Map#Build", maptype, seq, index, val);
            }
            else if (seqType is MultiSetType)
            {
              Type elmtType = cce.NonNull((MultiSetType)seqType).Arg;
              Bpl.Expr index = BoxIfNecessary(expr.tok, TrExpr(e.Index), elmtType);
              Bpl.Expr val = TrExpr(e.Value);
              return Bpl.Expr.StoreTok(expr.tok, seq, index, val);
            }
            else
            {
              Contract.Assert(false);
              throw new cce.UnreachableException();
            }
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

        } else if (expr is ApplyExpr) {
          ApplyExpr e = (ApplyExpr)expr;
          int arity = e.Args.Count;
          var tt = e.Function.Type as ArrowType;
          Contract.Assert(tt != null);
          Contract.Assert(tt.Arity == arity);

          {
            // optimisation: if this could have just as well been a FunctionCallExpr, call it as such!
            var con = e.Function as ConcreteSyntaxExpression;
            var recv = con == null ? e.Function : con.Resolved;
            var mem = recv as MemberSelectExpr;
            var fn = mem == null ? null : mem.Member as Function;
            if (fn != null) {
              return TrExpr(new FunctionCallExpr(e.tok, fn.Name, mem.Obj, e.OpenParen, e.Args) {
                Function = fn,
                Type = e.Type,
                TypeArgumentSubstitutions = Util.Dict(GetTypeParams(fn), mem.TypeApplication)
              });
            }
          }

          Func<Expression, Bpl.Expr> TrArg = arg => translator.BoxIfUnboxed(TrExpr(arg), arg.Type);

          var applied = translator.FunctionCall(expr.tok, translator.Apply(arity), predef.BoxType, 
            Concat(Map(tt.TypeArgs,translator.TypeToTy),
            Cons(TrExpr(e.Function), Cons(HeapExpr, e.Args.ConvertAll(arg => TrArg(arg))))));

          return translator.UnboxIfBoxed(applied, tt.Result);

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          Bpl.Expr layerArgument;
          if (e.Function.IsRecursive) {
            Statistics_CustomLayerFunctionCount++;
            ModuleDefinition module = e.Function.EnclosingClass.Module;
            if (this.applyLimited_CurrentFunction != null &&
              this.layerIntraCluster != null &&
              ModuleDefinition.InSameSCC(e.Function, applyLimited_CurrentFunction)) {
              layerArgument = this.layerIntraCluster;
            } else {
              layerArgument = this.layerInterCluster;
            }
          } else {
            layerArgument = null;
          }

          var ty = translator.TrType(e.Type);
          var id = new Bpl.IdentifierExpr(e.tok, e.Function.FullSanitizedName, ty);
          bool returnLit;
          var args = FunctionInvocationArguments(e, layerArgument, out returnLit);

          Expr result = new Bpl.NAryExpr(e.tok, new Bpl.FunctionCall(id), args);
          result = translator.CondApplyUnbox(e.tok, result, e.Function.ResultType, e.Type);
          if (returnLit && !translator.IsOpaqueFunction(e.Function)) {
            result = translator.Lit(result, ty);
          }
          return result;
        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
          List<Bpl.Expr> args = new List<Bpl.Expr>();
          bool isLit = true;
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Expression arg = dtv.Arguments[i];
            Type t = dtv.Ctor.Formals[i].Type;
            var bArg = TrExpr(arg);
            isLit = isLit && translator.IsLit(bArg);
            args.Add(translator.CondApplyBox(expr.tok, bArg, cce.NonNull(arg.Type), t));
          }
          Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(dtv.tok, dtv.Ctor.FullName, predef.DatatypeType);
          Bpl.Expr ret = new Bpl.NAryExpr(dtv.tok, new Bpl.FunctionCall(id), args);
          if (isLit) {
            ret = translator.Lit(ret, predef.DatatypeType);
          }
          return ret;
        } else if (expr is OldExpr) {
          OldExpr e = (OldExpr)expr;
          return Old.TrExpr(e.E);

        } else if (expr is MultiSetFormingExpr) {
          MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
          var eType = e.E.Type.NormalizeExpand();
          if (eType is SetType) {
            return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetFromSet, translator.TrType(cce.NonNull((SetType)eType).Arg), TrExpr(e.E));
          } else if (eType is SeqType) {
            return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetFromSeq, translator.TrType(cce.NonNull((SeqType)eType).Arg), TrExpr(e.E));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();
          }

        } else if (expr is UnaryOpExpr) {
          var e = (UnaryOpExpr)expr;
          Bpl.Expr arg = TrExpr(e.E);
          switch (e.Op) {
            case UnaryOpExpr.Opcode.Lit:
              return translator.Lit(arg);
            case UnaryOpExpr.Opcode.Not:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
            case UnaryOpExpr.Opcode.Cardinality:
              var eType = e.E.Type.NormalizeExpand();
              if (eType is SeqType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, arg);
              } else if (eType is SetType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.SetCard, null, arg);
              } else if (eType is MultiSetType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetCard, null, arg);
              } else if (eType is MapType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.MapCard, null, arg);
              } else {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected sized type
              }
            case UnaryOpExpr.Opcode.Fresh:
              var eeType = e.E.Type.NormalizeExpand();
              if (eeType is SetType) {
                // generate:  (forall $o: ref :: $o != null && X[Box($o)] ==> !old($Heap)[$o,alloc])
                // TODO: trigger?
                Bpl.Variable oVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$o", predef.RefType));
                Bpl.Expr o = new Bpl.IdentifierExpr(expr.tok, oVar);
                Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
                Bpl.Expr oInSet = TrInSet(expr.tok, o, e.E, ((SetType)eeType).Arg);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, o));
                Bpl.Expr body = Bpl.Expr.Imp(Bpl.Expr.And(oNotNull, oInSet), oIsFresh);
                return new Bpl.ForallExpr(expr.tok, new List<Variable> { oVar }, body);
              } else if (eeType is SeqType) {
                // generate:  (forall $i: int :: 0 <= $i && $i < Seq#Length(X) && Unbox(Seq#Index(X,$i)) != null ==> !old($Heap)[Unbox(Seq#Index(X,$i)),alloc])
                // TODO: trigger?
                Bpl.Variable iVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$i", Bpl.Type.Int));
                Bpl.Expr i = new Bpl.IdentifierExpr(expr.tok, iVar);
                Bpl.Expr iBounds = translator.InSeqRange(expr.tok, i, TrExpr(e.E), true, null, false);
                Bpl.Expr XsubI = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.RefType, TrExpr(e.E), i);
                XsubI = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, predef.RefType, XsubI);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, XsubI));
                Bpl.Expr xsubiNotNull = Bpl.Expr.Neq(XsubI, predef.Null);
                Bpl.Expr body = Bpl.Expr.Imp(Bpl.Expr.And(iBounds, xsubiNotNull), oIsFresh);
                return new Bpl.ForallExpr(expr.tok, new List<Variable> { iVar }, body);
              } else if (eeType.IsDatatype) {
                // translator.FunctionCall(e.tok, BuiltinFunction.DtAlloc, null, TrExpr(e.E), Old.HeapExpr);
                Bpl.Expr alloc = translator.MkIsAlloc(TrExpr(e.E), eeType, Old.HeapExpr);
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, alloc);
              } else {
                // generate:  x != null && !old($Heap)[x]
                Bpl.Expr oNull = Bpl.Expr.Neq(TrExpr(e.E), predef.Null);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, TrExpr(e.E)));
                return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And, oNull, oIsFresh);
              }
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
          }

        } else if (expr is ConversionExpr) {
          var e = (ConversionExpr)expr;
          Bpl.ArithmeticCoercion.CoercionType ct;
          if (e.ToType is IntType) {
            if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int)) {
              return TrExpr(e.E);
            }
            ct = Bpl.ArithmeticCoercion.CoercionType.ToInt;
          } else if (e.ToType is RealType) {
            if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
              return TrExpr(e.E);
            }
            ct = Bpl.ArithmeticCoercion.CoercionType.ToReal;
          } else {
            Contract.Assert(false);  // unexpected ConversionExpr to-type
            ct = Bpl.ArithmeticCoercion.CoercionType.ToInt;  // please compiler
          }
          return new Bpl.NAryExpr(e.tok, new ArithmeticCoercion(e.tok, ct), new List<Expr> { TrExpr(e.E) });

        } else if (expr is BinaryExpr) {
          BinaryExpr e = (BinaryExpr)expr;
          bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuation.Real);
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
          Bpl.Type typ;
          var oe0 = e0;
          var oe1 = e1;
          var lit0 = translator.GetLit(e0);
          var lit1 = translator.GetLit(e1);
          bool liftLit = lit0 != null && lit1 != null;
          // NOTE(namin): We usually avoid keeping literals, because their presence might mess up triggers that do not expect them.
          //              Still for equality-related operations, it's useful to keep them instead of lifting them, so that they can be propagated.
          bool keepLits = false;
          if (lit0 != null) {
            e0 = lit0;
          }
          if (lit1 != null) {
            e1 = lit1;
          }
          switch (e.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Iff:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Iff; break;
            case BinaryExpr.ResolvedOpcode.Imp:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Imp; break;
            case BinaryExpr.ResolvedOpcode.And:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.And; break;
            case BinaryExpr.ResolvedOpcode.Or:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Or; break;

            case BinaryExpr.ResolvedOpcode.EqCommon:
              keepLits = true;
              var cot = e.E0.Type.AsCoDatatype;
              if (cot != null) {
                var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                return translator.CoEqualCall(cot, e0args, e1args, null, LayerN(2), e0, e1, expr.tok);
              }
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Eq; break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
              var cotx = e.E0.Type.AsCoDatatype;
              if (cotx != null) {
                var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                var x = translator.CoEqualCall(cotx, e0args, e1args, null, LayerN(2), e0, e1, expr.tok);
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, x);
              }
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Neq; break;

            case BinaryExpr.ResolvedOpcode.Lt:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Lt; break;
            case BinaryExpr.ResolvedOpcode.Le:
              keepLits = true;
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Le; break;
            case BinaryExpr.ResolvedOpcode.Ge:
              keepLits = true;
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Ge; break;
            case BinaryExpr.ResolvedOpcode.Gt:
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Gt; break;
            case BinaryExpr.ResolvedOpcode.Add:
              typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
              bOpcode = BinaryOperator.Opcode.Add; break;
            case BinaryExpr.ResolvedOpcode.Sub:
              typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
              bOpcode = BinaryOperator.Opcode.Sub; break;
            case BinaryExpr.ResolvedOpcode.Mul:
              typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
              bOpcode = BinaryOperator.Opcode.Mul; break;
            case BinaryExpr.ResolvedOpcode.Div:
              if (isReal) {
                typ = Bpl.Type.Real;
                bOpcode = BinaryOperator.Opcode.RealDiv; break;
              } else {
                typ = Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Div; break;
              }
            case BinaryExpr.ResolvedOpcode.Mod:
              typ = Bpl.Type.Int;
              bOpcode = BinaryOperator.Opcode.Mod; break;

            case BinaryExpr.ResolvedOpcode.SetEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.SetNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.SetEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperSubset:
              return translator.ProperSubset(expr.tok, e0, e1);
            case BinaryExpr.ResolvedOpcode.Subset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.Superset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetSubset, null, e1, e0);
            case BinaryExpr.ResolvedOpcode.ProperSuperset:
              return translator.ProperSubset(expr.tok, e1, e0);
            case BinaryExpr.ResolvedOpcode.Disjoint:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetDisjoint, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.InSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.Union:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetUnion, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.Intersection:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetIntersection, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SetDifference, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);

            case BinaryExpr.ResolvedOpcode.MultiSetEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.MapEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MapEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MapNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.MapEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
              return translator.ProperMultiset(expr.tok, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSubset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSuperset:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetSubset, null, e1, e0);
            case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
              return translator.ProperMultiset(expr.tok, e1, e0);
            case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetDisjoint, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.InMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInMultiSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetUnion, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetIntersection, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);
            case BinaryExpr.ResolvedOpcode.MultiSetDifference:
              return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetDifference, translator.TrType(expr.Type.AsMultiSetType.Arg), e0, e1);

            case BinaryExpr.ResolvedOpcode.SeqEq:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqEqual, null, e0, e1);
            case BinaryExpr.ResolvedOpcode.SeqNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.FunctionCall(expr.tok, BuiltinFunction.SeqEqual, null, e0, e1));
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              return translator.ProperPrefix(expr.tok, e0, e1);
            case BinaryExpr.ResolvedOpcode.Prefix:
              {
                Bpl.Expr len0 = translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, e0);
                Bpl.Expr len1 = translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, e1);
                return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And,
                  Bpl.Expr.Le(len0, len1),
                  translator.FunctionCall(expr.tok, BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
              }
            case BinaryExpr.ResolvedOpcode.Concat:
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqAppend, translator.TrType(expr.Type.AsSeqType.Arg), e0, e1);
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
                translator.FunctionCall(expr.tok, e.E0.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, e0),
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e1));
            case BinaryExpr.ResolvedOpcode.RankGt:
              return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.Gt,
                translator.FunctionCall(expr.tok, BuiltinFunction.DtRank, null, e0),
                translator.FunctionCall(expr.tok, e.E1.Type.IsDatatype ? BuiltinFunction.DtRank: BuiltinFunction.BoxRank, null, e1));

            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected binary expression
          }
          liftLit = liftLit && !keepLits;
          var ae0 = keepLits ? oe0 : e0;
          var ae1 = keepLits ? oe1 : e1;
          Bpl.Expr re = Bpl.Expr.Binary(expr.tok, bOpcode, ae0, ae1);
          if (liftLit) {
            re = translator.Lit(re, typ);
          }
          return re;
        } else if (expr is TernaryExpr) {
          var e = (TernaryExpr)expr;
          var e0 = TrExpr(e.E0);
          var e1 = TrExpr(e.E1);
          var e2 = TrExpr(e.E2);
          switch (e.Op) {
            case TernaryExpr.Opcode.PrefixEqOp:
            case TernaryExpr.Opcode.PrefixNeqOp:
              var e1type = e.E1.Type.NormalizeExpand();
              var e2type = e.E2.Type.NormalizeExpand();
              var cot = e1type.AsCoDatatype;
              Contract.Assert(cot != null);  // the argument types of prefix equality (and prefix disequality) are codatatypes
              var r = translator.CoEqualCall(cot, e1type.TypeArgs, e2type.TypeArgs, e0, LayerN(2), e1, e2);
              if (e.Op == TernaryExpr.Opcode.PrefixEqOp) {
                return r;
              } else {
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, r);
              }
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected ternary expression
          }
        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          if (e.Exact) {
            return TrExpr(GetSubstitutedBody(e));
          } else {
            var d = translator.LetDesugaring(e);
            return TrExpr(d);
          }
        } else if (expr is NamedExpr) {
          return TrExpr(((NamedExpr)expr).Body);
        } else if (expr is QuantifierExpr) {
          QuantifierExpr e = (QuantifierExpr)expr;
          List<Variable> tyvars = translator.MkTyParamBinders(e.TypeArgs);
          List<Variable> bvars = new List<Variable>();

          var initEtran = this;
          var bodyEtran = this;
          bool _scratch = true;

          Bpl.Expr antecedent = Bpl.Expr.True;

          if (Attributes.ContainsBool(e.Attributes, "layerQuantifier", ref _scratch)) {
            // If this is a layer quantifier, quantify over layers here, and use $LS(ly) layers in the translation of the body
            var ly = BplBoundVar(e.Refresh("$ly", ref translator.otherTmpVarCount), predef.LayerType, bvars);
            Expr layer = translator.LayerSucc(ly); 
            bodyEtran = new ExpressionTranslator(translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layer, layer, modifiesFrame);
          }
          if (Attributes.ContainsBool(e.Attributes, "heapQuantifier", ref _scratch)) {
            var h = BplBoundVar(e.Refresh("$heap", ref translator.otherTmpVarCount), predef.HeapType, bvars);
            bodyEtran = new ExpressionTranslator(bodyEtran, h);
            antecedent = BplAnd(new List<Bpl.Expr> {
              antecedent,
              translator.FunctionCall(e.tok, BuiltinFunction.IsGoodHeap, null, h),
              translator.HeapSameOrSucc(initEtran.HeapExpr, h)
            });
          }

          antecedent = BplAnd(antecedent, bodyEtran.TrBoundVariables(e.BoundVars, bvars));

          Bpl.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
          Bpl.Trigger tr = null;
          for (Attributes aa = e.Attributes; aa != null; aa = aa.Prev) {
            if (aa.Name == "trigger") {
              List<Bpl.Expr> tt = new List<Bpl.Expr>();
              foreach (var arg in aa.Args) {
                if (arg.E == null) {
                  Console.WriteLine("Warning: string argument to 'trigger' attribute ignored");
                } else {
                  tt.Add(bodyEtran.TrExpr(arg.E));
                }
              }
              tr = new Bpl.Trigger(expr.tok, true, tt, tr);
            } 
          }
          if (e.Range != null) {
            antecedent = BplAnd(antecedent, bodyEtran.TrExpr(e.Range));
          }
          Bpl.Expr body = bodyEtran.TrExpr(e.Term);

          if (e is ForallExpr) {
            return new Bpl.ForallExpr(expr.tok, new List<TypeVariable>(), Concat(tyvars,bvars), kv, tr, Bpl.Expr.Imp(antecedent, body));
          } else {
            Contract.Assert(e is ExistsExpr);
            return new Bpl.ExistsExpr(expr.tok, new List<TypeVariable>(), Concat(tyvars,bvars), kv, tr, Bpl.Expr.And(antecedent, body));
          }

        } else if (expr is SetComprehension) {
          var e = (SetComprehension)expr;
          // Translate "set xs | R :: T" into "lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))".
          List<Variable> bvars = new List<Variable>();
          Bpl.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars);
          Bpl.QKeyValue kv = TrAttributes(e.Attributes, null);

          var yVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$y#" + translator.otherTmpVarCount, predef.BoxType));
          translator.otherTmpVarCount++;
          Bpl.Expr y = new Bpl.IdentifierExpr(expr.tok, yVar);

          var eq = Bpl.Expr.Eq(y, BoxIfNecessary(expr.tok, TrExpr(e.Term), e.Term.Type));
          var ebody = Bpl.Expr.And(BplAnd(typeAntecedent, TrExpr(e.Range)), eq);
          var exst = new Bpl.ExistsExpr(expr.tok, bvars, ebody);

          return new Bpl.LambdaExpr(expr.tok, new List<TypeVariable>(), new List<Variable> { yVar }, kv, exst);

        } else if (expr is MapComprehension) {
          var e = (MapComprehension)expr;
          // Translate "map x | R :: T" into
          // Map#Glue(lambda y: BoxType :: [unbox(y)/x]R,
          //          lambda y: BoxType :: [unbox(y)/x]T)".
          List<Variable> bvars = new List<Variable>();
          var bv = e.BoundVars[0];
          TrBoundVariables(e.BoundVars, bvars);

          Bpl.QKeyValue kv = TrAttributes(e.Attributes, null);

          var yVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$y#" + translator.otherTmpVarCount, predef.BoxType));
          translator.otherTmpVarCount++;

          Bpl.Expr unboxy = translator.UnboxIfBoxed(new Bpl.IdentifierExpr(expr.tok, yVar), bv.Type);
          Bpl.Expr typeAntecedent = translator.GetWhereClause(bv.tok, unboxy, bv.Type, this);


          Dictionary<IVariable, Expression> subst = new Dictionary<IVariable,Expression>();
          subst.Add(e.BoundVars[0], new BoogieWrapper(unboxy,e.BoundVars[0].Type));

          var ebody = BplAnd(typeAntecedent ?? Bpl.Expr.True, TrExpr(translator.Substitute(e.Range, null, subst)));
          Bpl.Expr l1 = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { yVar }, kv, ebody);
          ebody = TrExpr(translator.Substitute(e.Term, null, subst));
          Bpl.Expr l2 = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { yVar }, kv, BoxIfNecessary(expr.tok, ebody, e.Term.Type));


          return translator.FunctionCall(e.tok, BuiltinFunction.MapGlue, null, l1, l2);

        } else if (expr is LambdaExpr) {
          var e = (LambdaExpr)expr;

          return TrLambdaExpr(e);
        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          return TrExpr(e.E);

        } else if (expr is ITEExpr) {
          ITEExpr e = (ITEExpr)expr;
          var g = translator.RemoveLit(TrExpr(e.Test));
          var thn = translator.RemoveLit(TrExpr(e.Thn));
          var els = translator.RemoveLit(TrExpr(e.Els));
          return new NAryExpr(expr.tok, new IfThenElse(expr.tok), new List<Bpl.Expr> { g, thn, els });

        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          var ite = DesugarMatchExpr(e);
          return TrExpr(ite);

        } else if (expr is ConcreteSyntaxExpression) {
          var e = (ConcreteSyntaxExpression)expr;
          return TrExpr(e.ResolvedExpression);

        } else if (expr is BoxingCastExpr) {
          BoxingCastExpr e = (BoxingCastExpr)expr;
          return translator.CondApplyBox(e.tok, TrExpr(e.E), e.FromType, e.ToType);

        } else if (expr is UnboxingCastExpr) {
          UnboxingCastExpr e = (UnboxingCastExpr)expr;
          return translator.CondApplyUnbox(e.tok, TrExpr(e.E), e.FromType, e.ToType);

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
        }
      }

      private Expr TrLambdaExpr(LambdaExpr e) {
        var bvars = new List<Bpl.Variable>();
        var bargs = new List<Bpl.Expr>();

        var heap = BplBoundVar(e.MkName("heap"), predef.HeapType, bvars);
        bargs.Add(heap);

        var subst = new Dictionary<IVariable, Expression>();
        foreach (var bv in e.BoundVars) {
          var ve = BplBoundVar(e.MkName(bv.Name), predef.BoxType, bvars);
          bargs.Add(ve);

          Bpl.Expr unboxy = translator.UnboxIfBoxed(ve, bv.Type);

          subst[bv] = new BoogieWrapper(unboxy, bv.Type);
        }
        var su = new Substituter(null, subst, new Dictionary<TypeParameter, Type>(), translator);

        var et = new ExpressionTranslator(this, heap);
        var lvars = new List<Bpl.Variable>();
        var ly = BplBoundVar(e.MkName("ly"), predef.LayerType, lvars);
        et = et.WithLayer(ly);

        var ebody = et.TrExpr(translator.Substitute(e.Body, null, subst));
        ebody = translator.BoxIfUnboxed(ebody, e.Body.Type);

        Bpl.Expr reqbody = Bpl.Expr.True;
        if (e.Range != null) {
          reqbody = et.TrExpr(translator.Substitute(e.Range, null, subst));
        }
        if (e.OneShot) {
          reqbody = BplAnd(reqbody, Bpl.Expr.Eq(HeapExpr, heap));
        }

        var rdvars = new List<Bpl.Variable>();
        var o = translator.UnboxIfBoxed(BplBoundVar(e.MkName("o"), predef.BoxType, rdvars), new ObjectType());

        Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), et.IsAlloced(e.tok, o));
        Bpl.Expr consequent = translator.InRWClause(e.tok, o, null, e.Reads.ConvertAll(su.SubstFrameExpr), et, null, null);
        Bpl.Expr rdbody = 
          new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), rdvars, null, 
            BplImp(ante, consequent));

        return translator.Lit(
          translator.FunctionCall(e.tok, BuiltinFunction.AtLayer, predef.HandleType,
            new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), lvars, null,
              translator.FunctionCall(e.tok, translator.Handle(e.BoundVars.Count), predef.BoxType,
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, ebody),
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, reqbody),
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, rdbody))), 
            layerIntraCluster ?? layerInterCluster), 
          predef.HandleType);
      }

      public Expression DesugarMatchExpr(MatchExpr e) {
        Contract.Requires(e != null);
        // Translate:
        //   match S
        //   case C(i, j) => X
        //   case D(k, l) => Y
        //   case E(m, n) => Z
        // into:
        //   if S.C? then
        //     X[i,j := S.dC0, S.dC1]
        //   else if S.D? then
        //     Y[k,l := S.dD0, S.dD1]
        //   else
        //     Z[m,n := S.dE0, S.dE1]
        // As a special case, when there are no cases at all (which, in a correct program, means the
        // match expression is unreachable), the translation is:
        //   t
        // where is "t" is some value (in particular, the default value) of the expected type.
        Expression r = null;
        for (int i = e.Cases.Count; 0 <= --i; ) {
          var mc = e.Cases[i];
          var substMap = new Dictionary<IVariable, Expression>();
          var argIndex = 0;
          foreach (var bv in mc.Arguments) {
            if (!LocalVariable.HasWildcardName(bv)) {
              var dtor = mc.Ctor.Destructors[argIndex];
              var dv = new MemberSelectExpr(bv.tok, e.Source, dtor.Name);
              dv.Member = dtor;  // resolve here
              dv.Type = bv.Type;  // resolve here
              substMap.Add(bv, dv);
            }
            argIndex++;
          }
          var c = translator.Substitute(mc.Body, null, substMap);
          if (r == null) {
            r = c;
          } else {
            var test = new MemberSelectExpr(mc.tok, e.Source, mc.Ctor.QueryField.Name);
            test.Member = mc.Ctor.QueryField;  // resolve here
            test.Type = Type.Bool;  // resolve here
            var ite = new ITEExpr(mc.tok, test, c, r);
            ite.Type = e.Type;
            r = ite;
          }
        }
        return r ?? new BoogieWrapper(ArbitraryValue(e.Type), e.Type);
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars) {
        return TrBoundVariables(boundVars, bvars, false);
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars, bool translateAsLocals) {
        Contract.Requires(boundVars != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var tid = new Bpl.TypedIdent(bv.tok, bv.AssignUniqueName(translator.currentDeclaration), translator.TrType(bv.Type));
          Bpl.Variable bvar;
          if (translateAsLocals) {
            bvar = new Bpl.LocalVariable(bv.tok, tid);
          } else {
            bvar = new Bpl.BoundVariable(bv.tok, tid);
          }
          bvars.Add(bvar);
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, bvar), bv.Type, this);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public Bpl.Expr TrBoundVariablesRename(List<BoundVar> boundVars, List<Variable> bvars, out Dictionary<IVariable, Expression> substMap) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);

        substMap = new Dictionary<IVariable, Expression>();
        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var newBoundVar = new BoundVar(bv.tok, bv.Name, bv.Type);
          IdentifierExpr ie = new IdentifierExpr(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration));
          ie.Var = newBoundVar; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(bv, ie);
          Bpl.Variable bvar = new Bpl.BoundVariable(newBoundVar.tok, new Bpl.TypedIdent(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration), translator.TrType(newBoundVar.Type)));
          bvars.Add(bvar);
          var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, bIe, newBoundVar.Type, this);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public List<Expr> FunctionInvocationArguments(FunctionCallExpr e, Bpl.Expr layerArgument) {
        bool returnLit;
        return FunctionInvocationArguments(e, layerArgument, out returnLit);
      }

      public List<Expr> FunctionInvocationArguments(FunctionCallExpr e, Bpl.Expr layerArgument, out bool returnLit) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<List<Bpl.Expr>>() != null);

        List<Bpl.Expr> args = new List<Bpl.Expr>();

        // first add type arguments        
        var tyParams = GetTypeParams(e.Function);
        var tySubst = e.TypeArgumentSubstitutions;
        Contract.Assert(tyParams.Count == tySubst.Count);
        args.AddRange(translator.trTypeArgs(tySubst, tyParams));
        
        if (layerArgument != null) {
          args.Add(layerArgument);
        }
        args.Add(HeapExpr);
        if (!e.Function.IsStatic) {
          args.Add(TrExpr(e.Receiver));
        }
        returnLit = true;
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Type t = e.Function.Formals[i].Type;
          Expr tr_ee = TrExpr(ee);
          returnLit = returnLit && translator.IsLit(tr_ee);
          args.Add(translator.CondApplyBox(e.tok, tr_ee, cce.NonNull(ee.Type), t));
        }
        return args;
      }

      public Bpl.Expr GetArrayIndexFieldName(IToken tok, List<Expression> indices) {
        return translator.GetArrayIndexFieldName(tok, Map(indices, TrExpr));
      }

      public Bpl.Expr BoxIfNecessary(IToken tok, Bpl.Expr e, Type fromType) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(fromType != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return translator.BoxIfNecessary(tok, e, fromType);
      }

      public static Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r, Expr f) {
        Contract.Requires(tok != null);
        Contract.Requires(heap != null);
        Contract.Requires(r != null);
        Contract.Requires(f != null);
        Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

        List<Bpl.Expr> args = new List<Bpl.Expr>();
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

        List<Bpl.Expr> args = new List<Bpl.Expr>();
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
              return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Or, TrInMultiSet(tok, elmt, bin.E0, elmtType), TrInMultiSet(tok, elmt, bin.E1, elmtType));
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.And, TrInMultiSet(tok, elmt, bin.E0, elmtType), TrInMultiSet(tok, elmt, bin.E1, elmtType));
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
          if (attrs.Name == skipThisAttribute
           || attrs.Name == "axiom") {  // Dafny's axiom attribute clashes with Boogie's axiom keyword
            continue;
          }
          List<object> parms = new List<object>();
          foreach (Attributes.Argument arg in attrs.Args) {
            if (arg.E != null) {
              var e = TrExpr(arg.E);
              e = translator.RemoveLit(e);
              parms.Add(e);
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
        return translator.IsAlloced(tok, HeapExpr, e);        
      }

      public Bpl.Expr GoodRef(IToken tok, Bpl.Expr e, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        // Add $Is and $IsAlloc
        return translator.GetWhereClause(tok, e, type, this);
      }

      public Bpl.Expr GoodRef_(IToken tok, Bpl.Expr e, Type ty, bool isNew) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(ty != null);

        Bpl.Expr tr_ty = translator.TypeToTy(ty); 

        Bpl.Expr alloc = IsAlloced(tok, e);
        if (isNew) {
          alloc = Bpl.Expr.Not(alloc);
        }

        return Bpl.Expr.And(alloc,translator.DType(e, tr_ty));
      }
    }

    enum BuiltinFunction
    {
      Lit,
      LitInt,
      LitReal,
      LayerSucc,
      
      Is, IsBox,
      IsAlloc, IsAllocBox,

      SetCard,
      SetEmpty,
      SetUnionOne,
      SetUnion,
      SetIntersection,
      SetDifference,
      SetEqual,
      SetSubset,
      SetDisjoint,
      IsGoodSet_Extended,

      MultiSetCard,
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
      IsGoodMultiSet_Extended,

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
      SeqRank,

      MapEmpty,
      MapCard,
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
      HeapSuccGhost,

      DynamicType,  // allocated type (of object reference)
      TypeTuple,
      DeclType,
      FieldOfDecl,
      FDim,  // field dimension (0 - named, 1 or more - indexed)
      IsGhostField,

      DatatypeCtorId,
      DtRank,
      BoxRank,

      GenericAlloc,

      AtLayer
    }

    Bpl.Expr Lit(Bpl.Expr expr, Bpl.Type typ) {
      Contract.Requires(expr != null);
      Contract.Requires(typ != null);
      // To avoid Boogie's int_2_U and U_2_int conversions, which seem to cause problems with
      // arithmetic reasoning, we use several Lit functions.  In particular, we use one for
      // integers, one for reals, and one for everything else.
      if (typ.IsInt) {
        return FunctionCall(expr.tok, BuiltinFunction.LitInt, null, expr);
      } else if (typ.IsReal) {
        return FunctionCall(expr.tok, BuiltinFunction.LitReal, null, expr);
      } else {
        return FunctionCall(expr.tok, BuiltinFunction.Lit, typ, expr);
      }
    }


    Bpl.Expr Lit(Bpl.Expr expr) {
      return Lit(expr, expr.Type);
    }

    Bpl.Expr GetLit(Bpl.Expr expr) {
      if (expr is NAryExpr) {
        NAryExpr app = (NAryExpr)expr;
        switch (app.Fun.FunctionName) {
          case "LitInt":
          case "LitReal":
          case "Lit":
            return app.Args[0];
          default:
            break;
        }
      }
      return null;
    }

    Bpl.Expr RemoveLit(Bpl.Expr expr) {
      return GetLit(expr) ?? expr;
    }

    bool IsLit(Bpl.Expr expr) {
      return GetLit(expr) != null;
    }

    // The "typeInstantiation" argument is passed in to help construct the result type of the function.
    Bpl.NAryExpr FunctionCall(IToken tok, BuiltinFunction f, Bpl.Type typeInstantiation, params Bpl.Expr[] args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(args != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      switch (f) {
        case BuiltinFunction.LitInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "LitInt", Bpl.Type.Int, args);
        case BuiltinFunction.LitReal:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "LitReal", Bpl.Type.Real, args);
        case BuiltinFunction.Lit:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Lit", typeInstantiation, args);
        case BuiltinFunction.LayerSucc:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$LS", predef.LayerType, args);

        case BuiltinFunction.Is:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$Is", Bpl.Type.Bool, args);
        case BuiltinFunction.IsBox:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsBox", Bpl.Type.Bool, args);
        case BuiltinFunction.IsAlloc:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsAlloc", Bpl.Type.Bool, args);
        case BuiltinFunction.IsAllocBox:
          Contract.Assert(args.Length == 3);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsAllocBox", Bpl.Type.Bool, args);

        case BuiltinFunction.SetCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Card", Bpl.Type.Int, args);
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
        case BuiltinFunction.IsGoodSet_Extended:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodSet_Extended", Bpl.Type.Bool, args);

        case BuiltinFunction.MultiSetCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "MultiSet#Card", Bpl.Type.Int, args);
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
        case BuiltinFunction.IsGoodMultiSet_Extended:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodMultiSet_Extended", Bpl.Type.Bool, args);

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
        case BuiltinFunction.SeqRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Seq#Rank", Bpl.Type.Int, args);

        case BuiltinFunction.MapEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MapType(tok, typeInstantiation, typeInstantiation);  // use 'typeInstantiation' (which is really always just BoxType anyway) as both type arguments
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Map#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.MapCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Map#Card", Bpl.Type.Int, args);
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
        case BuiltinFunction.HeapSuccGhost:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$HeapSuccGhost", Bpl.Type.Bool, args);

        case BuiltinFunction.DynamicType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "dtype", predef.ClassNameType, args);
        case BuiltinFunction.TypeTuple:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "TypeTuple", predef.ClassNameType, args);
        case BuiltinFunction.DeclType:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "DeclType", predef.ClassNameType, args);
        case BuiltinFunction.FieldOfDecl:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "FieldOfDecl", predef.FieldName(tok, typeInstantiation) , args);
        case BuiltinFunction.FDim:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "FDim", Bpl.Type.Int, args);
        case BuiltinFunction.IsGhostField:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "$IsGhostField", Bpl.Type.Bool, args);

        case BuiltinFunction.DatatypeCtorId:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DatatypeCtorId", predef.DtCtorId, args);
        case BuiltinFunction.DtRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "DtRank", Bpl.Type.Int, args);
        case BuiltinFunction.BoxRank:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "BoxRank", Bpl.Type.Int, args);

        case BuiltinFunction.GenericAlloc:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "GenericAlloc", Bpl.Type.Bool, args);

        case BuiltinFunction.AtLayer:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "AtLayer", typeInstantiation, args);

        default:
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected built-in function
      }
    }

    Bpl.NAryExpr FunctionCall(IToken tok, string function, Bpl.Type returnType, params Bpl.Expr[] args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(returnType != null);
      Contract.Requires(args != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), new List<Bpl.Expr>(args));
    }

    Bpl.NAryExpr FunctionCall(IToken tok, string function, Bpl.Type returnType, List<Bpl.Expr> args)
    {
      Contract.Requires(tok != null);
      Contract.Requires(function != null);
      Contract.Requires(returnType != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      List<Bpl.Expr> aa = new List<Bpl.Expr>();
      foreach (Bpl.Expr arg in args) {
        aa.Add(arg);
      }
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, function, returnType)), aa);
    }

    public Bpl.Expr ProperSubset(IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.And,
        FunctionCall(tok, BuiltinFunction.SetSubset, null, e0, e1),
        Bpl.Expr.Not(FunctionCall(tok, BuiltinFunction.SetSubset, null, e1, e0)));
    }
    public Bpl.Expr ProperMultiset(IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.And,
        FunctionCall(tok, BuiltinFunction.MultiSetSubset, null, e0, e1),
        Bpl.Expr.Not(FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1)));
    }
    public Bpl.Expr ProperPrefix(IToken tok, Bpl.Expr e0, Bpl.Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      Bpl.Expr len0 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e0);
      Bpl.Expr len1 = FunctionCall(tok, BuiltinFunction.SeqLength, null, e1);
      return Bpl.Expr.And(
        Bpl.Expr.Lt(len0, len1),
        FunctionCall(tok, BuiltinFunction.SeqSameUntil, null, e0, e1, len0));
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
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, name, Bpl.Type.Int)), new List<Bpl.Expr> { arr });
    }

    public class SplitExprInfo
    {
      public enum K { Free, Checked, Both }
      public K Kind;
      public bool IsOnlyFree { get { return Kind == K.Free; } }
      public bool IsOnlyChecked { get { return Kind == K.Checked; } }
      public bool IsChecked { get { return Kind != K.Free; } }
      public readonly Bpl.Expr E;
      public SplitExprInfo(K kind, Bpl.Expr e) {
        Contract.Requires(e != null && e.tok != null);
        // TODO:  Contract.Requires(kind == K.Free || e.tok.IsValid);
        Kind = kind;
        E = e;
      }
    }

    List<SplitExprInfo/*!*/>/*!*/ TrSplitExpr(Expression expr, ExpressionTranslator etran, bool apply_induction, out bool splitHappened) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, apply_induction, etran);
      return splits;
    }

    List<SplitExprInfo/*!*/>/*!*/ TrSplitExpr(Expression expr, ExpressionTranslator etran, int heightLimit, bool apply_induction, out bool splitHappened)
    {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      splitHappened = TrSplitExpr(expr, splits, true, heightLimit, apply_induction, etran);
      return splits;
    }

    /// <summary>
    /// Tries to split the expression into tactical conjuncts (if "position") or disjuncts (if "!position").
    /// If a (necessarily boolean) function call appears as a top-level conjunct, then inline the function if
    /// if it declared in the current module and its height is less than "heightLimit" (if "heightLimit" is
    /// passed in as 0, then no functions will be inlined).
    /// </summary>
    bool TrSplitExpr(Expression expr, List<SplitExprInfo/*!*/>/*!*/ splits, bool position, int heightLimit, bool apply_induction, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType || (expr is BoxingCastExpr && ((BoxingCastExpr)expr).E.Type.IsBoolType));
      Contract.Requires(splits != null);
      Contract.Requires(etran != null);

      if (expr is BoxingCastExpr) {
        var bce = (BoxingCastExpr)expr;
        var ss = new List<SplitExprInfo>();
        if (TrSplitExpr(bce.E, ss, position, heightLimit, apply_induction, etran)) {
          foreach (var s in ss) {
            splits.Add(new SplitExprInfo(s.Kind, CondApplyBox(s.E.tok, s.E, bce.FromType, bce.ToType)));
          }
          return true;
        }

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return TrSplitExpr(e.ResolvedExpression, splits, position, heightLimit, apply_induction, etran);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          return TrSplitExpr(etran.GetSubstitutedBody(e), splits, position, heightLimit, apply_induction, etran);
        } else {
          var d = LetDesugaring(e);
          return TrSplitExpr(d, splits, position, heightLimit, apply_induction, etran);
        }

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Not) {
          var ss = new List<SplitExprInfo>();
          if (TrSplitExpr(e.E, ss, !position, heightLimit, apply_induction, etran)) {
            foreach (var s in ss) {
              splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Unary(s.E.tok, UnaryOperator.Opcode.Not, s.E)));
            }
            return true;
          }
        }

      } else if (expr is BinaryExpr) {
        var bin = (BinaryExpr)expr;
        if (position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, apply_induction, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, apply_induction, etran);
          return true;

        } else  if (!position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, apply_induction, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, apply_induction, etran);
          return true;

        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
          // non-conditionally split these, so we get the source location to point to a subexpression
          if (position) {
            var lhs = etran.TrExpr(bin.E0);
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E1, ss, position, heightLimit, apply_induction, etran);
            foreach (var s in ss) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, lhs, s.E)));
            }
          } else {
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E0, ss, !position, heightLimit, apply_induction, etran);
            var rhs = etran.TrExpr(bin.E1);
            foreach (var s in ss) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
            }
          }
          return true;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        if ((e.Op == TernaryExpr.Opcode.PrefixEqOp && position) || (e.Op == TernaryExpr.Opcode.PrefixNeqOp && !position)) {
          var e1type = e.E1.Type.NormalizeExpand();
          var e2type = e.E2.Type.NormalizeExpand();
          var codecl = e1type.AsCoDatatype;
          Contract.Assert(codecl != null);
          var k = etran.TrExpr(e.E0);
          var A = etran.TrExpr(e.E1);
          var B = etran.TrExpr(e.E2);
          // split as shows here for possibly infinite lists:
          //   checked $PrefixEqual#Dt(k, A, B) || (0 < k ==> A.Nil? ==> B.Nil?)
          //   checked $PrefixEqual#Dt(k, A, B) || (0 < k ==> A.Cons? ==> B.Cons? && A.head == B.head && $PrefixEqual#2#Dt(k - 1, A.tail, B.tail))  // note the #2 in the recursive call, just like for user-defined predicates that are inlined by TrSplitExpr
          //   free $PrefixEqual#Dt(k, A, B);
          var kPos = Bpl.Expr.Lt(Bpl.Expr.Literal(0), k);
          var prefixEqK = CoEqualCall(codecl, e1type.TypeArgs, e2type.TypeArgs, k, etran.LayerN(2), A, B); // FunctionCall(expr.tok, CoPrefixName(codecl, 1), Bpl.Type.Bool, k, A, B);
          var kMinusOne = Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
          // for the inlining of the definition of prefix equality, translate the two main equality operands arguments with a higher offset (to obtain #2 functions)
          var etran2 = etran.LayerOffset(1);
          var A2 = etran2.TrExpr(e.E1);
          var B2 = etran2.TrExpr(e.E2);
          var needsTokenAdjust = TrSplitNeedsTokenAdjustment(expr);
          // Dan: dafny4/Circ.dfy needs this one to be 2+, rather than 1+ 
          Bpl.Expr layer = LayerSucc(etran.layerInterCluster, 2); 
          foreach (var c in CoPrefixEquality(needsTokenAdjust ? new ForceCheckToken(expr.tok) : expr.tok, codecl, e1type.TypeArgs, e2type.TypeArgs, kMinusOne, layer, A2, B2, true)) {
            var p = Bpl.Expr.Binary(c.tok, BinaryOperator.Opcode.Or, prefixEqK, Bpl.Expr.Imp(kPos, c));
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, p));
          }
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, prefixEqK));
          return true;
        }

      } else if (expr is ITEExpr) {
        var ite = (ITEExpr)expr;

        var ssThen = new List<SplitExprInfo>();
        var ssElse = new List<SplitExprInfo>();

        TrSplitExpr(ite.Thn, ssThen, position, heightLimit, apply_induction, etran);
        TrSplitExpr(ite.Els, ssElse, position, heightLimit, apply_induction, etran);

        var op = position ? BinaryOperator.Opcode.Imp : BinaryOperator.Opcode.And;
        var test = etran.TrExpr(ite.Test);
        foreach (var s in ssThen)
        {
          // as the source location in the following implication, use that of the translated "s"
          splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, op, test, s.E)));
        }

        var negatedTest = Bpl.Expr.Not(test);
        foreach (var s in ssElse)
        {
          // as the source location in the following implication, use that of the translated "s"
          splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, op, negatedTest, s.E)));
        }

        return true;
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // For an expression S;E in split position, the conclusion of S can be used as an assumption.  Unfortunately,
        // this assumption is not generated in non-split positions (because I don't know how.)
        // So, treat "S; E" like "SConclusion ==> E".
        if (position) {
          var conclusion = etran.TrExpr(e.GetSConclusion());
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.E, ss, position, heightLimit, apply_induction, etran);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, conclusion, s.E)));
          }
        } else {
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.GetSConclusion(), ss, !position, heightLimit, apply_induction, etran);
          var rhs = etran.TrExpr(e.E);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
          }
        }
        return true;

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return TrSplitExpr(e.E, splits, position, heightLimit, apply_induction, etran.Old);

      } else if (expr is FunctionCallExpr && position) {
        var fexp = (FunctionCallExpr)expr;
        var f = fexp.Function;
        Contract.Assert(f != null);  // filled in during resolution
        var module = f.EnclosingClass.Module;
        var functionHeight = module.CallGraph.GetSCCRepresentativeId(f);

        if (module == currentModule && functionHeight < heightLimit && f.Body != null && !(f.Body.Resolved is MatchExpr)) {
          if (RefinementToken.IsInherited(fexp.tok, currentModule) &&
              f is Predicate && ((Predicate)f).BodyOrigin == Predicate.BodyOriginKind.DelayedDefinition &&
              (codeContext == null || !codeContext.MustReverify)) {
            // The function was inherited as body-less but is now given a body. Don't inline the body (since, apparently, everything
            // that needed to be proved about the function was proved already in the previous module, even without the body definition).
          } else if (IsOpaqueFunction(f)) {
            // Don't inline opaque functions
          } else {
            // inline this body
            var body = GetSubstitutedBody(fexp, f, false);
            var typeSpecializedBody = GetSubstitutedBody(fexp, f, true);
            var typeSpecializedResultType = Resolver.SubstType(f.ResultType, fexp.TypeArgumentSubstitutions);

            // Produce, for a "body" split into b0, b1, b2:
            //     checked F#canCall(args) ==> F(args) || b0
            //     checked F#canCall(args) ==> F(args) || b1
            //     checked F#canCall(args) ==> F(args) || b2
            //     free F#canCall(args) && F(args) && (b0 && b1 && b2)
            // For "inCoContext", split into:
            //     checked F#canCall(args) ==> F'(args) || b0''
            //     checked F#canCall(args) ==> F'(args) || b1''
            //     checked F#canCall(args) ==> F'(args) || b2''
            //     free F#canCall(args) && F'(args)
            // where the primes indicate certificate translations.
            // The checked conjuncts of the body make use of the type-specialized body.

            // F#canCall(args)
            Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
            List<Bpl.Expr> args = etran.FunctionInvocationArguments(fexp, null);
            Bpl.Expr canCall = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);

            Bpl.Expr fargs;
            // F(args)
            fargs = etran.TrExpr(fexp);

            // recurse on body
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(typeSpecializedBody, ss, position, functionHeight, apply_induction, etran);
            var needsTokenAdjust = TrSplitNeedsTokenAdjustment(typeSpecializedBody);
            foreach (var s in ss) {
              if (s.IsChecked) {
                var unboxedConjunct = CondApplyUnbox(s.E.tok, s.E, typeSpecializedResultType, expr.Type);
                var bodyOrConjunct = Bpl.Expr.Or(fargs, unboxedConjunct);
                var tok = needsTokenAdjust ? (IToken)new ForceCheckToken(typeSpecializedBody.tok) : (IToken)new NestedToken(fexp.tok, s.E.tok);
                var p = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Imp, canCall, bodyOrConjunct);
                splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, p));
              }
            }

            // body
            var trBody = etran.TrExpr(typeSpecializedBody); 
            trBody = CondApplyUnbox(trBody.tok, trBody, typeSpecializedResultType, expr.Type);
            // F#canCall(args) && F(args) && (b0 && b1 && b2)
            var fr = Bpl.Expr.And(canCall, BplAnd(fargs, trBody));
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, fr));

            return true;
          }
        }

      } else if (((position && expr is ForallExpr) || (!position && expr is ExistsExpr)) 
          /* NB: only for type arg less quantifiers for now: */ 
             && ((QuantifierExpr)expr).TypeArgs.Count == 0) {
        var e = (QuantifierExpr)expr;
        var inductionVariables = ApplyInduction(e);
        if (apply_induction && 2 <= DafnyOptions.O.Induction && inductionVariables.Count != 0) {
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
            types.Add(n.Type.NormalizeExpand());
            BoundVar k = new BoundVar(n.tok, n.Name + "$ih#" + otherTmpVarCount, n.Type);
            otherTmpVarCount++;
            kvars.Add(k);

            IdentifierExpr ieK = new IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration));
            ieK.Var = k; ieK.Type = ieK.Var.Type;  // resolve it here
            kk.Add(etran.TrExpr(ieK));

            IdentifierExpr ieN = new IdentifierExpr(n.tok, n.AssignUniqueName(currentDeclaration));
            ieN.Var = n; ieN.Type = ieN.Var.Type;  // resolve it here
            nn.Add(etran.TrExpr(ieN));

            substMap.Add(n, ieK);
          }
          Expression bodyK = Substitute(e.LogicalBody(), null, substMap);

          Bpl.Expr less = DecreasesCheck(toks, types, types, kk, nn, null, null, false, true);

          Bpl.Expr ihBody = etran.TrExpr(bodyK);
          if (!position) {
            ihBody = Bpl.Expr.Not(ihBody);
          }
          ihBody = Bpl.Expr.Imp(less, ihBody);
          List<Variable> bvars = new List<Variable>();
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(kvars, bvars);
          Bpl.Expr ih = new Bpl.ForallExpr(expr.tok, bvars, Bpl.Expr.Imp(typeAntecedent, ihBody));

          // More precisely now:
          //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case0(n)   ==> P(n))
          //   (forall n :: n-has-expected-type && (forall k :: k < n ==> P(k)) && case...(n) ==> P(n))
          // or similar for existentials.
          var caseProduct = new List<Bpl.Expr>() {
            // make sure to include the correct token information (so, don't just use Bpl.Expr.True here)
            new Bpl.LiteralExpr(TrSplitNeedsTokenAdjustment(expr) ? new ForceCheckToken(expr.tok) : expr.tok, true)
          };
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
          bvars = new List<Variable>();
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
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, q));
          }

          // Finally, assume the original quantifier (forall/exists n :: P(n))
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, etran.TrExpr(expr)));
          return true;

        } else {
          // Don't use induction on these quantifiers.
          // Nevertheless, produce two translated versions of the quantifier, one that uses #2 functions (that is, layerOffset 1)
          // for checking and one that uses #1 functions (that is, layerOffset 0) for assuming.
          var etranBoost = etran.LayerOffset(1);
          var r = etranBoost.TrExpr(expr);
          var needsTokenAdjustment = TrSplitNeedsTokenAdjustment(expr);
          if (needsTokenAdjustment) {
            r.tok = new ForceCheckToken(expr.tok);
          }
          if (etranBoost.Statistics_CustomLayerFunctionCount == 0) {
            // apparently, the LayerOffset(1) we did had no effect
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Both, r));
            return needsTokenAdjustment;
          } else {
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, r));  // check the boosted expression
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, etran.TrExpr(expr)));  // assume the ordinary expression
            return true;
          }
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
      if (TrSplitNeedsTokenAdjustment(expr)) {
        translatedExpression.tok = new ForceCheckToken(expr.tok);
        splitHappened = true;
      }
      splits.Add(new SplitExprInfo(SplitExprInfo.K.Both, translatedExpression));
      return splitHappened;
    }

    private Expression GetSubstitutedBody(FunctionCallExpr fexp, Function f, bool specializeTypeParameters) {
      Contract.Requires(fexp != null);
      Contract.Requires(f != null);
      var substMap = new Dictionary<IVariable, Expression>();
      Contract.Assert(fexp.Args.Count == f.Formals.Count);
      for (int i = 0; i < f.Formals.Count; i++) {
        Formal p = f.Formals[i];
        var formalType = specializeTypeParameters ? Resolver.SubstType(p.Type, fexp.TypeArgumentSubstitutions) : p.Type;
        Expression arg = fexp.Args[i];
        arg = new BoxingCastExpr(arg, cce.NonNull(arg.Type), formalType);
        arg.Type = formalType;  // resolve here
        substMap.Add(p, arg);
      }
      var body = f.Body;
      if (f is PrefixPredicate) {
        var pp = (PrefixPredicate)f;
        body = PrefixSubstitution(pp, body);
      }
      body = Substitute(body, fexp.Receiver, substMap, specializeTypeParameters ? fexp.TypeArgumentSubstitutions : null);
      return body;
    }

    bool TrSplitNeedsTokenAdjustment(Expression expr) {
      Contract.Requires(expr != null);
      return RefinementToken.IsInherited(expr.tok, currentModule) && (codeContext == null || !codeContext.MustReverify) && RefinementTransformer.ContainsChange(expr, currentModule);
    }

    List<BoundVar> ApplyInduction(QuantifierExpr e) {
      Contract.Requires(e.TypeArgs.Count == 0);
      return ApplyInduction(e.BoundVars, e.Attributes, new List<Expression>() { e.LogicalBody() },
        delegate(System.IO.TextWriter wr) { new Printer(wr).PrintExpression(e, true); });
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
    /// not 'expr' has prominent status in its context.
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
        var decr = e.Function.Decreases.Expressions;
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
          } else if (rec) {
            // The argument position is considered to be "variant" if the function is recursive and...
            // ... it has something to do with why the callee is well-founded, which happens when...
            if (f is ImplicitFormal) {
              // ... it is the argument is the implicit _k parameter, which is always first in the effective decreases clause of a prefix lemma, or
              variantArgument = true;
            } else if (decr.Exists(ee => ContainsFreeVariable(ee, false, f))) {
              // ... it participates in the effective decreases clause of the function, which happens when it is
              // a free variable of a term in the explicit decreases clause, or
              variantArgument = true;
            } else {
              // ... the callee is a prefix predicate.
              variantArgument = true;
            }
          }
          if (VarOccursInArgumentToRecursiveFunction(exp, n, variantArgument || subExprIsProminent)) {
            return true;
          }
        }
        return false;
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            return VarOccursInArgumentToRecursiveFunction(e.E0, n, true) ||
              VarOccursInArgumentToRecursiveFunction(e.E1, n, subExprIsProminent) ||
              VarOccursInArgumentToRecursiveFunction(e.E2, n, subExprIsProminent);
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected ternary expression
        }
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
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // ignore the statement
        return VarOccursInArgumentToRecursiveFunction(e.E, n);

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
      ty = ty.NormalizeExpand();
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
          List<Variable> bvs;
          List<Bpl.Expr> args;
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          // (exists args :: args-have-the-expected-types && ct(args) == expr)
          Bpl.Expr q = Bpl.Expr.Binary(ctor.tok, BinaryOperator.Opcode.Eq, ct, expr);
          if (bvs.Count != 0)
          {
            int i = 0;
            Bpl.Expr typeAntecedent = Bpl.Expr.True;
            foreach (Formal arg in ctor.Formals) {
              var instantiatedArgType = Resolver.SubstType(arg.Type, subst);
              Bpl.Expr wh = GetWhereClause(arg.tok, CondApplyUnbox(arg.tok, args[i], arg.Type, instantiatedArgType), instantiatedArgType, etran);
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
        return Contract.Exists(expr.SubExpressions, ee => ContainsFreeVariable(ee, lookForReceiver, v));
      }
    }

    // No expression introduces a type variable
    static void ComputeFreeTypeVariables(Expression expr, ISet<TypeParameter> fvs) {
      ComputeFreeTypeVariables(expr.Type, fvs);
      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        e.TypeArgumentSubstitutions.Iter(kv => ComputeFreeTypeVariables(kv.Value, fvs));
      }
      expr.SubExpressions.Iter(ee => ComputeFreeTypeVariables(ee, fvs));
    }

    static void ComputeFreeTypeVariables(Type ty, ISet<TypeParameter> fvs) {
      // Add type parameters, unless they are abstract type declarations: they are in scope 
      if (ty.IsTypeParameter && ! ty.AsTypeParameter.IsAbstractTypeDeclaration) {
        fvs.Add(ty.AsTypeParameter);
      }
      ty.NormalizeExpand().TypeArgs.Iter(tt => ComputeFreeTypeVariables(tt, fvs));
    }

    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs, ref bool usesHeap, ref bool usesOldHeap, ref Type usesThis, bool inOldContext) {
      Contract.Requires(expr != null);

      if (expr is ThisExpr) {
        Contract.Assert(expr.Type != null);
        usesThis = expr.Type;
        return;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        fvs.Add(e.Var);
        return;
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        bool subUsesHeap = false;
        ComputeFreeVariables(e.E, fvs, ref subUsesHeap, ref usesOldHeap, ref usesThis, true);
        if (subUsesHeap) {
          usesOldHeap = true;
        }
      } else if (expr is MemberSelectExpr) {
        usesHeap = true;
      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        if (e.Seq.Type.IsArrayType) {
          usesHeap = true;
        }
      } else if (expr is MultiSelectExpr) {
        usesHeap = true;
      } else if (expr is FunctionCallExpr) {
        usesHeap = true;
      } else if (expr is UnaryOpExpr && ((UnaryOpExpr)expr).Op == UnaryOpExpr.Opcode.Fresh) {
        usesOldHeap = true;
      }

      // visit subexpressions
      bool uHeap = false, uOldHeap = false;
      Type uThis = null;
      expr.SubExpressions.Iter(ee => ComputeFreeVariables(ee, fvs, ref uHeap, ref uOldHeap, ref uThis, inOldContext));
      Contract.Assert(usesThis == null || uThis == null || usesThis.Equals(uThis));
      usesThis = usesThis ?? uThis;
      usesHeap |= uHeap;
      usesOldHeap |= uOldHeap;

      if (expr is LetExpr) {
        var e = (LetExpr)expr;
        foreach (var v in e.BoundVars) {
          fvs.Remove(v);
        }
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var v in e.BoundVars) {
          fvs.Remove(v);
        }
      }
    }

    /// <summary>
    /// Returns an expression like "expr", but where free occurrences of "v" have been replaced by "e".
    /// </summary>
    public Expression Substitute(Expression expr, IVariable v, Expression e) {
      Contract.Requires(expr != null);
      Contract.Requires(v != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Expression>() != null);
      var substMap = new Dictionary<IVariable, Expression>();
      substMap.Add(v, e);
      return Substitute(expr, null, substMap);
    }

    public Expression Substitute(Expression expr, Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type>/*?*/ typeMap = null) {
      Contract.Requires(expr != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new Substituter(receiverReplacement, substMap, typeMap ?? new Dictionary<TypeParameter, Type>(), this);
      return s.Substitute(expr);
    }

    public class FunctionCallSubstituter : Substituter
    {
      public readonly Function A, B;
      public FunctionCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Function a, Function b, Translator translator)
        : base(receiverReplacement, substMap, new Dictionary<TypeParameter,Type>(), translator) {
        A = a;
        B = b;
      }
      public override Expression Substitute(Expression expr) {
        if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          Expression receiver = Substitute(e.Receiver);
          List<Expression> newArgs = SubstituteExprList(e.Args);
          FunctionCallExpr newFce = new FunctionCallExpr(expr.tok, e.Name, receiver, e.OpenParen, newArgs);
          if (e.Function == A) {
            newFce.Function = B;
            newFce.Type = e.Type; // TODO: this may not work with type parameters.
          } else {
            newFce.Function = e.Function;
            newFce.Type = e.Type;
          }
          newFce.TypeArgumentSubstitutions = e.TypeArgumentSubstitutions;  // resolve here
          return newFce;
        }
        return base.Substitute(expr);
      }
    }
    public class PrefixCallSubstituter : Substituter
    {
      readonly CoPredicate coPred;
      readonly Expression coDepth;
      readonly ModuleDefinition module;
      public PrefixCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> tySubstMap, CoPredicate copred, Expression depth, Translator translator)
        : base(receiverReplacement, substMap, tySubstMap, translator) {
        Contract.Requires(copred != null);
        Contract.Requires(depth != null);
        coPred = copred;
        coDepth = depth;
        module = copred.EnclosingClass.Module;
      }
      public override Expression Substitute(Expression expr) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          var cof = e.Function as CoPredicate;
          if (cof != null && ModuleDefinition.InSameSCC(cof, coPred)) {
            expr = cof.CreatePrefixPredicateCall(e, coDepth);
          }
        }
        return base.Substitute(expr);
      }
    }
    /// <summary>
    /// The substituter has methods to create an expression from an existing one, where the new one has the indicated
    /// substitutions for "this" (receiverReplacement), variables (substMap), and types (typeMap).
    /// CAUTION:  The result of the substitution is intended for use by TrExpr, not for well-formedness checks.  In
    /// particular, the substituter does not copy parts of an expression that are used only for well-formedness checks.
    /// </summary>
    public class Substituter
    {
      public readonly Expression receiverReplacement;
      public readonly Dictionary<IVariable, Expression/*!*/>/*!*/ substMap;
      public readonly Dictionary<TypeParameter, Type/*!*/>/*!*/ typeMap;
      readonly Translator translator;
      public Substituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap, Translator translator) {
        Contract.Requires(substMap != null);
        Contract.Requires(typeMap != null);
        this.receiverReplacement = receiverReplacement;
        this.substMap = substMap;
        this.typeMap = typeMap;
        this.translator = translator;
      }
      public virtual Expression Substitute(Expression expr) {
        Contract.Requires(expr != null);
        Contract.Ensures(Contract.Result<Expression>() != null);

        Expression newExpr = null;  // set to non-null value only if substitution has any effect; if non-null, the .Type of newExpr will be filled in at end

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
          List<Expression> newElements = SubstituteExprList(e.Elements);
          if (newElements != e.Elements) {
            if (expr is SetDisplayExpr) {
              newExpr = new SetDisplayExpr(expr.tok, newElements);
            } else if (expr is MultiSetDisplayExpr) {
              newExpr = new MultiSetDisplayExpr(expr.tok, newElements);
            } else {
              newExpr = new SeqDisplayExpr(expr.tok, newElements);
            }
          }
        } else if (expr is MapDisplayExpr) {
          var e = (MapDisplayExpr)expr;
          var elmts = new List<ExpressionPair>();
          var anyChanges = false;
          foreach (var ep in e.Elements) {
            var a = Substitute(ep.A);
            var b = Substitute(ep.B);
            elmts.Add(new ExpressionPair(a, b));
            if (a != ep.A || b != ep.B) {
              anyChanges = true;
            }
          }
          if (anyChanges) {
            newExpr = new MapDisplayExpr(expr.tok, elmts);
          }
        } else if (expr is MemberSelectExpr) {
          MemberSelectExpr fse = (MemberSelectExpr)expr;
          Expression substE = Substitute(fse.Obj);
          MemberSelectExpr fseNew = new MemberSelectExpr(fse.tok, substE, fse.MemberName);
          fseNew.Member = fse.Member;
          fseNew.TypeApplication = fse.TypeApplication == null
            ? null
            : fse.TypeApplication.ConvertAll(t => Resolver.SubstType(t, typeMap));
          newExpr = fseNew;
        } else if (expr is SeqSelectExpr) {
          SeqSelectExpr sse = (SeqSelectExpr)expr;
          Expression seq = Substitute(sse.Seq);
          Expression e0 = sse.E0 == null ? null : Substitute(sse.E0);
          Expression e1 = sse.E1 == null ? null : Substitute(sse.E1);
          if (seq != sse.Seq || e0 != sse.E0 || e1 != sse.E1) {
            newExpr = new SeqSelectExpr(sse.tok, sse.SelectOne, seq, e0, e1);
          }

        } else if (expr is SeqUpdateExpr) {
          SeqUpdateExpr sse = (SeqUpdateExpr)expr;
          if (sse.ResolvedUpdateExpr != null)
          {
            newExpr = Substitute(sse.ResolvedUpdateExpr);
          }
          else
          {
            Expression seq = Substitute(sse.Seq);
            Expression index = Substitute(sse.Index);
            Expression val = Substitute(sse.Value);
            if (seq != sse.Seq || index != sse.Index || val != sse.Value)
            {
              newExpr = new SeqUpdateExpr(sse.tok, seq, index, val);
            }
          }

        } else if (expr is MultiSelectExpr) {
          MultiSelectExpr mse = (MultiSelectExpr)expr;
          Expression array = Substitute(mse.Array);
          List<Expression> newArgs = SubstituteExprList(mse.Indices);
          if (array != mse.Array || newArgs != mse.Indices) {
            newExpr = new MultiSelectExpr(mse.tok, array, newArgs);
          }

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          Expression receiver = Substitute(e.Receiver);
          List<Expression> newArgs = SubstituteExprList(e.Args);
          var newTypeInstantiation = SubstituteTypeMap(e.TypeArgumentSubstitutions);
          if (receiver != e.Receiver || newArgs != e.Args || newTypeInstantiation != e.TypeArgumentSubstitutions) {
            FunctionCallExpr newFce = new FunctionCallExpr(expr.tok, e.Name, receiver, e.OpenParen, newArgs);
            newFce.Function = e.Function;  // resolve on the fly (and set newFce.Type below, at end)
            newFce.CoCall = e.CoCall;  // also copy the co-call status
            newFce.TypeArgumentSubstitutions = newTypeInstantiation;
            newExpr = newFce;
          }

        } else if (expr is ApplyExpr) {
          ApplyExpr e = (ApplyExpr)expr;
          Expression receiver = Substitute(e.Function);
          List<Expression> args = SubstituteExprList(e.Args);
          newExpr = new ApplyExpr(e.tok, e.OpenParen, receiver, args);

        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          List<Expression> newArgs = SubstituteExprList(dtv.Arguments);
          if (newArgs != dtv.Arguments) {
            DatatypeValue newDtv = new DatatypeValue(dtv.tok, dtv.DatatypeName, dtv.MemberName, newArgs);
            newDtv.Ctor = dtv.Ctor;  // resolve on the fly (and set newDtv.Type below, at end)
            newDtv.InferredTypeArgs = Map(dtv.InferredTypeArgs, tt => Resolver.SubstType(tt, typeMap));
                                     // ^ Set the correct type arguments to the constructor 
            newExpr = newDtv;
          }

        } else if (expr is OldExpr) {
          OldExpr e = (OldExpr)expr;
          // Note, it is up to the caller to avoid variable capture.  In most cases, this is not a
          // problem, since variables have unique declarations.  However, it is an issue if the substitution
          // takes place inside an OldExpr.  In those cases (see LetExpr), the caller can use a
          // BoogieWrapper before calling Substitute.
          Expression se = Substitute(e.E);
          if (se != e.E) {
            newExpr = new OldExpr(expr.tok, se);
          }
        } else if (expr is MultiSetFormingExpr) {
          var e = (MultiSetFormingExpr)expr;
          var se = Substitute(e.E);
          if (se != e.E) {
            newExpr = new MultiSetFormingExpr(expr.tok, se);
          }
        } else if (expr is BoxingCastExpr) {
          var e = (BoxingCastExpr)expr;
          var se = Substitute(e.E);
          if (se != e.E) {
            newExpr = new BoxingCastExpr(se, e.FromType, e.ToType);
          }
        } else if (expr is UnaryExpr) {
          var e = (UnaryExpr)expr;
          Expression se = Substitute(e.E);
          if (se != e.E) {
            if (e is UnaryOpExpr) {
              var ee = (UnaryOpExpr)e;
              newExpr = new UnaryOpExpr(expr.tok, ee.Op, se);
            } else if (e is ConversionExpr) {
              var ee = (ConversionExpr)e;
              newExpr = new ConversionExpr(expr.tok, se, ee.ToType);
            } else {
              Contract.Assert(false);  // unexpected UnaryExpr subtype
            }
          }
        } else if (expr is BinaryExpr) {
          BinaryExpr e = (BinaryExpr)expr;
          Expression e0 = Substitute(e.E0);
          Expression e1 = Substitute(e.E1);
          if (e0 != e.E0 || e1 != e.E1) {
            BinaryExpr newBin = new BinaryExpr(expr.tok, e.Op, e0, e1);
            newBin.ResolvedOp = e.ResolvedOp;  // part of what needs to be done to resolve on the fly (newBin.Type is set below, at end)
            newExpr = newBin;
          }

        } else if (expr is TernaryExpr) {
          var e = (TernaryExpr)expr;
          var e0 = Substitute(e.E0);
          var e1 = Substitute(e.E1);
          var e2 = Substitute(e.E2);
          if (e0 != e.E0 || e1 != e.E1 || e2 != e.E2) {
            newExpr = new TernaryExpr(expr.tok, e.Op, e0, e1, e2);
          }

        } else if (expr is LetExpr) {
          var e = (LetExpr)expr;
          if (e.Exact) {
            var rhss = new List<Expression>();
            bool anythingChanged = false;
            foreach (var rhs in e.RHSs) {
              var r = Substitute(rhs);
              if (r != rhs) {
                anythingChanged = true;
              }
              rhss.Add(r);
            }
            // Note, CreateBoundVarSubstitutions has the side effect of updating the substitution map.
            // For an Exact let expression, this is something that needs to be done after substituting
            // in the RHSs.
            var newCasePatterns = CreateCasePatternSubstitutions(e.LHSs);
            if (newCasePatterns != e.LHSs) {
              anythingChanged = true;
            }
            var body = Substitute(e.Body);
            // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
            foreach (var bv in e.BoundVars) {
              substMap.Remove(bv);
            }
            // Put things together
            if (anythingChanged || body != e.Body) {
              newExpr = new LetExpr(e.tok, newCasePatterns, rhss, body, e.Exact);
            }
          } else {
            var rhs = Substitute(e.RHSs[0]);
            var body = Substitute(e.Body);
            if (rhs == e.RHSs[0] && body == e.Body) {
              return e;
            }
            var newLet = new LetExpr(e.tok, e.LHSs, new List<Expression>{ rhs }, body, e.Exact);
            if (translator != null)
            {
              Expression d = translator.LetDesugaring(e);
              newLet.translationDesugaring = Substitute(d);
              var info = translator.letSuchThatExprInfo[e];
              translator.letSuchThatExprInfo.Add(newLet, new LetSuchThatExprInfo(info, translator, substMap, typeMap));
            }
            newExpr = newLet;
          }

        } else if (expr is MatchExpr) {
          var e = (MatchExpr)expr;
          var src = Substitute(e.Source);
          bool anythingChanged = src != e.Source;
          var cases = new List<MatchCaseExpr>();
          foreach (var mc in e.Cases) {
            var newBoundVars = CreateBoundVarSubstitutions(mc.Arguments);
            var body = Substitute(mc.Body);
            // undo any changes to substMap (could be optimized to do this only if newBoundVars != mc.Arguments)
            foreach (var bv in mc.Arguments) {
              substMap.Remove(bv);
            }
            // Put things together
            if (newBoundVars != mc.Arguments || body != mc.Body) {
              anythingChanged = true;
            }
            var newCaseExpr = new MatchCaseExpr(mc.tok, mc.Id, newBoundVars, body);
            newCaseExpr.Ctor = mc.Ctor;  // resolve here
            cases.Add(newCaseExpr);
          }
          if (anythingChanged) {
            var newME = new MatchExpr(expr.tok, src, cases, e.UsesOptionalBraces);
            newME.MissingCases.AddRange(e.MissingCases);
            newExpr = newME;
          }

        } else if (expr is NamedExpr) {
          var e = (NamedExpr)expr;
          var body = Substitute(e.Body);
          var contract = e.Contract == null ? null : Substitute(e.Contract);
          newExpr = new NamedExpr(e.tok, e.Name, body, contract, e.ReplacerToken);
        } else if (expr is ComprehensionExpr) {
          var e = (ComprehensionExpr)expr;
          // For quantifiers we want to make sure that we don't introduce name clashes with
          // the enclosing scopes.
          var newBoundVars = CreateBoundVarSubstitutions(e.BoundVars, expr is ForallExpr || expr is ExistsExpr);
          Expression newRange = e.Range == null ? null : Substitute(e.Range);
          Expression newTerm = Substitute(e.Term);
          Attributes newAttrs = SubstAttributes(e.Attributes);
          if (newBoundVars != e.BoundVars || newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes) {
            if (e is SetComprehension) {
              newExpr = new SetComprehension(expr.tok, newBoundVars, newRange, newTerm);
            } else if (e is MapComprehension) {
              newExpr = new MapComprehension(expr.tok, newBoundVars, newRange, newTerm);
            } else if (expr is ForallExpr) {
              newExpr = new ForallExpr(expr.tok, ((QuantifierExpr)expr).TypeArgs, newBoundVars, newRange, newTerm, newAttrs);
            } else if (expr is ExistsExpr) {
              newExpr = new ExistsExpr(expr.tok, ((QuantifierExpr)expr).TypeArgs, newBoundVars, newRange, newTerm, newAttrs);
            } else if (expr is LambdaExpr) {
              var l = (LambdaExpr)expr;
              newExpr = new LambdaExpr(e.tok, l.OneShot, newBoundVars, newRange, l.Reads.ConvertAll(SubstFrameExpr), newTerm);
            } else {
              Contract.Assert(false);  // unexpected ComprehensionExpr
            }
          }
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.BoundVars)
          foreach (var bv in e.BoundVars) {
            substMap.Remove(bv);
          }

        } else if (expr is StmtExpr) {
          var e = (StmtExpr)expr;
          newExpr = new StmtExpr(e.tok, SubstStmt(e.S), Substitute(e.E));

        } else if (expr is ITEExpr) {
          ITEExpr e = (ITEExpr)expr;
          Expression test = Substitute(e.Test);
          Expression thn = Substitute(e.Thn);
          Expression els = Substitute(e.Els);
          if (test != e.Test || thn != e.Thn || els != e.Els) {
            newExpr = new ITEExpr(expr.tok, test, thn, els);
          }

        } else if (expr is ConcreteSyntaxExpression) {
          var e = (ConcreteSyntaxExpression)expr;
          return Substitute(e.ResolvedExpression);
        } else if (expr is BoogieFunctionCall) {
          var e = (BoogieFunctionCall)expr;
          bool anythingChanged = false;
          var newTyArgs = new List<Type>();
          foreach (var arg in e.TyArgs) {
            var newArg = Resolver.SubstType(arg, typeMap);
            if (newArg != arg) {
              anythingChanged = true;
            }
            newTyArgs.Add(newArg);
          }
          var newArgs = new List<Expression>();
          foreach (var arg in e.Args) {
            var newArg = Substitute(arg);
            if (newArg != arg) {
              anythingChanged = true;
            }
            newArgs.Add(newArg);
          }
          if (anythingChanged) {
            newExpr = new BoogieFunctionCall(e.tok, e.FunctionName, e.UsesHeap, e.UsesOldHeap, newArgs, newTyArgs);
          }

        } else {
          Contract.Assume(false); // unexpected Expression
        }

        if (newExpr == null) {
          return expr;
        } else {
          newExpr.Type = Resolver.SubstType(expr.Type, typeMap);  // resolve on the fly (any additional resolution must be done above)
          return newExpr;
        }
      }

      /// <summary>
      /// Return a list of bound variables, of the same length as 'vars' but with possible substitutions.
      /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
      /// undoing these changes once the updated 'substMap' has been used.
      /// If no changes are necessary, the list returned is exactly 'vars' and 'substMap' is unchanged.
      /// </summary>
      protected virtual List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfQuantifiedVars = false) {
        bool anythingChanged = false;
        var newBoundVars = new List<BoundVar>();
        foreach (var bv in vars) {
          var tt = Resolver.SubstType(bv.Type, typeMap);
          if (!forceSubstitutionOfQuantifiedVars && tt == bv.Type) {
            newBoundVars.Add(bv);
          } else {
            anythingChanged = true;
            var newBv = new BoundVar(bv.tok, bv.Name, tt);
            newBoundVars.Add(newBv);
            // update substMap to reflect the new BoundVar substitutions
            var ie = new IdentifierExpr(newBv.tok, newBv.Name);
            ie.Var = newBv;  // resolve here
            ie.Type = newBv.Type;  // resolve here
            substMap.Add(bv, ie);
          }
        }
        return anythingChanged ? newBoundVars : vars;
      }

      /// <summary>
      /// Return a list of case patterns, of the same length as 'patterns' but with possible substitutions.
      /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
      /// undoing these changes once the updated 'substMap' has been used.
      /// If no changes are necessary, the list returned is exactly 'patterns' and 'substMap' is unchanged.
      /// </summary>
      protected virtual List<CasePattern> CreateCasePatternSubstitutions(List<CasePattern> patterns) {
        bool anythingChanged = false;
        var newPatterns = new List<CasePattern>();
        foreach (var pat in patterns) {
          var newPat = SubstituteCasePattern(pat);
          newPatterns.Add(newPat);
          if (newPat != pat) {
            anythingChanged = true;
          }
        }
        return anythingChanged ? newPatterns : patterns;
      }
      CasePattern SubstituteCasePattern(CasePattern pat) {
        Contract.Requires(pat != null);
        if (pat.Var != null) {
          var bv = pat.Var;
          var tt = Resolver.SubstType(bv.Type, typeMap);
          if (tt != bv.Type) {
            var newBv = new BoundVar(pat.tok, pat.Id, tt);
            // update substMap to reflect the new BoundVar substitutions
            var ie = new IdentifierExpr(newBv.tok, newBv.Name);
            ie.Var = newBv;  // resolve here
            ie.Type = newBv.Type;  // resolve here
            substMap.Add(bv, ie);
            var newPat = new CasePattern(pat.tok, newBv);
            newPat.AssembleExpr(null);
            return newPat;
          }
        } else if (pat.Arguments != null) {
          bool anythingChanged = false;
          var newArgs = new List<CasePattern>();
          foreach (var arg in pat.Arguments) {
            var newArg = SubstituteCasePattern(arg);
            newArgs.Add(newArg);
            if (newArg != arg) {
              anythingChanged = true;
            }
          }
          if (anythingChanged) {
            var patE = (DatatypeValue)pat.Expr;
            var newPat = new CasePattern(pat.tok, pat.Id, newArgs);
            newPat.Ctor = pat.Ctor;
            newPat.AssembleExpr(patE.InferredTypeArgs.ConvertAll(tp => Resolver.SubstType(tp, typeMap)));
            return newPat;
          }
        }
        return pat;
      }

      protected List<Expression/*!*/>/*!*/ SubstituteExprList(List<Expression/*!*/>/*!*/ elist) {
        Contract.Requires(cce.NonNullElements(elist));
        Contract.Ensures(cce.NonNullElements(Contract.Result<List<Expression>>()));

        List<Expression> newElist = null;  // initialized lazily
        for (int i = 0; i < elist.Count; i++) {
          cce.LoopInvariant(newElist == null || newElist.Count == i);

          Expression substE = Substitute(elist[i]);
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

      protected Dictionary<TypeParameter, Type> SubstituteTypeMap(Dictionary<TypeParameter, Type> tmap) {
        Contract.Requires(tmap != null);
        Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);
        if (typeMap.Count == 0) {  // optimization
          return tmap;
        }
        bool anythingChanged = false;
        var newTmap = new Dictionary<TypeParameter, Type>();
        var i = 0;
        foreach (var maplet in tmap) {
          cce.LoopInvariant(newTmap == null || newTmap.Count == i);
          var tt = Resolver.SubstType(maplet.Value, typeMap);
          if (tt != maplet.Value) {
            anythingChanged = true;
          }
          newTmap.Add(maplet.Key, tt);
          i++;
        }
        if (anythingChanged) {
          return newTmap;
        } else {
          return tmap;
        }
      }

      /// <summary>
      /// This method (which currently is used only internally to class Substituter) performs substitutions in
      /// statements that can occur in a StmtExpr.  (For example, it does not bother to do anything with a
      /// PrintStmt, ReturnStmt, or YieldStmt.)
      /// </summary>
      protected virtual Statement SubstStmt(Statement stmt) {
        Statement r;
        if (stmt == null) {
          return null;
        } else if (stmt is AssertStmt) {
          var s = (AssertStmt)stmt;
          r = new AssertStmt(s.Tok, s.EndTok, Substitute(s.Expr), SubstAttributes(s.Attributes));
        } else if (stmt is AssumeStmt) {
          var s = (AssumeStmt)stmt;
          r = new AssumeStmt(s.Tok, s.EndTok, Substitute(s.Expr), SubstAttributes(s.Attributes));
        } else if (stmt is BreakStmt) {
          var s = (BreakStmt)stmt;
          BreakStmt rr;
          if (s.TargetLabel != null) {
            rr = new BreakStmt(s.Tok, s.EndTok, s.TargetLabel);
          } else {
            rr = new BreakStmt(s.Tok, s.EndTok, s.BreakCount);
          }
          // r.TargetStmt will be filled in as later
          List<BreakStmt> breaks;
          if (!BreaksToBeResolved.TryGetValue(s, out breaks)) {
            breaks = new List<BreakStmt>();
            BreaksToBeResolved.Add(s, breaks);
          }
          breaks.Add(rr);
          r = rr;
        } else if (stmt is AssignStmt) {
          var s = (AssignStmt)stmt;
          r = new AssignStmt(s.Tok, s.EndTok, Substitute(s.Lhs), SubstRHS(s.Rhs));
        } else if (stmt is CallStmt) {
          var s = (CallStmt)stmt;
          var rr = new CallStmt(s.Tok, s.EndTok, s.Lhs.ConvertAll(Substitute), Substitute(s.Receiver), s.MethodName, s.Args.ConvertAll(Substitute));
          rr.Method = s.Method;
          rr.TypeArgumentSubstitutions = new Dictionary<TypeParameter, Type>(); 
          foreach (var p in s.TypeArgumentSubstitutions) {
            rr.TypeArgumentSubstitutions[p.Key] = Resolver.SubstType(p.Value, typeMap);
          }
          r = rr;
        } else if (stmt is BlockStmt) {
          r = SubstBlockStmt((BlockStmt)stmt);
        } else if (stmt is IfStmt) {
          var s = (IfStmt)stmt;
          r = new IfStmt(s.Tok, s.EndTok, Substitute(s.Guard), SubstBlockStmt(s.Thn), SubstStmt(s.Els));
        } else if (stmt is AlternativeStmt) {
          var s = (AlternativeStmt)stmt;
          r = new AlternativeStmt(s.Tok, s.EndTok, s.Alternatives.ConvertAll(SubstGuardedAlternative));
        } else if (stmt is WhileStmt) {
          var s = (WhileStmt)stmt;
          r = new WhileStmt(s.Tok, s.EndTok, Substitute(s.Guard), s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), SubstBlockStmt(s.Body));
        } else if (stmt is AlternativeLoopStmt) {
          var s = (AlternativeLoopStmt)stmt;
          r = new AlternativeLoopStmt(s.Tok, s.EndTok, s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(SubstGuardedAlternative));
        } else if (stmt is ForallStmt) {
          var s = (ForallStmt)stmt;
          var newBoundVars = CreateBoundVarSubstitutions(s.BoundVars);
          var body = SubstStmt(s.Body);
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
          foreach (var bv in s.BoundVars) {
            substMap.Remove(bv);
          }
          // Put things together
          var rr = new ForallStmt(s.Tok, s.EndTok, newBoundVars, SubstAttributes(s.Attributes), Substitute(s.Range), s.Ens.ConvertAll(SubstMayBeFreeExpr), body);
          rr.Kind = s.Kind;
          r = rr;
        } else if (stmt is CalcStmt) {
          var s = (CalcStmt)stmt;
          var rr = new CalcStmt(s.Tok, s.EndTok, SubstCalcOp(s.Op), s.Lines.ConvertAll(Substitute), s.Hints.ConvertAll(SubstBlockStmt), s.StepOps.ConvertAll(SubstCalcOp), SubstCalcOp(s.ResultOp));
          rr.Steps.AddRange(s.Steps.ConvertAll(Substitute));
          rr.Result = Substitute(s.Result);
          r = rr;
        } else if (stmt is MatchStmt) {
          var s = (MatchStmt)stmt;
          var rr = new MatchStmt(s.Tok, s.EndTok, Substitute(s.Source), s.Cases.ConvertAll(SubstMatchCaseStmt), s.UsesOptionalBraces);
          rr.MissingCases.AddRange(s.MissingCases);
          r = rr;
        } else if (stmt is AssignSuchThatStmt) {
          var s = (AssignSuchThatStmt)stmt;
          r = new AssignSuchThatStmt(s.Tok, s.EndTok, s.Lhss.ConvertAll(Substitute), Substitute(s.Expr), s.AssumeToken == null ? null : s.AssumeToken);
        } else if (stmt is UpdateStmt) {
          var s = (UpdateStmt)stmt;
          var resolved = s.ResolvedStatements;
          UpdateStmt rr;
          if (resolved.Count == 1) {
            // when later translating this UpdateStmt, the s.Lhss and s.Rhss components won't be used, only s.ResolvedStatements
            rr = new UpdateStmt(s.Tok, s.EndTok, s.Lhss, s.Rhss, s.CanMutateKnownState);
          } else {
            rr = new UpdateStmt(s.Tok, s.EndTok, s.Lhss.ConvertAll(Substitute), s.Rhss.ConvertAll(SubstRHS), s.CanMutateKnownState);
          }
          rr.ResolvedStatements.AddRange(s.ResolvedStatements.ConvertAll(SubstStmt));
          r = rr;
        } else if (stmt is VarDeclStmt) {
          var s = (VarDeclStmt)stmt;
          var lhss = s.Locals.ConvertAll(c => new LocalVariable(c.Tok, c.EndTok, c.Name, c.OptionalType == null ? null : Resolver.SubstType(c.OptionalType, typeMap), c.IsGhost));
          var rr = new VarDeclStmt(s.Tok, s.EndTok, lhss, (ConcreteUpdateStatement)SubstStmt(s.Update));
          r = rr;
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
        }

        // add labels to the cloned statement
        AddStmtLabels(r, stmt.Labels);
        r.Attributes = SubstAttributes(stmt.Attributes);
        r.IsGhost = stmt.IsGhost;
        if (stmt.Labels != null || stmt is WhileStmt) {
          List<BreakStmt> breaks;
          if (BreaksToBeResolved.TryGetValue(stmt, out breaks)) {
            foreach (var b in breaks) {
              b.TargetStmt = r;
            }
            BreaksToBeResolved.Remove(stmt);
          }
        }

        return r;
      }

      Dictionary<Statement, List<BreakStmt>> BreaksToBeResolved = new Dictionary<Statement, List<BreakStmt>>();  // old-target -> new-breaks

      protected void AddStmtLabels(Statement s, LList<Label> node) {
        if (node != null) {
          AddStmtLabels(s, node.Next);
          s.Labels = new LList<Label>(node.Data, s.Labels);
        }
      }

      protected virtual BlockStmt SubstBlockStmt(BlockStmt stmt) {
        return stmt == null ? null : new BlockStmt(stmt.Tok, stmt.EndTok, stmt.Body.ConvertAll(SubstStmt));
      }

      protected GuardedAlternative SubstGuardedAlternative(GuardedAlternative alt) {
        Contract.Requires(alt != null);
        return new GuardedAlternative(alt.Tok, Substitute(alt.Guard), alt.Body.ConvertAll(SubstStmt));
      }

      protected MaybeFreeExpression SubstMayBeFreeExpr(MaybeFreeExpression expr) {
        Contract.Requires(expr != null);
        var mfe = new MaybeFreeExpression(Substitute(expr.E), expr.IsFree);
        mfe.Attributes = SubstAttributes(expr.Attributes);
        return mfe;
      }

      protected Specification<Expression> SubstSpecExpr(Specification<Expression> spec) {
        var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(Substitute);
        return new Specification<Expression>(ee, SubstAttributes(spec.Attributes));
      }

      protected Specification<FrameExpression> SubstSpecFrameExpr(Specification<FrameExpression> frame) {
        var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(SubstFrameExpr);
        return new Specification<FrameExpression>(ee, SubstAttributes(frame.Attributes));
      }

      public FrameExpression SubstFrameExpr(FrameExpression frame) {
        Contract.Requires(frame != null);
        return new FrameExpression(frame.tok, Substitute(frame.E), frame.FieldName);
      }

      protected AssignmentRhs SubstRHS(AssignmentRhs rhs) {
        AssignmentRhs c;
        if (rhs is ExprRhs) {
          var r = (ExprRhs)rhs;
          c = new ExprRhs(Substitute(r.Expr));
        } else if (rhs is HavocRhs) {
          c = new HavocRhs(rhs.Tok);
        } else {
          // since the Substituter is assumed to operate on statements only if they are part of a StatementExpression, then the TypeRhs case cannot occur
          Contract.Assume(false); throw new cce.UnreachableException();
        }
        c.Attributes = SubstAttributes(rhs.Attributes);
        return c;
      }

      protected MatchCaseStmt SubstMatchCaseStmt(MatchCaseStmt c) {
        Contract.Requires(c != null);
        var newBoundVars = CreateBoundVarSubstitutions(c.Arguments);
        var r = new MatchCaseStmt(c.tok, c.Id, newBoundVars, c.Body.ConvertAll(SubstStmt));
        r.Ctor = c.Ctor;
        // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
        foreach (var bv in c.Arguments) {
          substMap.Remove(bv);
        }
        return r;
      }

      protected CalcStmt.CalcOp SubstCalcOp(CalcStmt.CalcOp op) {
        if (op is CalcStmt.BinaryCalcOp) {
          return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp)op).Op);
        } else if (op is CalcStmt.TernaryCalcOp) {
          return new CalcStmt.TernaryCalcOp(Substitute(((CalcStmt.TernaryCalcOp)op).Index));
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public Attributes SubstAttributes(Attributes attrs) {
        Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
        if (attrs != null) {
          List<Attributes.Argument> newArgs = new List<Attributes.Argument>();  // allocate it eagerly, what the heck, it doesn't seem worth the extra complexity in the code to do it lazily for the infrequently occurring attributes
          bool anyArgSubst = false;
          foreach (Attributes.Argument arg in attrs.Args) {
            Attributes.Argument newArg = arg;
            if (arg.E != null) {
              Expression newE = Substitute(arg.E);
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

          Attributes prev = SubstAttributes(attrs.Prev);
          if (newArgs != attrs.Args || prev != attrs.Prev) {
            return new Attributes(attrs.Name, newArgs, prev);
          }
        }
        return attrs;
      }
    }

    /// <summary>
    /// This substituter performs substitutions in such a way that it's okay to print the resulting expression without a human getting confused.
    /// More precisely, bound variables first gets alpha-renamed.  Also, "this" is never left implicit, including in the
    /// case where "receiverReplacement" is given as ImplicitThisExpr (but no attempt is made to substitute for all ImplicitThisExpr's in
    /// "receiverReplacement" and the range of "substMap").
    /// </summary>
    public class AlphaConverting_Substituter : Substituter
    {
      ISet<string> namesToAvoid = new HashSet<string>();
      public AlphaConverting_Substituter(Expression receiverReplacement, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap, Translator translator)
        : base(receiverReplacement is ImplicitThisExpr ? new ThisExpr(receiverReplacement.tok) : receiverReplacement, substMap, typeMap, translator) {
        Contract.Requires(substMap != null);
        Contract.Requires(typeMap != null);
        Contract.Requires(translator != null);
      }
      protected override List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfQuantifiedVars) {
        var newBoundVars = vars.Count == 0 ? vars : new List<BoundVar>();
        foreach (var bv in vars) {
          var tt = Resolver.SubstType(bv.Type, typeMap);
          var newBv = new BoundVar(bv.tok, "_'" + bv.Name, tt);
          newBoundVars.Add(newBv);
          // update substMap to reflect the new BoundVar substitutions
          var ie = new IdentifierExpr(newBv.tok, newBv.Name);
          ie.Var = newBv;  // resolve here
          ie.Type = newBv.Type;  // resolve here
          substMap.Add(bv, ie);
        }
        return newBoundVars;
      }
    }

    Bpl.Expr HeapSameOrSucc(Bpl.Expr oldHeap, Bpl.Expr newHeap) {
      return Bpl.Expr.Or(
        Bpl.Expr.Eq(oldHeap, newHeap),
        FunctionCall(newHeap.tok, BuiltinFunction.HeapSucc, null, oldHeap, newHeap));
    }

    // Bpl-making-utilities

    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Expr body) {
      var args = new List<Bpl.Variable>(args_in);
      if (args.Count == 0) {
        return body;
      } else {
        return new Bpl.ForallExpr(body.tok, args, body);
      }
    }

    // Note: if the trigger is null, makes a forall without any triggers
    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Trigger trg, Bpl.Expr body) {
      if (trg == null) {
        return BplForall(args_in, body);
      } else {
        var args = new List<Bpl.Variable>(args_in);
        if (args.Count == 0) {
          return body;
        } else {
          return new Bpl.ForallExpr(body.tok, args, trg, body);
        }
      }
    }

    static Bpl.Expr BplForall(Bpl.Variable arg, Bpl.Trigger trg, Bpl.Expr body) {
      return BplForall(Singleton(arg), trg, body);
    }

    static Bpl.Expr BplAnd(IEnumerable<Bpl.Expr> conjuncts) {
      Contract.Requires(conjuncts != null);
      Bpl.Expr eq = Bpl.Expr.True;
      foreach (var c in conjuncts) {
        eq = BplAnd(eq, c);
      }
      return eq;
    }

    static Bpl.Expr BplAnd(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True) {
        return b;
      } else if (b == Bpl.Expr.True) {
        return a;
      } else {
        return Bpl.Expr.Binary(a.tok, BinaryOperator.Opcode.And, a, b);
      }
    }

    static Bpl.Expr BplOr(IEnumerable<Bpl.Expr> disjuncts) {
      Contract.Requires(disjuncts != null);
      Bpl.Expr eq = Bpl.Expr.False;
      foreach (var d in disjuncts) {
        eq = BplOr(eq, d);
      }
      return eq;
    }

    static Bpl.Expr BplOr(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.False) {
        return b;
      } else if (b == Bpl.Expr.False) {
        return a;
      } else {
        return Bpl.Expr.Binary(a.tok, BinaryOperator.Opcode.Or, a, b);
      }
    }

    Bpl.Expr BplIff(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True) { 
        return b;
      } else if (b == Bpl.Expr.True) {
        return a;
      } else {
        return Bpl.Expr.Iff(a, b);
      }
    }

    static Bpl.Expr BplImp(Bpl.Expr a, Bpl.Expr b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (a == Bpl.Expr.True || b == Bpl.Expr.True || b == Bpl.Expr.False) {
        return b;
      } else if (a == Bpl.Expr.False) {
        return Bpl.Expr.True;
      } else {
        return Bpl.Expr.Imp(a, b);
      }
    }

    private static void BplIfIf(IToken tk, bool yes, Bpl.Expr guard, Bpl.StmtListBuilder builder, Action<Bpl.StmtListBuilder> k) {
      if (yes) {
        var newBuilder = new Bpl.StmtListBuilder();
        k(newBuilder);
        builder.Add(new Bpl.IfCmd(tk, guard, newBuilder.Collect(tk), null, null));
      } else {
        k(builder);
      }
    }

    /// <summary>
    /// lhs should be a Bpl.IdentifierExpr. 
    /// Creates lhs := rhs;
    /// </summary>
    static Bpl.Cmd BplSimplestAssign(Bpl.Expr lhs, Bpl.Expr rhs) {
      Contract.Requires(lhs is Bpl.IdentifierExpr);
      return new Bpl.AssignCmd(rhs.tok,
        Singleton((AssignLhs)new SimpleAssignLhs(rhs.tok, (Bpl.IdentifierExpr)lhs)),
        Singleton(rhs));
    }

    /// Makes a simple trigger
    static Bpl.Trigger BplTrigger(Bpl.Expr e) {
      return new Trigger(e.tok, true, new List<Bpl.Expr> { e });
    }

    static Bpl.Axiom BplAxiom(Bpl.Expr e) {
      return new Bpl.Axiom(e.tok, e);
    }

    static Bpl.Expr BplLocalVar(string name, Bpl.Type ty, List<Bpl.Variable> lvars) {
      Bpl.Expr v;
      lvars.Add(BplLocalVar(name, ty, out v));
      return v;
    }

    static Bpl.LocalVariable BplLocalVar(string name, Bpl.Type ty, out Bpl.Expr e) {
      Contract.Requires(ty != null);
      var v = new Bpl.LocalVariable(ty.tok, new Bpl.TypedIdent(ty.tok, name, ty));
      e = new Bpl.IdentifierExpr(ty.tok, name, ty);
      return v;
    }

    /* This function allows you to replace, for example:
       
           Bpl.BoundVariable iVar = new Bpl.BoundVariable(e.tok, new Bpl.TypedIdent(e.tok, "$i", Bpl.Type.Int));
           Bpl.IdentifierExpr i = new Bpl.IdentifierExpr(e.tok, iVar);
      
       with:

           Bpl.Expr i; var iVar = BplBoundVar("$i", Bpl.Type.Int, out i); 
    */
    static Bpl.BoundVariable BplBoundVar(string name, Bpl.Type ty, out Bpl.Expr e) {
      Contract.Requires(ty != null);
      var v = new Bpl.BoundVariable(ty.tok, new Bpl.TypedIdent(ty.tok, name, ty));
      e = new Bpl.IdentifierExpr(ty.tok, name, ty);
      return v;
    }

    static Bpl.Expr BplBoundVar(string name, Bpl.Type ty, List<Bpl.Variable> bvars) {
      Bpl.Expr e;
      bvars.Add(BplBoundVar(name, ty, out e));
      return e;
    }

    // Makes a formal variable
    static Bpl.Formal BplFormalVar(string name, Bpl.Type ty, bool incoming) {
      Bpl.Expr _scratch;
      return BplFormalVar(name, ty, incoming, out _scratch);
    }

    static Bpl.Formal BplFormalVar(string name, Bpl.Type ty, bool incoming, out Bpl.Expr e) {
      Bpl.Formal res;
      if (name == null) {
        name = Bpl.TypedIdent.NoName;
      }
      res = new Bpl.Formal(ty.tok, new TypedIdent(ty.tok, name, ty), incoming);
      e = new Bpl.IdentifierExpr(ty.tok, res);
      return res;
    }

    static Bpl.Expr BplFormalVar(string name, Bpl.Type ty, bool incoming, List<Bpl.Variable> fvars) {
      Bpl.Expr e;
      fvars.Add(BplFormalVar(name, ty, incoming, out e));
      return e;
    }

    List<Bpl.Variable> MkTyParamBinders(List<TypeParameter> args) {
      List<Bpl.Expr> _scratch;
      return MkTyParamBinders(args, out _scratch);
    }

    List<Bpl.Variable> MkTyParamBinders(List<TypeParameter> args, out List<Bpl.Expr> exprs) {
      List<Bpl.Variable> vars = new List<Bpl.Variable>();
      exprs = new List<Bpl.Expr>();
      foreach (TypeParameter v in args) {
        Bpl.Expr e;
        vars.Add(BplBoundVar(nameTypeParam(v), predef.Ty, out e));
        exprs.Add(e);
      }
      return vars;
    }

    // For incoming formals
    List<Bpl.Variable> MkTyParamFormals(List<TypeParameter> args, bool named = true) {
      List<Bpl.Expr> _scratch;
      return MkTyParamFormals(args, out _scratch, named);
    }

    // For incoming formals
    List<Bpl.Variable> MkTyParamFormals(List<TypeParameter> args, out List<Bpl.Expr> exprs, bool named = true) {
      List<Bpl.Variable> vars = new List<Bpl.Variable>();
      exprs = new List<Bpl.Expr>();
      foreach (TypeParameter v in args) {
        Bpl.Expr e;
        vars.Add(BplFormalVar(named ? nameTypeParam(v) : null, predef.Ty, true, out e));
        exprs.Add(e);
      }
      return vars;
    }

    // Utilities for lists and dicts...

    static List<A> Singleton<A>(A x) {
      return Util.Singleton(x); 
    }

    static List<A> Cons<A>(A x, List<A> xs) {
      return Util.Cons(x, xs);
    }

    static List<A> Snoc<A>(List<A> xs, A x) {
      return Util.Snoc(xs, x); 
    }

    static List<A> Concat<A>(List<A> xs, List<A> ys) {
      return Util.Concat(xs, ys);
    }

    static List<B> Map<A,B>(IEnumerable<A> xs, Func<A,B> f) {
      return Util.Map(xs, f); 
    }
    
    public static void MapM<A>(IEnumerable<A> xs, Action<A> K)
    {
      Contract.Requires(xs != null);
      Contract.Requires(K != null);
      foreach (A x in xs) {
        K(x);
      }
    }

    static readonly List<Boolean> Bools = new List<Boolean> { false, true };
  }
}
