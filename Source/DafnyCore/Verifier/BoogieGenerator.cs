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
    private DafnyOptions options;
    public const string NameSeparator = "$$";
    private bool filterOnlyMembers;

    ErrorReporter reporter;
    // TODO(wuestholz): Enable this once Dafny's recommended Z3 version includes changeset 0592e765744497a089c42021990740f303901e67.
    public bool UseOptimizationInZ3 { get; set; }

    void AddOtherDefinition(Bpl.Declaration declaration, Axiom axiom) {
      sink.AddTopLevelDeclaration(axiom);

      // Axioms that have triggers and bound variables do not need to be inside
      // uses clauses. Putting such axioms inside uses clauses weakens pruning
      // when the trigger contains more than one function or constant symbol combined.
      // The early return would happen whenever axiom is of the form:
      // axiom (<quantifier> <(optionally) type variables> <at least one dummy variable> :: { ... } ...
      if (axiom.Expr is Microsoft.Boogie.QuantifierExpr qe && qe.Dummies != null && qe.Dummies.Any() &&
          qe.Triggers != null && qe.Triggers.Tr != null && qe.Triggers.Tr.Any()) {
        return;
      }

      switch (declaration) {
        case null:
          break;
        case Boogie.Function boogieFunction:
          boogieFunction.OtherDefinitionAxioms.Add(axiom);
          break;
        case Boogie.Constant boogieConstant:
          boogieConstant.DefinitionAxioms.Add(axiom);
          break;
        default: throw new ArgumentException("Declaration must be a function or constant");
      }
    }

    public class TranslatorFlags {
      public TranslatorFlags(DafnyOptions options) {
        InsertChecksums = 0 < options.VerifySnapshots;
      }

      public bool InsertChecksums { get; init; }
      public string UniqueIdPrefix = null;
      public bool ReportRanges = false;
    }

    [NotDelayed]
    public BoogieGenerator(ErrorReporter reporter, ProofDependencyManager depManager, TranslatorFlags flags = null) {
      this.options = reporter.Options;
      this.flags = new TranslatorFlags(options);
      this.proofDependencies = depManager;
      triggersCollector = new Triggers.TriggersCollector(new Dictionary<Expression, HashSet<OldExpr>>(), options);
      this.reporter = reporter;
      if (flags == null) {
        flags = new TranslatorFlags(options) {
          ReportRanges = options.Get(DafnyConsolePrinter.ShowSnippets)
        };
      }
      this.flags = flags;
      Bpl.Program boogieProgram = ReadPrelude();
      if (boogieProgram != null) {
        sink = boogieProgram;
        predef = FindPredefinedDecls(boogieProgram);
      }
    }

    public void SetReporter(ErrorReporter reporter) {
      this.reporter = reporter;
    }

    private void EstablishModuleScope(ModuleDefinition systemModule, ModuleDefinition m) {
      currentScope = new VisibilityScope();
      verificationScope = new VisibilityScope();

      currentScope.Augment(m.VisibilityScope);
      verificationScope.Augment(currentScope);

      currentScope.Augment(systemModule.VisibilityScope);
      foreach (var decl in m.TopLevelDecls) {
        if (decl is ModuleDecl && !(decl is ModuleExportDecl)) {
          var mdecl = (ModuleDecl)decl;
          currentScope.Augment(mdecl.AccessibleSignature().VisibilityScope);
        }
      }

    }

    // translation state
    readonly Dictionary<TopLevelDecl/*!*/, Bpl.Constant/*!*/>/*!*/ classes = new Dictionary<TopLevelDecl/*!*/, Bpl.Constant/*!*/>();
    readonly Dictionary<TopLevelDecl, string>/*!*/ classConstants = new Dictionary<TopLevelDecl, string>();
    readonly Dictionary<Function, string> functionHandles = new Dictionary<Function, string>();
    readonly List<FuelConstant> functionFuel = new List<FuelConstant>();
    readonly Dictionary<Function, Bpl.Expr> functionReveals = new();
    readonly Dictionary<Field/*!*/, Bpl.Constant/*!*/>/*!*/ fields = new Dictionary<Field/*!*/, Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/, Bpl.Function/*!*/>/*!*/ fieldFunctions = new Dictionary<Field/*!*/, Bpl.Function/*!*/>();
    readonly Dictionary<string, Bpl.Constant> fieldConstants = new Dictionary<string, Constant>();
    readonly Dictionary<string, Bpl.Constant> tytagConstants = new Dictionary<string, Constant>();

    private ProofDependencyManager proofDependencies;

    // optimizing translation
    readonly ISet<MemberDecl> referencedMembers = new HashSet<MemberDecl>();

    public void AddReferencedMember(MemberDecl m) {
      if (m is Method && !InVerificationScope(m)) {
        referencedMembers.Add(m);
      }
    }

    FuelContext fuelContext = null;
    IsAllocContext isAllocContext = null;
    Program program;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullDictionaryAndValues(classes));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fields));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fieldFunctions));
      Contract.Invariant(codeContext == null || codeContext.EnclosingModule == currentModule);
    }

    [Pure]
    bool VisibleInScope(Declaration d) {
      Contract.Requires(d != null);
      if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd }) {
        // "provides" is recorded in the non-null type declaration, not the class
        return nntd.IsVisibleInScope(currentScope);
      }
      return d.IsVisibleInScope(currentScope);
    }

    [Pure]
    bool VisibleInScope(Type t) {
      if (t is UserDefinedType udt && udt.ResolvedClass != null && !t.IsTypeParameter) {
        return VisibleInScope(udt.ResolvedClass);
      }
      return true;
    }

    [Pure]
    bool RevealedInScope(Declaration d) {
      Contract.Requires(d != null);
      return d.IsRevealedInScope(currentScope);
    }

    [Pure]
    bool RevealedInScope(RevealableTypeDecl d) {
      Contract.Requires(d != null);
      return RevealedInScope(d.AsTopLevelDecl);
    }

    [Pure]
    bool InVerificationScope(Declaration d) {
      Contract.Requires(d != null);
      if (!d.ShouldVerify(program.Compilation)) {
        return false;
      }

      if (d.IsVisibleInScope(verificationScope)) {
        Contract.Assert(d.IsRevealedInScope(verificationScope));
        if (d is MemberDecl m && m.EnclosingClass.EnclosingModuleDefinition is { IsFacade: true }) {
          return false;
        }

        return true;
      }
      return false;
    }

    [Pure]
    bool InVerificationScope(RedirectingTypeDecl d) {
      Contract.Requires(d != null);
      Contract.Requires(d is Declaration);
      return InVerificationScope((Declaration)d);
    }

    private Bpl.Program sink;
    private VisibilityScope currentScope;
    private VisibilityScope verificationScope;
    private Dictionary<Declaration, Bpl.Function> declarationMapping = new();

    readonly PredefinedDecls predef;

    private TranslatorFlags flags;
    private bool InsertChecksums { get { return flags.InsertChecksums; } }
    private string UniqueIdPrefix { get { return flags.UniqueIdPrefix; } }

    public class PredefinedDecls {
      public readonly Bpl.Type CharType;
      public readonly Bpl.Type RefType;
      public readonly Bpl.Type BoxType;
      public Bpl.Type BigOrdinalType {
        get { return BoxType; }
      }
      private readonly Bpl.TypeSynonymDecl setTypeCtor;
      private readonly Bpl.TypeSynonymDecl isetTypeCtor;
      private readonly Bpl.TypeSynonymDecl multiSetTypeCtor;
      private readonly Bpl.TypeCtorDecl mapTypeCtor;
      private readonly Bpl.TypeCtorDecl imapTypeCtor;
      public readonly Bpl.Function ArrayLength;
      public readonly Bpl.Function RealFloor;
      public readonly Bpl.Function ORDINAL_IsLimit;
      public readonly Bpl.Function ORDINAL_IsSucc;
      public readonly Bpl.Function ORDINAL_Offset;
      public readonly Bpl.Function ORDINAL_IsNat;
      public readonly Bpl.Function MapDomain;
      public readonly Bpl.Function IMapDomain;
      public readonly Bpl.Function MapValues;
      public readonly Bpl.Function IMapValues;
      public readonly Bpl.Function MapItems;
      public readonly Bpl.Function IMapItems;
      public readonly Bpl.Function ObjectTypeConstructor;
      public readonly Bpl.Function Tuple2TypeConstructor;
      public readonly Bpl.Function Tuple2Destructors0;
      public readonly Bpl.Function Tuple2Destructors1;
      public readonly Bpl.Function Tuple2Constructor;
      private readonly Bpl.TypeCtorDecl seqTypeCtor;
      public readonly Bpl.Type Bv0Type;
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
      public readonly Bpl.Type TyTagFamily;
      public readonly Bpl.Expr Null;
      public readonly Bpl.Constant AllocField;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(CharType != null);
        Contract.Invariant(RefType != null);
        Contract.Invariant(BoxType != null);
        Contract.Invariant(setTypeCtor != null);
        Contract.Invariant(multiSetTypeCtor != null);
        Contract.Invariant(ArrayLength != null);
        Contract.Invariant(RealFloor != null);
        Contract.Invariant(ORDINAL_IsLimit != null);
        Contract.Invariant(ORDINAL_IsSucc != null);
        Contract.Invariant(ORDINAL_Offset != null);
        Contract.Invariant(ORDINAL_IsNat != null);
        Contract.Invariant(MapDomain != null);
        Contract.Invariant(IMapDomain != null);
        Contract.Invariant(MapValues != null);
        Contract.Invariant(IMapValues != null);
        Contract.Invariant(MapItems != null);
        Contract.Invariant(IMapItems != null);
        Contract.Invariant(Tuple2Destructors0 != null);
        Contract.Invariant(Tuple2Destructors1 != null);
        Contract.Invariant(Tuple2Constructor != null);
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
        Contract.Invariant(TyTagFamily != null);
        Contract.Invariant(Null != null);
        Contract.Invariant(AllocField != null);
      }

      public Bpl.Type SetType(Bpl.IToken tok, bool finite, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, finite ? setTypeCtor : isetTypeCtor, new List<Bpl.Type> { ty });
      }

      public Bpl.Type MultiSetType(Bpl.IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, multiSetTypeCtor, new List<Bpl.Type> { ty });
      }
      public Bpl.Type MapType(Bpl.IToken tok, bool finite, Bpl.Type tya, Bpl.Type tyb) {
        Contract.Requires(tok != null);
        Contract.Requires(tya != null && tyb != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(Token.NoToken, finite ? mapTypeCtor : imapTypeCtor, new List<Bpl.Type> { tya, tyb });
      }

      public Bpl.Type SeqType(Bpl.IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);
        return new Bpl.CtorType(Token.NoToken, seqTypeCtor, new List<Bpl.Type> { ty });
      }

      public Bpl.Type FieldName(Bpl.IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(tok, fieldName, new List<Bpl.Type> { ty });
      }

      public Bpl.IdentifierExpr Alloc(Bpl.IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

        return new Bpl.IdentifierExpr(tok, AllocField);
      }

      public PredefinedDecls(Bpl.TypeCtorDecl charType, Bpl.TypeCtorDecl refType, Bpl.TypeCtorDecl boxType,
                             Bpl.TypeSynonymDecl setTypeCtor, Bpl.TypeSynonymDecl isetTypeCtor, Bpl.TypeSynonymDecl multiSetTypeCtor,
                             Bpl.TypeCtorDecl mapTypeCtor, Bpl.TypeCtorDecl imapTypeCtor,
                             Bpl.Function arrayLength, Bpl.Function realFloor,
                             Bpl.Function ORD_isLimit, Bpl.Function ORD_isSucc, Bpl.Function ORD_offset, Bpl.Function ORD_isNat,
                             Bpl.Function mapDomain, Bpl.Function imapDomain,
                             Bpl.Function mapValues, Bpl.Function imapValues, Bpl.Function mapItems, Bpl.Function imapItems,
                             Bpl.Function objectTypeConstructor,
                             Bpl.Function tuple2Destructors0, Bpl.Function tuple2Destructors1, Bpl.Function tuple2Constructor, Bpl.Function tuple2TypeConstructor,
                             Bpl.TypeCtorDecl seqTypeCtor, Bpl.TypeSynonymDecl bv0TypeDecl,
                             Bpl.TypeCtorDecl fieldNameType, Bpl.TypeCtorDecl tyType, Bpl.TypeCtorDecl tyTagType, Bpl.TypeCtorDecl tyTagFamilyType,
                             Bpl.GlobalVariable heap, Bpl.TypeCtorDecl classNameType, Bpl.TypeCtorDecl nameFamilyType,
                             Bpl.TypeCtorDecl datatypeType, Bpl.TypeCtorDecl handleType, Bpl.TypeCtorDecl layerType, Bpl.TypeCtorDecl dtCtorId,
                             Bpl.Constant allocField) {
        #region Non-null preconditions on parameters
        Contract.Requires(charType != null);
        Contract.Requires(refType != null);
        Contract.Requires(boxType != null);
        Contract.Requires(setTypeCtor != null);
        Contract.Requires(isetTypeCtor != null);
        Contract.Requires(multiSetTypeCtor != null);
        Contract.Requires(mapTypeCtor != null);
        Contract.Requires(imapTypeCtor != null);
        Contract.Requires(arrayLength != null);
        Contract.Requires(realFloor != null);
        Contract.Requires(ORD_isLimit != null);
        Contract.Requires(ORD_isSucc != null);
        Contract.Requires(ORD_offset != null);
        Contract.Requires(ORD_isNat != null);
        Contract.Requires(mapDomain != null);
        Contract.Requires(imapDomain != null);
        Contract.Requires(mapValues != null);
        Contract.Requires(imapValues != null);
        Contract.Requires(mapItems != null);
        Contract.Requires(imapItems != null);
        Contract.Requires(tuple2Destructors0 != null);
        Contract.Requires(tuple2Destructors1 != null);
        Contract.Requires(tuple2Constructor != null);
        Contract.Requires(seqTypeCtor != null);
        Contract.Requires(bv0TypeDecl != null);
        Contract.Requires(fieldNameType != null);
        Contract.Requires(heap != null);
        Contract.Requires(classNameType != null);
        Contract.Requires(datatypeType != null);
        Contract.Requires(layerType != null);
        Contract.Requires(dtCtorId != null);
        Contract.Requires(allocField != null);
        Contract.Requires(tyType != null);
        Contract.Requires(tyTagType != null);
        Contract.Requires(tyTagFamilyType != null);
        #endregion

        this.CharType = new Bpl.CtorType(Token.NoToken, charType, new List<Bpl.Type>());
        Bpl.CtorType refT = new Bpl.CtorType(Token.NoToken, refType, new List<Bpl.Type>());
        this.RefType = refT;
        this.BoxType = new Bpl.CtorType(Token.NoToken, boxType, new List<Bpl.Type>());
        this.setTypeCtor = setTypeCtor;
        this.isetTypeCtor = isetTypeCtor;
        this.multiSetTypeCtor = multiSetTypeCtor;
        this.mapTypeCtor = mapTypeCtor;
        this.imapTypeCtor = imapTypeCtor;
        this.ArrayLength = arrayLength;
        this.RealFloor = realFloor;
        this.ORDINAL_IsLimit = ORD_isLimit;
        this.ORDINAL_IsSucc = ORD_isSucc;
        this.ORDINAL_Offset = ORD_offset;
        this.ORDINAL_IsNat = ORD_isNat;
        this.MapDomain = mapDomain;
        this.IMapDomain = imapDomain;
        this.MapValues = mapValues;
        this.IMapValues = imapValues;
        this.MapItems = mapItems;
        this.IMapItems = imapItems;
        this.ObjectTypeConstructor = objectTypeConstructor;
        this.Tuple2Destructors0 = tuple2Destructors0;
        this.Tuple2Destructors1 = tuple2Destructors1;
        this.Tuple2Constructor = tuple2Constructor;
        this.Tuple2TypeConstructor = tuple2TypeConstructor;
        this.seqTypeCtor = seqTypeCtor;
        this.Bv0Type = new Bpl.TypeSynonymAnnotation(Token.NoToken, bv0TypeDecl, new List<Bpl.Type>());
        this.fieldName = fieldNameType;
        this.HeapType = heap.TypedIdent.Type;
        this.HeapVarName = heap.Name;
        this.Ty = new Bpl.CtorType(Token.NoToken, tyType, new List<Bpl.Type>());
        this.TyTag = new Bpl.CtorType(Token.NoToken, tyTagType, new List<Bpl.Type>());
        this.TyTagFamily = new Bpl.CtorType(Token.NoToken, tyTagFamilyType, new List<Bpl.Type>());
        this.ClassNameType = new Bpl.CtorType(Token.NoToken, classNameType, new List<Bpl.Type>());
        this.NameFamilyType = new Bpl.CtorType(Token.NoToken, nameFamilyType, new List<Bpl.Type>());
        this.DatatypeType = new Bpl.CtorType(Token.NoToken, datatypeType, new List<Bpl.Type>());
        this.HandleType = new Bpl.CtorType(Token.NoToken, handleType, new List<Bpl.Type>());
        this.LayerType = new Bpl.CtorType(Token.NoToken, layerType, new List<Bpl.Type>());
        this.DtCtorId = new Bpl.CtorType(Token.NoToken, dtCtorId, new List<Bpl.Type>());
        this.AllocField = allocField;
        this.Null = new Bpl.IdentifierExpr(Token.NoToken, "null", refT);
      }
    }

    PredefinedDecls FindPredefinedDecls(Bpl.Program prog) {
      Contract.Requires(prog != null);
      if (prog.Resolve(options) != 0) {
        options.OutputWriter.WriteLine("Error: resolution errors encountered in Dafny prelude");
        return null;
      }

      Bpl.TypeCtorDecl charType = null;
      Bpl.TypeCtorDecl refType = null;
      Bpl.TypeSynonymDecl setTypeCtor = null;
      Bpl.TypeSynonymDecl isetTypeCtor = null;
      Bpl.TypeSynonymDecl multiSetTypeCtor = null;
      Bpl.Function arrayLength = null;
      Bpl.Function realFloor = null;
      Bpl.Function ORDINAL_isLimit = null;
      Bpl.Function ORDINAL_isSucc = null;
      Bpl.Function ORDINAL_offset = null;
      Bpl.Function ORDINAL_isNat = null;
      Bpl.Function mapDomain = null;
      Bpl.Function imapDomain = null;
      Bpl.Function mapValues = null;
      Bpl.Function imapValues = null;
      Bpl.Function mapItems = null;
      Bpl.Function imapItems = null;
      Bpl.Function objectTypeConstructor = null;
      Bpl.Function tuple2TypeConstructor = null;
      Bpl.Function tuple2Destructors0 = null;
      Bpl.Function tuple2Destructors1 = null;
      Bpl.Function tuple2Constructor = null;
      Bpl.TypeCtorDecl seqTypeCtor = null;
      Bpl.TypeCtorDecl fieldNameType = null;
      Bpl.TypeCtorDecl classNameType = null;
      Bpl.TypeSynonymDecl bv0TypeDecl = null;
      Bpl.TypeCtorDecl tyType = null;
      Bpl.TypeCtorDecl tyTagType = null;
      Bpl.TypeCtorDecl tyTagFamilyType = null;
      Bpl.TypeCtorDecl nameFamilyType = null;
      Bpl.TypeCtorDecl datatypeType = null;
      Bpl.TypeCtorDecl handleType = null;
      Bpl.TypeCtorDecl layerType = null;
      Bpl.TypeCtorDecl dtCtorId = null;
      Bpl.TypeCtorDecl boxType = null;
      Bpl.TypeCtorDecl mapTypeCtor = null;
      Bpl.TypeCtorDecl imapTypeCtor = null;
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
          } else if (dt.Name == "TyTagFamily") {
            tyTagFamilyType = dt;
          } else if (dt.Name == "DatatypeType") {
            datatypeType = dt;
          } else if (dt.Name == "HandleType") {
            handleType = dt;
          } else if (dt.Name == "LayerType") {
            layerType = dt;
          } else if (dt.Name == "DtCtorId") {
            dtCtorId = dt;
          } else if (dt.Name == "char") {
            charType = dt;
          } else if (dt.Name == "ref") {
            refType = dt;
          } else if (dt.Name == "NameFamily") {
            nameFamilyType = dt;
          } else if (dt.Name == "Box") {
            boxType = dt;
          } else if (dt.Name == "Map") {
            mapTypeCtor = dt;
          } else if (dt.Name == "IMap") {
            imapTypeCtor = dt;
          }
        } else if (d is Bpl.TypeSynonymDecl) {
          Bpl.TypeSynonymDecl dt = (Bpl.TypeSynonymDecl)d;
          if (dt.Name == "Set") {
            setTypeCtor = dt;
          } else if (dt.Name == "MultiSet") {
            multiSetTypeCtor = dt;
          } else if (dt.Name == "ISet") {
            isetTypeCtor = dt;
          } else if (dt.Name == "Bv0") {
            bv0TypeDecl = dt;
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
          } else if (f.Name == "_System.real.Floor") {
            realFloor = f;
          } else if (f.Name == "ORD#IsLimit") {
            ORDINAL_isLimit = f;
          } else if (f.Name == "ORD#IsSucc") {
            ORDINAL_isSucc = f;
          } else if (f.Name == "ORD#Offset") {
            ORDINAL_offset = f;
          } else if (f.Name == "ORD#IsNat") {
            ORDINAL_isNat = f;
          } else if (f.Name == "Map#Domain") {
            mapDomain = f;
          } else if (f.Name == "IMap#Domain") {
            imapDomain = f;
          } else if (f.Name == "Map#Values") {
            mapValues = f;
          } else if (f.Name == "IMap#Values") {
            imapValues = f;
          } else if (f.Name == "Map#Items") {
            mapItems = f;
          } else if (f.Name == "IMap#Items") {
            imapItems = f;
          } else if (f.Name == "_System.Tuple2._0") {
            tuple2Destructors0 = f;
          } else if (f.Name == "_System.Tuple2._1") {
            tuple2Destructors1 = f;
          } else if (f.Name == "#_System._tuple#2._#Make2") {
            tuple2Constructor = f;
          } else if (f.Name == "Tclass._System.Tuple2") {
            tuple2TypeConstructor = f;
          } else if (f.Name == "Tclass._System.object?") {
            objectTypeConstructor = f;
          }
        }
      }
      if (seqTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Seq");
      } else if (setTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Set");
      } else if (isetTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type ISet");
      } else if (multiSetTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type MultiSet");
      } else if (mapTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Map");
      } else if (imapTypeCtor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type IMap");
      } else if (arrayLength == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function _System.array.Length");
      } else if (realFloor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function _System.real.Floor");
      } else if (ORDINAL_isLimit == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsLimit");
      } else if (ORDINAL_isSucc == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsSucc");
      } else if (ORDINAL_offset == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function ORD#Offset");
      } else if (ORDINAL_isNat == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsNat");
      } else if (mapDomain == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function Map#Domain");
      } else if (imapDomain == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Domain");
      } else if (mapValues == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function Map#Values");
      } else if (imapValues == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Values");
      } else if (mapItems == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function Map#Items");
      } else if (imapItems == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Items");
      } else if (tuple2Destructors0 == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function _System.Tuple2._0");
      } else if (tuple2Destructors1 == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function _System.Tuple2._1");
      } else if (tuple2Constructor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of function #_System._tuple#2._#Make2");
      } else if (bv0TypeDecl == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Bv0");
      } else if (fieldNameType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Field");
      } else if (classNameType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type ClassName");
      } else if (tyType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Ty");
      } else if (tyTagType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type TyTag");
      } else if (tyTagFamilyType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type TyTagFamily");
      } else if (nameFamilyType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type NameFamily");
      } else if (datatypeType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type DatatypeType");
      } else if (handleType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type HandleType");
      } else if (layerType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type LayerType");
      } else if (dtCtorId == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type DtCtorId");
      } else if (charType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type char");
      } else if (refType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type ref");
      } else if (boxType == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of type Box");
      } else if (heap == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of $Heap");
      } else if (allocField == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of constant alloc");
      } else if (tuple2TypeConstructor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of tuple2TypeConstructor");
      } else if (objectTypeConstructor == null) {
        options.OutputWriter.WriteLine("Error: Dafny prelude is missing declaration of objectTypeConstructor");
      } else {
        return new PredefinedDecls(charType, refType, boxType,
                                   setTypeCtor, isetTypeCtor, multiSetTypeCtor,
                                   mapTypeCtor, imapTypeCtor,
                                   arrayLength, realFloor,
                                   ORDINAL_isLimit, ORDINAL_isSucc, ORDINAL_offset, ORDINAL_isNat,
                                   mapDomain, imapDomain,
                                   mapValues, imapValues, mapItems, imapItems,
                                   objectTypeConstructor,
                                   tuple2Destructors0, tuple2Destructors1, tuple2Constructor, tuple2TypeConstructor,
                                   seqTypeCtor, bv0TypeDecl,
                                   fieldNameType, tyType, tyTagType, tyTagFamilyType,
                                   heap, classNameType, nameFamilyType,
                                   datatypeType, handleType, layerType, dtCtorId,
                                   allocField);
      }
      return null;
    }

    Bpl.Program ReadPrelude() {
      string preludePath = options.DafnyPrelude;
      if (preludePath == null) {
        //using (System.IO.Stream stream = cce.NonNull( System.Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream("DafnyPrelude.bpl")) // Use this once Spec#/VSIP supports designating a non-.resx project item as an embedded resource
        string codebase = cce.NonNull(System.IO.Path.GetDirectoryName(cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
        preludePath = System.IO.Path.Combine(codebase, "DafnyPrelude.bpl");
      }

      var defines = new List<string>();
      if (6 <= options.ArithMode) {
        defines.Add("ARITH_DISTR");
      }
      if (8 <= options.ArithMode) {
        defines.Add("ARITH_MUL_DIV_MOD");
      }
      if (9 <= options.ArithMode) {
        defines.Add("ARITH_MUL_SIGN");
      }
      if (10 <= options.ArithMode) {
        defines.Add("ARITH_MUL_COMM");
        defines.Add("ARITH_MUL_ASSOC");
      }
      if (options.Get(CommonOptionBag.UnicodeCharacters)) {
        defines.Add("UNICODE_CHAR");
      }
      int errorCount = BplParser.Parse(preludePath, defines, out var prelude);
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
      return new Bpl.IdentifierExpr(tok, var.AssignUniqueName(currentDeclaration.IdGenerator), TrType(var.Type));
    }

    public Bpl.Program DoTranslation(Program p, ModuleDefinition forModule) {
      if (sink == null) {
        return new Bpl.Program();
      }

      foreach (var plugin in p.Options.Plugins) {
        foreach (var rewriter in plugin.GetRewriters(p.Reporter)) {
          rewriter.PreVerify(forModule);
        }
      }

      program = p;
      this.forModule = forModule;
      Type.EnableScopes();

      EstablishModuleScope(p.SystemModuleManager.SystemModule, forModule);
      Type.PushScope(this.currentScope);

      foreach (var w in program.SystemModuleManager.Bitwidths) {
        // type axioms
        AddBitvectorTypeAxioms(w);
        // bitwise operations
        AddBitvectorFunction(w, "and_bv", "bvand");
        AddBitvectorFunction(w, "or_bv", "bvor");
        AddBitvectorFunction(w, "xor_bv", "bvxor");  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
        AddBitvectorFunction(w, "not_bv", "bvnot", false);
        // arithmetic operations
        AddBitvectorFunction(w, "add_bv", "bvadd");
        AddBitvectorFunction(w, "sub_bv", "bvsub");  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
        AddBitvectorFunction(w, "mul_bv", "bvmul");
        AddBitvectorFunction(w, "div_bv", "bvudiv");
        AddBitvectorFunction(w, "mod_bv", "bvurem");
        // comparisons
        AddBitvectorFunction(w, "lt_bv", "bvult", true, Bpl.Type.Bool, false);
        AddBitvectorFunction(w, "le_bv", "bvule", true, Bpl.Type.Bool, true);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
        AddBitvectorFunction(w, "ge_bv", "bvuge", true, Bpl.Type.Bool, true);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
        AddBitvectorFunction(w, "gt_bv", "bvugt", true, Bpl.Type.Bool, false);  // Z3 supports this, but it seems not to be in the SMT-LIB 2 standard
        // shifts
        AddBitvectorShiftFunction(w, "LeftShift_bv", "bvshl");
        AddBitvectorShiftFunction(w, "RightShift_bv", "bvlshr");
        // rotates
        AddBitvectorShiftFunction(w, "LeftRotate_bv", "ext_rotate_left");
        AddBitvectorShiftFunction(w, "RightRotate_bv", "ext_rotate_right");
        // conversion functions
        AddBitvectorNatConversionFunction(w);
      }

      foreach (TopLevelDecl d in program.SystemModuleManager.SystemModule.TopLevelDecls) {
        currentDeclaration = d;
        if (d is AbstractTypeDecl abstractType) {
          GetOrCreateTypeConstructor(abstractType);
          AddClassMembers(abstractType, true, true);
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          AddTypeDecl(dd);
          AddClassMembers(dd, true, true);
        } else if (d is SubsetTypeDecl) {
          AddTypeDecl((SubsetTypeDecl)d);
        } else if (d is TypeSynonymDecl) {
          // do nothing, just bypass type synonyms in the translation
        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          AddDatatype(dd);
          AddClassMembers(dd, true, true);
        } else if (d is ArrowTypeDecl) {
          var ad = (ArrowTypeDecl)d;
          GetClassTyCon(ad);
          AddArrowTypeAxioms(ad);
        } else if (d is ClassLikeDecl) {
          var cl = (ClassLikeDecl)d;
          AddClassMembers(cl, true, true);
          if (cl.NonNullTypeDecl != null) {
            AddTypeDecl(cl.NonNullTypeDecl);
          }
        } else {
          Contract.Assert(d is ValuetypeDecl);
        }
      }

      ComputeFunctionFuel(); // compute which function needs fuel constants.

      //translate us first
      List<ModuleDefinition> mods = program.RawModules().ToList();
      mods.Remove(forModule);
      mods.Insert(0, forModule);

      var visibleTopLevelDecls =
        mods.SelectMany(m => m.TopLevelDecls.Where(VisibleInScope));

      if (visibleTopLevelDecls.Any(
            d => d is TopLevelDeclWithMembers memberContainer &&
                 memberContainer.Members.Any(
                   member =>
                     Attributes.Contains(member.Attributes, "only")
                 ))) {
        filterOnlyMembers = true;
      }

      foreach (TopLevelDecl d in visibleTopLevelDecls) {
        currentDeclaration = d;
        if (d is AbstractTypeDecl abstractType) {
          AddClassMembers(abstractType, true, true);
        } else if (d is ModuleDecl) {
          // submodules have already been added as a top level module, ignore this.
        } else if (d is RevealableTypeDecl revealableTypeDecl) {
          AddRevealableTypeDecl(revealableTypeDecl);
        } else {
          Contract.Assert(false);
        }
      }

      filterOnlyMembers = false;

      foreach (var c in tytagConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }
      foreach (var c in fieldConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }

      AddTraitParentAxioms();

      if (InsertChecksums) {
        foreach (var impl in sink.Implementations) {
          if (impl.FindAttribute("checksum") == null) {
            impl.AddAttribute("checksum", "stable");
          }
        }
        foreach (var func in sink.Functions) {
          if (func.FindAttribute("checksum") == null) {
            func.AddAttribute("checksum", "stable");
          }
        }
      }

      Type.PopScope(this.currentScope);
      Type.DisableScopes();
      return sink;

    }

    // Don't verify modules which only contain other modules
    private static bool ShouldVerifyModule(Program program, ModuleDefinition m) {
      if (!m.ShouldVerify(program.Compilation)) {
        return false;
      }

      foreach (var top in m.TopLevelDecls) {
        if (top is DefaultClassDecl) {
          if (((DefaultClassDecl)top).Members.Count > 0) {
            return true;
          }
        } else if (!(top is ModuleDecl)) {
          return true;
        }
      }
      return false;
    }

    public static IEnumerable<ModuleDefinition> VerifiableModules(Program p) {
      return p.RawModules().Where(m => ShouldVerifyModule(p, m));
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(Program p, ErrorReporter reporter, TranslatorFlags flags = null) {
      Contract.Requires(p != null);
      Contract.Requires(p.ModuleSigs.Count > 0);

      Type.ResetScopes();

      foreach (ModuleDefinition outerModule in VerifiableModules(p)) {
        var translator = new BoogieGenerator(reporter, p.ProofDependencyManager, flags);

        if (translator.sink == null || translator.sink == null) {
          // something went wrong during construction, which reads the prelude; an error has
          // already been printed, so just return an empty program here (which is non-null)
          yield return new Tuple<string, Bpl.Program>(outerModule.SanitizedName, new Bpl.Program());
        }
        yield return new Tuple<string, Bpl.Program>(outerModule.SanitizedName, translator.DoTranslation(p, outerModule));
      }
    }

    /// <summary>
    /// Declare and add to the sink a Boogie function named "namePrefix + w".
    /// If "binary", then the function takes two arguments; otherwise, it takes one.  Arguments have the type
    /// corresponding to the Dafny type for w-width bitvectors.
    /// The function's result type is the same as the argument type, unless "resultType" is non-null, in which
    /// case the function's result type is "resultType".
    /// For w > 0:
    ///     Attach an attribute {:bvbuiltin smtFunctionName}.
    /// For w == 0:
    ///     Attach an attribute {:inline} and add a .Body to the function.
    ///     If "resultType" is null, then use 0 as the body; otherwise, use "bodyForBv0" as the body (which
    ///     assumes "resultType" is actually Bpl.Type.Bool).
    /// </summary>
    private void AddBitvectorFunction(int w, string namePrefix, string smtFunctionName, bool binary = true, Bpl.Type resultType = null, bool bodyForBv0 = false) {
      Contract.Requires(0 <= w);
      Contract.Requires(namePrefix != null);
      Contract.Requires(smtFunctionName != null);
      var tok = Token.NoToken;
      var t = BplBvType(w);
      List<Bpl.Variable> args;
      if (binary) {
        var a0 = BplFormalVar(null, t, true);
        var a1 = BplFormalVar(null, t, true);
        args = new List<Variable>() { a0, a1 };
      } else {
        var a0 = BplFormalVar(null, t, true);
        args = new List<Variable>() { a0 };
      }
      var r = BplFormalVar(null, resultType ?? t, false);
      Bpl.QKeyValue attr;
      if (w == 0) {
        attr = InlineAttribute(tok);
      } else {
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
      }
      var func = new Bpl.Function(tok, namePrefix + w, new List<TypeVariable>(), args, r, null, attr);
      if (w == 0) {
        if (resultType != null) {
          func.Body = Bpl.Expr.Literal(bodyForBv0);
        } else {
          func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
        }
      }
      sink.AddTopLevelDeclaration(func);
    }

    private void AddBitvectorShiftFunction(int w, string namePrefix, string smtFunctionName) {
      Contract.Requires(0 <= w);
      Contract.Requires(namePrefix != null);
      Contract.Requires(smtFunctionName != null);
      var tok = Token.NoToken;
      var t = BplBvType(w);
      List<Bpl.Variable> args;
      var a0 = BplFormalVar(null, t, true);
      var a1 = BplFormalVar(null, t, true);
      args = new List<Variable>() { a0, a1 };
      var r = BplFormalVar(null, t, false);
      Bpl.QKeyValue attr;
      if (w == 0) {
        attr = InlineAttribute(tok);
      } else {
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
      }
      var func = new Bpl.Function(tok, namePrefix + w, new List<TypeVariable>(), args, r, null, attr);
      if (w == 0) {
        func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
      }
      sink.AddTopLevelDeclaration(func);
    }

    private void AddBitvectorNatConversionFunction(int w) {
      Contract.Requires(0 <= w);
      var tok = Token.NoToken;
      var bv = BplBvType(w);
      Bpl.QKeyValue attr;
      Bpl.Function func;

      // function {:bvbuiltin "(_ int2bv 67)"} nat_to_bv67(int) : bv67;
      // OR:
      // function {:inline} nat_to_bv0(int) : Bv0 { ZERO }
      if (w == 0) {
        attr = InlineAttribute(tok);
      } else {
        var smt_int2bv = string.Format("(_ int2bv {0})", w);
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smt_int2bv }, null);  // SMT-LIB 2 calls this function nat2bv, but Z3 apparently calls it int2bv
      }
      func = new Bpl.Function(tok, "nat_to_bv" + w, new List<TypeVariable>(),
        new List<Variable>() { BplFormalVar(null, Bpl.Type.Int, true) }, BplFormalVar(null, bv, false),
        null, attr);
      if (w == 0) {
        func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
      }
      sink.AddTopLevelDeclaration(func);

      if (w == 0) {
        // function {:inline} nat_from_bv0_smt(Bv0) : int { 0 }
        attr = InlineAttribute(tok);
        func = new Bpl.Function(tok, "nat_from_bv" + w, new List<TypeVariable>(),
          new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
          null, attr);
        func.Body = Bpl.Expr.Literal(0);
        sink.AddTopLevelDeclaration(func);
      } else {
        // function {:bvbuiltin "bv2int"} smt_nat_from_bv67(bv67) : int;
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { "bv2int" }, null);  // SMT-LIB 2 calls this function bv2nat, but Z3 apparently calls it bv2int
        var smtFunc = new Bpl.Function(tok, "smt_nat_from_bv" + w, new List<TypeVariable>(),
          new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
          null, attr);
        sink.AddTopLevelDeclaration(smtFunc);
        // function nat_from_bv67(bv67) : int;
        func = new Bpl.Function(tok, "nat_from_bv" + w, new List<TypeVariable>(),
          new List<Variable>() { BplFormalVar(null, bv, true) }, BplFormalVar(null, Bpl.Type.Int, false),
          null, null);
        sink.AddTopLevelDeclaration(func);
        // axiom (forall b: bv67 :: { nat_from_bv67(b) }
        //          0 <= nat_from_bv67(b) && nat_from_bv67(b) < 0x8_0000_0000_0000_0000 &&
        //          nat_from_bv67(b) == smt_nat_from_bv67(b));
        var bVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "b", BplBvType(w)));
        var b = new Bpl.IdentifierExpr(tok, bVar);
        var bv2nat = FunctionCall(tok, "nat_from_bv" + w, Bpl.Type.Int, b);
        var smt_bv2nat = FunctionCall(tok, "smt_nat_from_bv" + w, Bpl.Type.Int, b);
        var body = BplAnd(BplAnd(
          Bpl.Expr.Le(Bpl.Expr.Literal(0), bv2nat),
          Bpl.Expr.Lt(bv2nat, Bpl.Expr.Literal(BaseTypes.BigNum.FromBigInt(BigInteger.One << w)))),
          Bpl.Expr.Eq(bv2nat, smt_bv2nat));
        var ax = new Bpl.ForallExpr(tok, new List<Variable>() { bVar }, BplTrigger(bv2nat), body);
        sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, ax));
      }
    }

    private void ComputeFunctionFuel() {
      foreach (ModuleDefinition m in program.RawModules()) {
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          if (d is TopLevelDeclWithMembers) {
            var c = (TopLevelDeclWithMembers)d;
            foreach (MemberDecl member in c.Members) {
              if (member is Function && RevealedInScope(member)) {
                Function f = (Function)member;
                // declare the fuel constant
                if (f.IsFueled) {
                  // const BaseFuel_FunctionA : LayerType
                  Bpl.Constant baseFuel = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, "BaseFuel_" + f.FullName, predef.LayerType), false);
                  sink.AddTopLevelDeclaration(baseFuel);
                  Bpl.Expr baseFuel_expr = new Bpl.IdentifierExpr(f.tok, baseFuel);
                  // const StartFuel_FunctionA : LayerType
                  Bpl.Constant startFuel = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, "StartFuel_" + f.FullName, predef.LayerType), false);
                  sink.AddTopLevelDeclaration(startFuel);
                  Bpl.Expr startFuel_expr = new Bpl.IdentifierExpr(f.tok, startFuel);
                  // const StartFuelAssert_FunctionA : LayerType
                  Bpl.Constant startFuelAssert = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, "StartFuelAssert_" + f.FullName, predef.LayerType), false);
                  sink.AddTopLevelDeclaration(startFuelAssert);
                  Bpl.Expr startFuelAssert_expr = new Bpl.IdentifierExpr(f.tok, startFuelAssert);
                  this.functionFuel.Add(new FuelConstant(f, baseFuel_expr, startFuel_expr, startFuelAssert_expr));
                }

                if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
                  CreateRevealableConstant(f);
                }
              }
            }
          }
        }
      }
    }

    private void CreateRevealableConstant(Function f) {
      if (!this.functionReveals.ContainsKey(f)) {
        // const reveal_FunctionA : bool
        Bpl.Constant revealTrigger =
          new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, "reveal_" + f.FullName, Bpl.Type.Bool), false);
        sink.AddTopLevelDeclaration(revealTrigger);
        Bpl.Expr revealTrigger_expr = new Bpl.IdentifierExpr(f.tok, revealTrigger);
        this.functionReveals[f] = revealTrigger_expr;
      }
    }

    /// <summary>
    /// For every revealed type (class or trait) C<T> that extends a trait J<G(T)>, add:
    ///   axiom (forall T: Ty, $o: ref ::
    ///       { $Is($o, C(T)) }
    ///       $o != null && $Is($o, C(T)) ==> $Is($o, J(G(T)));
    ///   axiom (forall T: Ty, $Heap: Heap, $o: ref ::
    ///       { $IsAlloc($o, C(T), $Heap) }
    ///       $o != null && $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
    /// Note:
    ///   It is sometimes useful also to be able to determine the _absence_ of trait-parent relationships.
    ///   For example, suppose one can tell from the looking at the "extends" clauses in a program
    ///   that a class C does not (directly or transitively) extend a trait T. Then, given variables c and t
    ///   of static types C and T, respectively, the verifier should be able to infer c != t. This is not
    ///   possible with the axioms below. It will require an axiomatization of _all_ possible parent traits, not just
    ///   saying that some are possible. When this becomes needed, the axiomatization will need to be
    ///   embellished.
    /// </summary>
    private void AddTraitParentAxioms() {
      foreach (ModuleDefinition m in program.RawModules()) {
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          var c = d as TopLevelDeclWithMembers;
          if (c == null || !RevealedInScope(d)) {
            continue;
          }
          foreach (var parentType in c.ParentTraits) {
            var childType = UserDefinedType.FromTopLevelDecl(c.tok, c);

            Bpl.Expr heap; var heapVar = BplBoundVar("$heap", predef.HeapType, out heap);
            Bpl.Expr o; var oVar = BplBoundVar("$o", TrType(childType), out o);
            Bpl.Expr oNotNull = childType.IsRefType ? Bpl.Expr.Neq(o, predef.Null) : Bpl.Expr.True;

            var oj = BoxifyForTraitParent(c.tok, o, ((UserDefinedType)parentType.NormalizeExpand()).ResolvedClass, childType);

            List<Bpl.Expr> tyexprs;
            var bvarsTypeParameters = MkTyParamBinders(GetTypeParams(c), out tyexprs);

            // axiom (forall T: Ty, $o: ref ::
            //     { $Is($o, C(T)) }
            //     $o != null && $Is($o, C(T)) ==> $Is($o, J(G(T)));
            var isC = MkIs(o, childType);
            var isJ = MkIs(oj, parentType);
            var bvs = new List<Bpl.Variable>();
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            var tr = BplTrigger(isC);
            var body = BplImp(BplAnd(oNotNull, isC), isJ);

            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body),
              $"type axiom for trait parent: {d} extends {parentType}"));

            // axiom (forall T: Ty, $Heap: Heap, $o: ref ::
            //     { $IsAlloc($o, C(T), $Heap) }
            //     $o != null && $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
            var isAllocC = MkIsAlloc(o, childType, heap);
            var isAllocJ = MkIsAlloc(oj, parentType, heap);
            bvs = new List<Bpl.Variable>();
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            bvs.Add(heapVar);
            tr = BplTrigger(isAllocC);
            body = BplImp(BplAnd(oNotNull, isAllocC), isAllocJ);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body),
              $"allocation axiom for trait parent: {d} extends {parentType}"));
          }
        }
      }
    }

    /// <summary>
    /// Construct an expression denoting the equality of e0 and e1, taking advantage of
    /// any available extensional equality based on the given Dafny type.
    /// </summary>
    public Expr TypeSpecificEqual(IToken tok, Dafny.Type type, Expr e0, Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);

      if (type.AsSetType != null) {
        var finite = type.AsSetType.Finite;
        return FunctionCall(tok, finite ? BuiltinFunction.SetEqual : BuiltinFunction.ISetEqual, null, e0, e1);
      } else if (type.AsMapType != null) {
        var finite = type.AsMapType.Finite;
        return FunctionCall(tok, finite ? BuiltinFunction.MapEqual : BuiltinFunction.IMapEqual, null, e0, e1);
      } else if (type.AsMultiSetType != null) {
        return FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
      } else if (type.AsSeqType != null) {
        return FunctionCall(tok, BuiltinFunction.SeqEqual, null, e0, e1);
      } else if (type.IsIndDatatype) {
        return FunctionCall(tok, type.AsIndDatatype.FullSanitizedName + "#Equal", Bpl.Type.Bool, e0, e1);
      } else {
        return Bpl.Expr.Eq(e0, e1);
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
            var lexprs = Map(ty.TypeArgs, tt => tt.Subst(lsu));
            var rexprs = Map(ty.TypeArgs, tt => tt.Subst(rsu));
            q = CoEqualCall(codecl, lexprs, rexprs, k, l, a, b);
          } else {
            // ordinary equality; let the usual translation machinery figure out the translation
            var tyA = ty.Subst(lsu);
            var tyB = ty.Subst(rsu);
            var aa = CondApplyUnbox(tok, a, ty, tyA);
            var bb = CondApplyUnbox(tok, b, ty, tyB);
            var equal = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, new BoogieWrapper(aa, tyA), new BoogieWrapper(bb, tyB));
            equal.ResolvedOp = ModuleResolver.ResolveOp(equal.Op, tyA, tyB);  // resolve here
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

    public Bpl.Expr LayerSucc(Bpl.Expr e, int amt = 1) {
      if (amt == 0) {
        return e;
      } else if (amt > 0) {
        return FunctionCall(e.tok, BuiltinFunction.LayerSucc, null, LayerSucc(e, amt - 1));
      } else {
        Contract.Assert(false);
        return null;
      }
    }

    // Makes a call to equality, if k is null, or otherwise prefix equality. For codatatypes.
    Bpl.Expr CoEqualCall(CoDatatypeDecl codecl, List<Bpl.Expr> largs, List<Bpl.Expr> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, Bpl.IToken tok = null) {
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

    void CreateBoundVariables<VT>(List<VT> formals, out List<Variable> bvs, out List<Bpl.Expr> args) where VT : IVariable {
      Contract.Requires(formals != null);
      Contract.Ensures(Contract.ValueAtReturn(out bvs).Count == Contract.ValueAtReturn(out args).Count);
      Contract.Ensures(Contract.ValueAtReturn(out bvs) != null);
      Contract.Ensures(cce.NonNullElements(Contract.ValueAtReturn(out args)));

      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("a#");
      bvs = new List<Variable>();
      args = new List<Bpl.Expr>();
      foreach (var arg in formals) {
        Contract.Assert(arg != null);
        var nm = varNameGen.FreshId(string.Format("#{0}#", bvs.Count));
        Bpl.Variable bv = new Bpl.BoundVariable(arg.Tok, new Bpl.TypedIdent(arg.Tok, nm, TrType(arg.Type)));
        bvs.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.Tok, bv));
      }
    }

    // This one says that this is /directly/ allocated, not that its "children" are,
    // i.e. h[x, alloc]
    public Bpl.Expr IsAlloced(IToken tok, Bpl.Expr heapExpr, Bpl.Expr e) {
      Contract.Requires(tok != null);
      Contract.Requires(heapExpr != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return ReadHeap(tok, heapExpr, e, predef.Alloc(tok), Bpl.Type.Bool);
    }

    public static Bpl.Expr ReadHeap(IToken tok, Expr heap, Expr r, Expr f, Bpl.Type ty = null) {
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
      Bpl.Expr readCall =
        new Bpl.NAryExpr(tok,
          new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "read", t.AsCtor.Arguments[0])),
          args);
      // Add a type coercion if supplied
      if (ty is not null) {
        Contract.Assert(ty.Equals(t.AsCtor.Arguments[0]));
      }
      return ty is null ? readCall : Bpl.Expr.CoerceType(tok, readCall, ty);
    }

    public static Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      List<Bpl.Expr> args = new List<Bpl.Expr>();
      args.Add(heap);
      args.Add(r);
      return new Bpl.NAryExpr(tok,
        new Bpl.MapSelect(tok, 1),
        args);
    }

    public static Boogie.NAryExpr UpdateHeap(IToken tok, Expr heap, Expr r, Expr f, Expr v) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Requires(v != null);
      Contract.Ensures(Contract.Result<Boogie.NAryExpr>() != null);

      List<Boogie.Expr> args = new List<Boogie.Expr>();
      args.Add(heap);
      args.Add(r);
      args.Add(f);
      args.Add(v);
      return new Boogie.NAryExpr(tok,
        new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, "update", heap.Type)),
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

    /// <summary>
    /// Returns true if the body of function "f" is available in module "context".
    /// This happens when the following conditions all hold:
    ///   - "f" has a body
    ///   - "f" is not opaque
    /// </summary>
    bool FunctionBodyIsAvailable(Function f, ModuleDefinition context, VisibilityScope scope, bool revealProtectedBody) {
      Contract.Requires(f != null);
      Contract.Requires(context != null);
      return f.Body != null && !IsOpaque(f) && f.IsRevealedInScope(scope);
    }
    bool IsOpaque(MemberDecl f) {
      Contract.Requires(f != null);
      if (f is Function f1) {
        return Attributes.Contains(f.Attributes, "opaque") || f.IsOpaque || f1.IsMadeImplicitlyOpaque(options);
      } else {
        return Attributes.Contains(f.Attributes, "opaque") || f.IsOpaque;
      }
    }
    static bool IsOpaqueRevealLemma(Method m) {
      Contract.Requires(m != null);
      return Attributes.Contains(m.Attributes, "opaque_reveal");
    }


    void AddEnsures(List<Bpl.Ensures> list, Bpl.Ensures ens) {
      list.Add(ens);
      if (!ens.Free) {
        this.assertionCount++;
      }
    }

    private Implementation AddImplementationWithVerboseName(IToken tok, Procedure proc, List<Variable> inParams,
      List<Variable> outParams, List<Variable> localVariables, StmtList stmts, QKeyValue kv) {
      Bpl.Implementation impl = new Bpl.Implementation(tok, proc.Name,
        new List<Bpl.TypeVariable>(), inParams, outParams,
        localVariables, stmts, kv);
      AddVerboseName(impl, proc.VerboseName);
      sink.AddTopLevelDeclaration(impl);
      return impl;
    }

    bool EmitImplementation(Attributes attributes) {
      // emit the impl only when there are proof obligations
      if (assertionCount > 0) {
        return true;
      } else {
        return false;
      }
    }

    private void Reset() {
      currentModule = null;
      codeContext = null;
      CurrentIdGenerator.Reset();
      _tmpIEs.Clear();
      assertionCount = 0;
    }

    public static Bpl.QKeyValue InlineAttribute(Bpl.IToken tok, Bpl.QKeyValue/*?*/ next = null) {
      Contract.Requires(tok != null);
      return new QKeyValue(tok, "inline", new List<object>(), next);
    }

    class Specialization {
      public readonly List<Formal/*!*/> Formals;
      public readonly List<Expression/*!*/> ReplacementExprs;
      public readonly List<BoundVar/*!*/> ReplacementFormals;
      public readonly Dictionary<IVariable, Expression> SubstMap;
      readonly BoogieGenerator boogieGenerator;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(cce.NonNullElements(Formals));
        Contract.Invariant(cce.NonNullElements(ReplacementExprs));
        Contract.Invariant(Formals.Count == ReplacementExprs.Count);
        Contract.Invariant(cce.NonNullElements(ReplacementFormals));
        Contract.Invariant(SubstMap != null);
      }

      public Specialization(IVariable formal, MatchCase mc, Specialization prev, BoogieGenerator boogieGenerator) {
        Contract.Requires(formal is Formal || formal is BoundVar);
        Contract.Requires(mc != null);
        Contract.Requires(prev == null || formal is BoundVar || !prev.Formals.Contains((Formal)formal));
        Contract.Requires(boogieGenerator != null);

        this.boogieGenerator = boogieGenerator;

        List<Expression> rArgs = new List<Expression>();
        foreach (BoundVar p in mc.Arguments) {
          IdentifierExpr ie = new IdentifierExpr(p.tok, p.AssignUniqueName(boogieGenerator.currentDeclaration.IdGenerator));
          ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
          rArgs.Add(ie);
        }
        // create and resolve datatype value
        var r = new DatatypeValue(mc.tok, mc.Ctor.EnclosingDatatype.Name, mc.Ctor.Name, rArgs);
        r.Ctor = mc.Ctor;
        r.Type = new UserDefinedType(mc.tok, mc.Ctor.EnclosingDatatype.Name, new List<Type>()/*this is not right, but it seems like it won't matter here*/);

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
            ReplacementExprs.Add(BoogieGenerator.Substitute(e, null, substMap));
          }
          foreach (var rf in prev.ReplacementFormals) {
            if (rf != formal) {
              ReplacementFormals.Add(rf);
            }
          }
          foreach (var entry in prev.SubstMap) {
            SubstMap.Add(entry.Key, BoogieGenerator.Substitute(entry.Value, null, substMap));
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

    (int olderParameterCount, Bpl.Expr olderCondition) OlderCondition(Function f, Bpl.Expr funcAppl, List<Bpl.Variable> inParams) {
      Contract.Requires(f != null);
      Contract.Requires(funcAppl != null);
      Contract.Requires(inParams != null);

      var olderParameterCount = f.Formals.Count(formal => formal.IsOlder);
      if (olderParameterCount == 0) {
        // nothing to do
        return (olderParameterCount, Bpl.Expr.True);
      }

      // For a function F(older x: X, y: Y), generate:
      //     (forall h: Heap :: { OlderTag(h) }
      //         IsGoodHeap(h) && OlderTag(h) && F(x, y) && IsAlloc(y, Y, h)
      //         ==>  IsAlloc(x, X, h))
      var heapVar = BplBoundVar("$olderHeap", predef.HeapType, out var heap);
      var etran = new ExpressionTranslator(this, predef, heap);

      var isGoodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, heap);
      var olderTag = FunctionCall(f.tok, "$OlderTag", Bpl.Type.Bool, heap);
      Bpl.Expr older = Bpl.Expr.True;
      Bpl.Expr newer = Bpl.Expr.True;
      var i = 0;
      if (!f.IsStatic) {
        var th = new Bpl.IdentifierExpr(f.tok, inParams[i]);
        i++;
        var wh = GetWhereClause(f.tok, th, ModuleResolver.GetReceiverType(f.tok, f), etran, ISALLOC, true);
        newer = BplAnd(newer, wh);
      }
      foreach (var formal in f.Formals) {
        var p = new Bpl.IdentifierExpr(f.tok, inParams[i]);
        i++;
        var wh = GetWhereClause(formal.tok, p, formal.Type, etran, ISALLOC, true);
        if (wh != null) {
          if (formal.IsOlder) {
            older = BplAnd(older, wh);
          } else {
            newer = BplAnd(newer, wh);
          }
        }
      }
      Contract.Assert(i == inParams.Count); // we should have used all the given inParams by now

      var body = BplImp(BplAnd(BplAnd(isGoodHeap, olderTag), BplAnd(funcAppl, newer)), older);
      var tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { olderTag });
      var olderCondition = new Bpl.ForallExpr(f.tok, new List<Bpl.TypeVariable>(), new List<Variable>() { heapVar }, null, tr, body);
      return (olderParameterCount, olderCondition);
    }

    Bpl.Expr AxiomActivation(Function f, ExpressionTranslator etran) {
      Contract.Requires(f != null);
      Contract.Requires(etran != null);
      Contract.Requires(VisibleInScope(f));
      if (InVerificationScope(f)) {
        return
          Bpl.Expr.Le(Bpl.Expr.Literal(forModule.CallGraph.GetSCCRepresentativePredecessorCount(f)), etran.FunctionContextHeight());
      } else {
        return Bpl.Expr.True;
      }
    }


    Bpl.Type TrReceiverType(MemberDecl f) {
      Contract.Requires(f != null);
      return TrType(ModuleResolver.GetReceiverType(f.tok, f));
    }

    Bpl.Expr ReceiverNotNull(Bpl.Expr th) {
      Contract.Requires(th != null);
      if (th.Type == predef.RefType) {
        return Bpl.Expr.Neq(th, predef.Null);
      } else {
        return Bpl.Expr.True;
      }
    }

    void AddFuelSuccSynonymAxiom(Function f, bool forHandle = false) {
      Contract.Requires(f != null);
      Contract.Requires(f.IsFuelAware());
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
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        var bvReveal = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$reveal", Boogie.Type.Bool));
        formals.Add(bvReveal);
        var sReveal = new Bpl.IdentifierExpr(f.tok, bvReveal);
        args1.Add(sReveal);
        args0.Add(sReveal);
      }

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }
      if (!forHandle && f.ReadsHeap) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }

      if (!f.IsStatic) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }
      if (!forHandle) {
        foreach (var p in f.Formals) {
          bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
          formals.Add(bv);
          s = new Bpl.IdentifierExpr(f.tok, bv);
          args1.Add(s);
          args0.Add(s);
        }
      }

      var name = forHandle ? f.FullSanitizedName + "#Handle" : f.FullSanitizedName;
      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, name, TrType(f.ResultType)));
      var funcAppl1 = new Bpl.NAryExpr(f.tok, funcID, args1);
      var funcAppl0 = new Bpl.NAryExpr(f.tok, funcID, args0);

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { funcAppl1 });
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, new List<Bpl.TypeVariable>(), formals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
      AddOtherDefinition(GetOrCreateFunction(f), new Bpl.Axiom(f.tok, ax, "layer synonym axiom"));
    }

    void AddFuelZeroSynonymAxiom(Function f) {
      // axiom  // fuel axiom
      //   (forall s, $Heap, formals ::
      //       { f(AsFuelBottom(s), $Heap, formals) }
      //       f(s, $Heap, formals) == f($LZ, $Heap, formals));
      Contract.Requires(f != null);
      Contract.Requires(f.IsFuelAware());
      Contract.Requires(sink != null && predef != null);

      List<Bpl.Expr> tyargs;
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
      var args2 = new List<Bpl.Expr>(tyargs);
      var args1 = new List<Bpl.Expr>(tyargs);
      var args0 = new List<Bpl.Expr>(tyargs);

      var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
      formals.Add(bv);
      var s = new Bpl.IdentifierExpr(f.tok, bv);
      args2.Add(FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, s));
      args1.Add(s);
      args0.Add(new Bpl.IdentifierExpr(f.tok, "$LZ", predef.LayerType)); // $LZ
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        var bvReveal = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$reveal", Boogie.Type.Bool));
        formals.Add(bvReveal);
        var sReveal = new Bpl.IdentifierExpr(f.tok, bvReveal);
        args2.Add(sReveal);
        args1.Add(sReveal);
        args0.Add(sReveal);
      }

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }
      if (f.ReadsHeap) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }

      if (!f.IsStatic) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }
      foreach (var p in f.Formals) {
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }

      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
      var funcAppl2 = new Bpl.NAryExpr(f.tok, funcID, args2);
      var funcAppl1 = new Bpl.NAryExpr(f.tok, funcID, args1);
      var funcAppl0 = new Bpl.NAryExpr(f.tok, funcID, args0);

      Bpl.Trigger tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { funcAppl2 });
      Bpl.Expr ax = new Bpl.ForallExpr(f.tok, new List<Bpl.TypeVariable>(), formals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
      AddOtherDefinition(GetOrCreateFunction(f), (new Bpl.Axiom(f.tok, ax, "fuel synonym axiom")));
    }

    Bpl.Expr InSeqRange(IToken tok, Bpl.Expr index, Type indexType, Bpl.Expr seq, bool isSequence, Bpl.Expr lowerBound, bool includeUpperBound) {
      Contract.Requires(tok != null);
      Contract.Requires(index != null);
      Contract.Requires(indexType != null);
      Contract.Requires(seq != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (indexType.IsBitVectorType) {
        index = ConvertExpression(tok, index, indexType, Type.Int);
      }
      Bpl.Expr lower;
      if (indexType.IsBitVectorType && lowerBound == null) {
        lower = Bpl.Expr.True;  // bitvectors are always non-negative
      } else {
        lower = Bpl.Expr.Le(lowerBound ?? Bpl.Expr.Literal(0), index);
      }
      Bpl.Expr length = isSequence ?
        FunctionCall(tok, BuiltinFunction.SeqLength, null, seq) :
        ArrayLength(tok, seq, 1, 0);
      Bpl.Expr upper;
      if (includeUpperBound) {
        upper = Bpl.Expr.Le(index, length);
      } else {
        upper = Bpl.Expr.Lt(index, length);
      }
      return BplAnd(lower, upper);
    }

    ModuleDefinition currentModule = null;  // the module whose members are currently being translated
    ModuleDefinition forModule = null;  // the root module
    ICallable codeContext = null;  // the method/iterator whose implementation is currently being translated or the function whose specification is being checked for well-formedness
    Bpl.LocalVariable yieldCountVariable = null;  // non-null when an iterator body is being translated
    bool inBodyInitContext = false;  // true during the translation of the .BodyInit portion of a divided constructor body
    readonly Dictionary<string, Bpl.IdentifierExpr> definiteAssignmentTrackers = new Dictionary<string, Bpl.IdentifierExpr>();
    bool assertAsAssume = false; // generate assume statements instead of assert statements
    Func<IToken, bool> assertionOnlyFilter = null; // generate assume statements instead of assert statements if not targeted by {:only}
    public enum StmtType { NONE, ASSERT, ASSUME };
    public StmtType stmtContext = StmtType.NONE;  // the Statement that is currently being translated
    public bool adjustFuelForExists = true;  // fuel need to be adjusted for exists based on whether exists is in assert or assume stmt.

    public readonly FreshIdGenerator defaultIdGenerator = new FreshIdGenerator();

    public FreshIdGenerator CurrentIdGenerator {
      get {
        var decl = codeContext as Declaration;
        if (decl != null) {
          return decl.IdGenerator;
        }
        return defaultIdGenerator;
      }
    }

    Dictionary<string, Bpl.IdentifierExpr> _tmpIEs = new Dictionary<string, Bpl.IdentifierExpr>();

    public int assertionCount = 0;

    Bpl.IdentifierExpr GetTmpVar_IdExpr(Bpl.IToken tok, string name, Bpl.Type ty, List<Variable> locals)  // local variable that's shared between statements that need it
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
    Bpl.Expr SaveInTemp(Bpl.Expr expr, bool otherExprsCanAffectPreviouslyKnownExpressions, string name, Bpl.Type ty, BoogieStmtListBuilder builder, List<Variable> locals) {
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

    void InitializeFuelConstant(IToken tok, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      if (this.functionFuel.Count > 0) {
        builder.Add(new CommentCmd("initialize fuel constant"));
      }
      FuelContext fuelContext = this.fuelContext;
      foreach (FuelConstant fuelConstant in this.functionFuel) {
        Function f = fuelConstant.f;
        Bpl.Expr baseFuel = fuelConstant.baseFuel;
        Bpl.Expr startFuel = fuelConstant.startFuel;
        Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
        // find out what the initial value should be
        FuelSettingPair settings;
        var found = fuelContext.TryGetValue(f, out settings);
        if (!found) {
          // If the context doesn't define fuel for this function, check for a fuel attribute (which supplies a default value if none is found)
          settings = FuelSetting.FuelAttrib(f, out found);
        }

        if (settings.low == 0 && settings.high == 0) {
          // Don't say anything about what startFuel and startFuel are set to
          // Just add the fixpoints that allow us to shortcut to LZ:
          // assume AsFuelBottom(startFuel) == startFuel
          // assume AsFuelBottom(startFuelAssert) == startFuelAssert
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, startFuel), startFuel)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, startFuelAssert), startFuelAssert)));
        } else {
          Bpl.Expr layer = etran.layerInterCluster.LayerN(settings.low, baseFuel);
          Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(settings.high, baseFuel);
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuel, layer)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuelAssert, layerAssert)));
          // assume AsFuelBottom(BaseFuel_F) == BaseFuel_F;
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, baseFuel), baseFuel)));
        }
      }
    }

    bool DefineFuelConstant(IToken tok, Attributes attribs, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      bool defineFuel = false;
      builder.Add(new CommentCmd("Assume Fuel Constant"));
      FuelContext fuelContext = new FuelContext();
      FuelSetting.FindFuelAttributes(attribs, fuelContext);
      foreach (KeyValuePair<Function, FuelSettingPair> fuel in fuelContext) {
        Function f = fuel.Key;
        FuelSettingPair settings = fuel.Value;
        FuelConstant fuelConstant = this.functionFuel.Find(x => x.f == f);
        if (fuelConstant != null) {
          Bpl.Expr startFuel = fuelConstant.startFuel;
          Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
          Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, predef, f.IdGenerator);
          Bpl.Expr layer = etran.layerInterCluster.LayerN(settings.low, moreFuel_expr);
          Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(settings.high, moreFuel_expr);
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuel, layer)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuelAssert, layerAssert)));
          defineFuel = true;
        }
      }
      return defineFuel;
    }

    internal static AssumeCmd optimizeExpr(bool minimize, Expression expr, IToken tok, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsIntegerType || expr.Type.IsRealType);
      Contract.Requires(tok != null && etran != null);

      var assumeCmd = new AssumeCmd(tok, Expr.True);
      assumeCmd.Attributes = new QKeyValue(expr.tok, (minimize ? "minimize" : "maximize"), new List<object> { etran.TrExpr(expr) }, null);
      return assumeCmd;
    }

    private void AddFunctionOverrideEnsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap,
      List<Bpl.Variable> implInParams,
      Bpl.Variable/*?*/ resultVariable) {
      Contract.Requires(f.Formals.Count <= implInParams.Count);

      //generating class post-conditions
      foreach (var en in f.Ens) {
        builder.Add(TrAssumeCmdWithDependencies(etran, f.tok, en.E, "overridden function ensures clause"));
      }

      //generating assume C.F(ins) == out, if a result variable was given
      if (resultVariable != null) {
        var funcIdC = new FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        var argsC = new List<Bpl.Expr>();

        // add type arguments
        argsC.AddRange(GetTypeArguments(f, null).ConvertAll(TypeToTy));

        // add fuel arguments
        if (f.IsFuelAware()) {
          argsC.Add(etran.layerInterCluster.GetFunctionFuel(f));
        }

        if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
          argsC.Add(GetRevealConstant(f));
        }

        // add heap arguments
        if (f is TwoStateFunction) {
          argsC.Add(etran.Old.HeapExpr);
        }
        if (f.ReadsHeap) {
          argsC.Add(etran.HeapExpr);
        }

        argsC.AddRange(implInParams.Select(var => new Bpl.IdentifierExpr(f.tok, var)));

        var funcExpC = new Bpl.NAryExpr(f.tok, funcIdC, argsC);
        var resultVar = new Bpl.IdentifierExpr(resultVariable.tok, resultVariable);
        builder.Add(TrAssumeCmd(f.tok, Bpl.Expr.Eq(funcExpC, resultVar)));
      }

      //generating trait post-conditions with class variables
      FunctionCallSubstituter sub = null;
      foreach (var en in f.OverriddenFunction.Ens) {
        sub ??= new FunctionCallSubstituter(substMap, typeMap, (TraitDecl)f.OverriddenFunction.EnclosingClass, (ClassLikeDecl)f.EnclosingClass);
        foreach (var s in TrSplitExpr(sub.Substitute(en.E), etran, false, out _).Where(s => s.IsChecked)) {
          builder.Add(Assert(f.tok, s.E, new PODesc.FunctionContractOverride(true)));
        }
      }
    }

    /// <summary>
    /// Return type arguments for function "f", where any type parameters are in terms of
    /// the context of "overridingFunction ?? f".
    ///
    /// In more symbols, suppose "f" is declared as follows:
    ///     class/trait Tr[A,B] {
    ///       function f[C,D](...): ...
    ///     }
    /// When "overridingFunction" is null, return:
    ///     [A, B, C, D]
    /// When "overridingFunction" is non-null and stands for:
    ///     class/trait Cl[G] extends Tr[X(G),Y(G)] {
    ///       function f[R,S](...): ...
    ///     }
    /// return:
    ///     [X(G), Y(G), R, S]
    ///
    /// See also GetTypeArgumentSubstitutionMap.
    /// </summary>
    private static List<Type> GetTypeArguments(Function f, Function/*?*/ overridingFunction) {
      Contract.Requires(f != null);
      Contract.Requires(overridingFunction == null || overridingFunction.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(overridingFunction == null || f.TypeArgs.Count == overridingFunction.TypeArgs.Count);

      List<Type> tyargs;
      if (overridingFunction == null) {
        tyargs = f.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.tok, tp));
      } else {
        var cl = (TopLevelDeclWithMembers)overridingFunction.EnclosingClass;
        var typeMap = cl.ParentFormalTypeParametersToActuals;
        tyargs = f.EnclosingClass.TypeArgs.ConvertAll(tp => typeMap[tp]);
      }
      tyargs.AddRange((overridingFunction ?? f).TypeArgs.ConvertAll(tp => new UserDefinedType(tp.tok, tp)));
      return tyargs;
    }

    private void AddFunctionOverrideSubsetChk(Function func, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap) {
      //getting framePrime
      List<FrameExpression> traitFrameExps = new List<FrameExpression>();
      FunctionCallSubstituter sub = null;
      foreach (var e in func.OverriddenFunction.Reads.Expressions) {
        sub ??= new FunctionCallSubstituter(substMap, typeMap, (TraitDecl)func.OverriddenFunction.EnclosingClass, (ClassLikeDecl)func.EnclosingClass);
        var newE = sub.Substitute(e.E);
        FrameExpression fe = new FrameExpression(e.tok, newE, e.FieldName);
        traitFrameExps.Add(fe);
      }

      QKeyValue kv = etran.TrAttributes(func.Attributes, null);

      IToken tok = func.tok;
      // Declare a local variable $_ReadsFrame: <alpha>[ref, Field alpha]bool
      Bpl.IdentifierExpr traitFrame = etran.ReadsFrame(func.OverriddenFunction.tok);  // this is a throw-away expression, used only to extract the type and name of the $_ReadsFrame variable
      traitFrame.Name = func.EnclosingClass.Name + "_" + traitFrame.Name;
      Contract.Assert(traitFrame.Type != null);  // follows from the postcondition of ReadsFrame
      Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, null ?? traitFrame.Name, traitFrame.Type));
      localVariables.Add(frame);
      // $_ReadsFrame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
      Bpl.Expr consequent = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null,
                                           Bpl.Expr.Imp(ante, consequent));

      //to initialize $_ReadsFrame variable to Frame'
      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));

      // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> $_ReadsFrame[o,f]);
      Bpl.Expr oInCallee = InRWClause(tok, o, f, func.Reads.Expressions, etran, null, null);
      Bpl.Expr consequent2 = InRWClause(tok, o, f, traitFrameExps, etran, null, null);
      Bpl.Expr q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
                                      Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), consequent2));
      builder.Add(Assert(tok, q, new PODesc.TraitFrame(func.WhatKind, false), kv));
    }

    private void AddFunctionOverrideReqsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Dictionary<IVariable, Expression> substMap,
      Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(f != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating trait pre-conditions with class variables
      FunctionCallSubstituter sub = null;
      foreach (var req in f.OverriddenFunction.Req) {
        sub ??= new FunctionCallSubstituter(substMap, typeMap, (TraitDecl)f.OverriddenFunction.EnclosingClass, (ClassLikeDecl)f.EnclosingClass);
        builder.Add(TrAssumeCmdWithDependencies(etran, f.tok, sub.Substitute(req.E), "overridden function requires clause"));
      }
      //generating class pre-conditions
      foreach (var s in f.Req.SelectMany(req => TrSplitExpr(req.E, etran, false, out _).Where(s => s.IsChecked))) {
        builder.Add(Assert(f.tok, s.E, new PODesc.FunctionContractOverride(false)));
      }
    }

    private void HavocMethodFrameLocations(Method m, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables) {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null && m.EnclosingClass is ClassLikeDecl);

      // play havoc with the heap according to the modifies clause
      builder.Add(new Bpl.HavocCmd(m.tok, new List<Bpl.IdentifierExpr> { etran.HeapCastToIdentifierExpr }));
      // assume the usual two-state boilerplate information
      foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, m.AllowsAllocation, etran.Old, etran, etran.Old)) {
        if (tri.IsFree) {
          builder.Add(TrAssumeCmd(m.tok, tri.Expr));
        }
      }
    }

    private void InsertChecksum(DatatypeDecl d, Bpl.Declaration decl) {
      Contract.Requires(VisibleInScope(d));
      byte[] data;
      using (var writer = new System.IO.StringWriter()) {
        var printer = new Printer(writer, options);
        printer.PrintDatatype(d, 0, null);
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Expression e, Bpl.Declaration decl) {
      byte[] data;
      using (var writer = new System.IO.StringWriter()) {
        var printer = new Printer(writer, options);
        printer.PrintExpression(e, false);
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Function f, Bpl.Declaration decl, bool specificationOnly = false) {
      Contract.Requires(f != null);
      Contract.Requires(decl != null);
      Contract.Requires(VisibleInScope(f));
      byte[] data;
      using (var writer = new System.IO.StringWriter()) {
        var printer = new Printer(writer, options);
        writer.Write(f.GetFunctionDeclarationKeywords(options));
        printer.PrintAttributes(f.Attributes);
        printer.PrintFormals(f.Formals, f);
        writer.Write(": ");
        printer.PrintType(f.ResultType);
        printer.PrintSpec("", f.Req, 0);
        printer.PrintFrameSpecLine("", f.Reads, 0);
        printer.PrintSpec("", f.Ens, 0);
        printer.PrintDecreasesSpec(f.Decreases, 0);
        writer.WriteLine();
        if (!specificationOnly && f.Body != null && RevealedInScope(f)) {
          printer.PrintExpression(f.Body, false);
        }
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(Bpl.Declaration decl, byte[] data) {
      Contract.Requires(decl != null);
      Contract.Requires(data != null);
      var md5 = System.Security.Cryptography.MD5.Create();
      var hashedData = md5.ComputeHash(data);
      var checksum = BitConverter.ToString(hashedData);

      decl.AddAttribute("checksum", checksum);

      InsertUniqueIdForImplementation(decl);
    }

    public void InsertUniqueIdForImplementation(Bpl.Declaration decl) {
      var impl = decl as Bpl.Implementation;
      var prefix = UniqueIdPrefix ?? (decl.tok.filename == null ? "" : System.Text.RegularExpressions.Regex.Replace(decl.tok.filename, @".v\d+.dfy", ".dfy"));
      if (impl != null && !string.IsNullOrEmpty(prefix)) {
        decl.AddAttribute("id", prefix + ":" + impl.Name + ":0");
      }
    }

    void GenerateImplPrelude(Method m, bool wellformednessProc, List<Variable> inParams, List<Variable> outParams,
                             BoogieStmtListBuilder builder, List<Variable> localVariables, ExpressionTranslator etran) {
      Contract.Requires(m != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);

      if (m is TwoStateLemma) {
        // $Heap := current$Heap;
        var heap = ExpressionTranslator.HeapIdentifierExpr(predef, m.tok);
        builder.Add(Bpl.Cmd.SimpleAssign(m.tok, heap, new Bpl.IdentifierExpr(m.tok, "current$Heap", predef.HeapType)));
      }

      // set up the information used to verify the method's reads and modifies clauses
      if (etran.readsFrame != null) {
        DefineFrame(m.tok, etran.ReadsFrame(m.tok), m.Reads.Expressions, builder, localVariables, null);
      }
      DefineFrame(m.tok, etran.ModifiesFrame(m.tok), m.Mod.Expressions, builder, localVariables, null);
      if (wellformednessProc) {
        builder.AddCaptureState(m.tok, false, "initial state");
      } else {
        Contract.Assert(m.Body != null);  // follows from precondition and the if guard
        // use the position immediately after the open-curly-brace of the body
        builder.AddCaptureState(m.Body.Tok, true, "initial state");
      }
    }

    void DefineFrame(IToken/*!*/ tok, Boogie.IdentifierExpr frameIdentifier, List<FrameExpression/*!*/>/*!*/ frameClause,
      BoogieStmtListBuilder/*!*/ builder, List<Variable>/*!*/ localVariables, string name, ExpressionTranslator/*?*/ etran = null) {
      Contract.Requires(tok != null);
      Contract.Requires(frameIdentifier != null);
      Contract.Requires(frameIdentifier.Type != null);
      Contract.Requires(cce.NonNullElements(frameClause));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(localVariables));
      Contract.Requires(predef != null);

      if (etran == null) {
        // This is the common case. It means that the frame will be defined in terms of the usual variable $Heap.
        // The one case where a frame is needed for a different heap is for lambda expressions, because they may
        // sit inside of an "old" expression.
        etran = new ExpressionTranslator(this, predef, tok);
      }
      // Declare a local variable $_Frame: <alpha>[ref, Field alpha]bool
      Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name ?? frameIdentifier.Name, frameIdentifier.Type));
      localVariables.Add(frame);
      // $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
      // $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: $o != null                    ==> ($o,$f) in Modifies/Reads-Clause);
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
      Bpl.Expr ante = Bpl.Expr.And(oNotNull, etran.IsAlloced(tok, o));
      Bpl.Expr consequent = InRWClause(tok, o, f, frameClause, etran, null, null);
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null,
                                           Bpl.Expr.Imp(ante, consequent));

      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));
    }

    void CheckFrameSubset(IToken tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable, Expression /*!*/> substMap,
                          ExpressionTranslator /*!*/ etran, Boogie.IdentifierExpr /*!*/ enclosingFrame,
                          BoogieStmtListBuilder /*!*/ builder,
                          PODesc.ProofObligationDescription desc,
                          Bpl.QKeyValue kv) {
      CheckFrameSubset(tok, calleeFrame, receiverReplacement, substMap, etran, enclosingFrame,
        (t, e, d, q) => builder.Add(Assert(t, e, d, q)), desc, kv);
    }

    void CheckFrameSubset(IToken tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/> substMap,
                          ExpressionTranslator/*!*/ etran, Boogie.IdentifierExpr /*!*/ enclosingFrame,
                          Action<IToken, Bpl.Expr, PODesc.ProofObligationDescription, Bpl.QKeyValue> MakeAssert,
                          PODesc.ProofObligationDescription desc,
                          Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(calleeFrame != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Requires(etran != null);
      Contract.Requires(MakeAssert != null);
      Contract.Requires(predef != null);

      // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> enclosingFrame[o,f]);
      Bpl.TypeVariable alpha = new Bpl.TypeVariable(tok, "alpha");
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
      Bpl.Expr oInCallee = InRWClause(tok, o, f, calleeFrame, etran, receiverReplacement, substMap);
      Bpl.Expr inEnclosingFrame = Bpl.Expr.Select(enclosingFrame, o, f);

      Bpl.Expr q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
                                      Bpl.Expr.Imp(Bpl.Expr.And(ante, oInCallee), inEnclosingFrame));
      if (IsExprAlways(q, true)) {
        return;
      }
      MakeAssert(tok, q, desc, kv);
    }

    void CheckFrameEmpty(IToken tok,
                         ExpressionTranslator/*!*/ etran, Boogie.IdentifierExpr /*!*/ frame,
                         BoogieStmtListBuilder/*!*/ builder, PODesc.ProofObligationDescription desc,
                         Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(frame != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      // emit: assert (forall<alpha> o: ref, f: Field alpha :: o != null && $Heap[o,alloc] ==> !frame[o,f]);
      var alpha = new Bpl.TypeVariable(tok, "alpha");
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);
      var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
      var f = new Bpl.IdentifierExpr(tok, fVar);
      var ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etran.IsAlloced(tok, o));
      var inFrame = Bpl.Expr.Select(frame, o, f);
      var notInFrame = Bpl.Expr.Not(inFrame);

      var q = new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar },
        Bpl.Expr.Imp(ante, notInFrame));
      if (IsExprAlways(q, true)) {
        return;
      }
      builder.Add(Assert(tok, q, desc, kv));
    }

    /// <summary>
    /// Returns true if it can statically determine that the expression q always evaluates to truth
    /// </summary>
    /// <param name="q">The expression</param>
    /// <param name="truth">The expected truth value that q might always have</param>
    /// <returns>True if q is always of the boolean value "truth"</returns>
    public static bool IsExprAlways(Bpl.Expr q, bool truth) {
      if (q is Bpl.ForallExpr forallExpr) {
        return truth && IsExprAlways(forallExpr.Body, true);
      }
      if (q is Bpl.ExistsExpr existsExpr) {
        return !truth && IsExprAlways(existsExpr.Body, false);
      }
      if (q is Bpl.LiteralExpr { isBool: true } lit && lit.asBool == truth) {
        return true;
      }

      if (q is Bpl.NAryExpr n) {
        if (n.Fun is Bpl.BinaryOperator op && n.Args.Count == 2) {
          switch (op.Op) {
            case BinaryOperator.Opcode.And:
              return truth
                ? IsExprAlways(n.Args[0], true) && IsExprAlways(n.Args[1], true)
                : IsExprAlways(n.Args[0], false) || IsExprAlways(n.Args[1], false);
            case BinaryOperator.Opcode.Or:
              return truth
                ? IsExprAlways(n.Args[0], true) || IsExprAlways(n.Args[1], true)
                : IsExprAlways(n.Args[0], false) && IsExprAlways(n.Args[1], false);
            case BinaryOperator.Opcode.Imp:
              return truth
                ? IsExprAlways(n.Args[0], false) || IsExprAlways(n.Args[1], true)
                : IsExprAlways(n.Args[0], true) && IsExprAlways(n.Args[1], false);
          }
        } else if (n.Fun is Bpl.UnaryOperator uop && n.Args.Count == 1) {
          switch (uop.Op) {
            case UnaryOperator.Opcode.Not:
              return IsExprAlways(n.Args[0], !truth);
          }
        }
      }

      return false;
    }

    /// <summary>
    /// Generates:
    ///   axiom (forall s, h0: HeapType, h1: HeapType, formals... ::
    ///        { IsHeapAnchor(h0), HeapSucc(h0,h1), F(s,h1,formals) }
    ///        heaps are well-formed and [formals are allocated AND]
    ///        IsHeapAnchor(h0) AND HeapSucc(h0,h1)
    ///        AND
    ///        (forall(alpha) o: ref, f: Field alpha ::
    ///            o != null [AND h0[o,alloc] AND]  // note that HeapSucc(h0,h1) && h0[o,alloc] ==> h1[o,alloc]
    ///            o in reads clause of formals in h0
    ///            IMPLIES h0[o,f] == h1[o,f])
    ///        IMPLIES
    ///        F(s,h0,formals) == F(s,h1,formals)
    ///      );
    /// Expressions in [...] are omitted if
    ///   - /allocated:0, or
    ///   - /allocated:1, or
    ///   - /allocated:3, except if "reads" clause is "*" of if the function is a two-state function;
    /// see comments in AddArrowTypeAxioms
    /// Also, with /allocated:3, the frame axiom is omitted altogether if the (one-state) function has an
    /// empty "reads" clause (because then the function doesn't take a heap argument at all).
    /// </summary>
    void AddFrameAxiom(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);

      var comment = "frame axiom for " + f.FullSanitizedName;
      // This is the general case
      Bpl.Expr prevH = null;
      Bpl.BoundVariable prevHVar = null;
      Bpl.Expr reveal = null;
      Bpl.BoundVariable revealVar = null;
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        revealVar = BplBoundVar("$reveal", Bpl.Type.Bool, out reveal);
      }
      if (f is TwoStateFunction) {
        // The previous-heap argument is the same for both function arguments.  That is,
        // the frame axiom says nothing about functions invoked with different previous heaps.
        prevHVar = BplBoundVar("$prevHeap", predef.HeapType, out prevH);
      }
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
      Bpl.Expr oNotNullAlloced = oNotNull;
      Bpl.Expr unchanged = Bpl.Expr.Eq(ReadHeap(f.tok, h0, o, field, alpha), ReadHeap(f.tok, h1, o, field, alpha));

      Bpl.Expr h0IsHeapAnchor = FunctionCall(h0.tok, BuiltinFunction.IsHeapAnchor, null, h0);
      Bpl.Expr heapSucc = HeapSucc(h0, h1);
      Bpl.Expr r0 = InRWClause(f.tok, o, field, f.Reads.Expressions, etran0, null, null);
      Bpl.Expr q0 = new Bpl.ForallExpr(f.tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fieldVar },
        Bpl.Expr.Imp(Bpl.Expr.And(oNotNullAlloced, r0), unchanged));

      List<Bpl.Expr> tyexprs;
      var bvars = MkTyParamBinders(GetTypeParams(f), out tyexprs);
      var f0args = new List<Bpl.Expr>(tyexprs);
      var f1args = new List<Bpl.Expr>(tyexprs);
      var f0argsCanCall = new List<Bpl.Expr>(tyexprs);
      var f1argsCanCall = new List<Bpl.Expr>(tyexprs);
      if (f.IsFuelAware()) {
        Bpl.Expr s; var sV = BplBoundVar("$ly", predef.LayerType, out s);
        bvars.Add(sV);
        f0args.Add(s); f1args.Add(s);  // but don't add to f0argsCanCall or f1argsCanCall
      }

      if (reveal != null) {
        bvars.Add(revealVar);
        f0args.Add(reveal); f1args.Add(reveal);
      }

      if (prevH != null) {
        bvars.Add(prevHVar);
        f0args.Add(prevH); f1args.Add(prevH); f0argsCanCall.Add(prevH); f1argsCanCall.Add(prevH);
      }
      bvars.Add(h0Var); bvars.Add(h1Var);
      f0args.Add(h0); f1args.Add(h1); f0argsCanCall.Add(h0); f1argsCanCall.Add(h1);

      var useAlloc = f.Reads.Expressions.Exists(fe => fe.E is WildcardExpr) ? ISALLOC : NOALLOC;
      if (!f.IsStatic) {
        Bpl.Expr th; var thVar = BplBoundVar("this", TrReceiverType(f), out th);
        bvars.Add(thVar);
        f0args.Add(th); f1args.Add(th); f0argsCanCall.Add(th); f1argsCanCall.Add(th);

        Type thisType = ModuleResolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(ReceiverNotNull(th), GetWhereClause(f.tok, th, thisType, etran0, useAlloc));
        wellFormed = Bpl.Expr.And(wellFormed, wh);
      }

      // (formalsAreWellFormed[h0] || canCallF(h0,...)) && (formalsAreWellFormed[h1] || canCallF(h1,...))
      Bpl.Expr fwf0 = Bpl.Expr.True;
      Bpl.Expr fwf1 = Bpl.Expr.True;
      foreach (Formal p in f.Formals) {
        Bpl.BoundVariable bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
        bvars.Add(bv);
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        f0args.Add(formal); f1args.Add(formal); f0argsCanCall.Add(formal); f1argsCanCall.Add(formal);
        Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, etran0, useAlloc);
        if (wh != null) { fwf0 = Bpl.Expr.And(fwf0, wh); }
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
      var tr = new Bpl.Trigger(f.tok, true, new List<Bpl.Expr> { h0IsHeapAnchor, heapSucc, F1 });

      var ax = new Bpl.ForallExpr(f.tok, new List<Bpl.TypeVariable>(), bvars, null, tr,
        Bpl.Expr.Imp(Bpl.Expr.And(wellFormed, Bpl.Expr.And(h0IsHeapAnchor, heapSucc)),
        Bpl.Expr.Imp(q0, eq)));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, ax, comment));
    }

    Bpl.Expr InRWClause(IToken tok, Bpl.Expr o, Bpl.Expr f, List<FrameExpression> rw, ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(cce.NonNullElements(rw));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(predef != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      return InRWClause(tok, o, f, rw, false, etran, receiverReplacement, substMap);
    }
    Bpl.Expr InRWClause(IToken tok, Bpl.Expr o, Bpl.Expr f, List<FrameExpression> rw, bool useInUnchanged,
                        ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(cce.NonNullElements(rw));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(predef != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      var boxO = FunctionCall(tok, BuiltinFunction.Box, null, o);
      return InRWClause_Aux(tok, o, boxO, f, rw, useInUnchanged, etran, receiverReplacement, substMap);
    }

    /// <summary>
    /// By taking both an "o" and a "boxO" parameter, the caller has a choice of passing in either
    /// "o, Box(o)" for some "o" or "Unbox(bx), bx" for some "bx".
    /// </summary>
    Bpl.Expr InRWClause_Aux(IToken tok, Bpl.Expr o, Bpl.Expr boxO, Bpl.Expr f, List<FrameExpression> rw, bool usedInUnchanged,
                        ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      Contract.Requires(boxO != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(cce.NonNullElements(rw));
      Contract.Requires(substMap == null || cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(predef != null);
      Contract.Requires((substMap == null && receiverReplacement == null) || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // requires o to denote an expression of type RefType
      // "rw" is allowed to contain a WildcardExpr

      Bpl.Expr disjunction = Bpl.Expr.False;
      foreach (FrameExpression rwComponent in rw) {
        Expression e = rwComponent.E;
        if (substMap != null) {
          e = Substitute(e, receiverReplacement, substMap);
        }

        Bpl.Expr disjunct;
        var eType = e.Type.NormalizeExpand();
        if (e is WildcardExpr) {
          // For /allocated:{0,1,3}, "function f(...)... reads *"
          // is more useful if "reads *" excludes unallocated references,
          // because otherwise, "reads *" lets f depend on unallocated state,
          // which means that f may change whenever any new allocation occurs,
          // which is generally undesirable.  Also, Dafny doesn't let you
          // say "reads set o :: allocated(o)", so it's hard to work around
          // this issue.
          disjunct = etran.IsAlloced(tok, o);
        } else if (eType is SetType) {
          // e[Box(o)]
          bool pr;
          disjunct = etran.TrInSet_Aux(tok, o, boxO, e, true, out pr);
        } else if (eType is MultiSetType) {
          // e[Box(o)] > 0
          disjunct = etran.TrInMultiSet_Aux(tok, o, boxO, e, true);
        } else if (eType is SeqType) {
          // (exists i: int :: 0 <= i && i < Seq#Length(e) && Seq#Index(e,i) == Box(o))
          Bpl.Variable iVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$i", Bpl.Type.Int));
          Bpl.Expr i = new Bpl.IdentifierExpr(tok, iVar);
          Bpl.Expr iBounds = InSeqRange(tok, i, Type.Int, etran.TrExpr(e), true, null, false);
          Bpl.Expr XsubI = FunctionCall(tok, BuiltinFunction.SeqIndex, predef.BoxType, etran.TrExpr(e), i);
          // TODO: the equality in the next line should be changed to one that understands extensionality
          //TRIG (exists $i: int :: 0 <= $i && $i < Seq#Length(read($h0, this, _module.DoublyLinkedList.Nodes)) && Seq#Index(read($h0, this, _module.DoublyLinkedList.Nodes), $i) == $Box($o))
          disjunct = new Bpl.ExistsExpr(tok, new List<Variable> { iVar }, Bpl.Expr.And(iBounds, Bpl.Expr.Eq(XsubI, boxO)));  // LL_TRIGGER
        } else {
          // o == e
          disjunct = Bpl.Expr.Eq(o, etran.TrExpr(e));
        }
        if (rwComponent.Field != null && f != null) {
          Bpl.Expr q = Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.tok, GetField(rwComponent.Field)));
          if (usedInUnchanged) {
            q = Bpl.Expr.Or(q,
              Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.tok, predef.AllocField)));
          }
          disjunct = Bpl.Expr.And(disjunct, q);
        }
        disjunction = BplOr(disjunction, disjunct);
      }
      return disjunction;
    }

    void AddWellformednessCheck(RedirectingTypeDecl decl) {
      Contract.Requires(decl != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(decl.Name, MethodTranslationKind.SpecWellformedness));

      if (!InVerificationScope(decl)) {
        // Checked in other file
        return;
      }

      // If there's no constraint, there's nothing to do
      if (decl.Var == null) {
        Contract.Assert(decl.Constraint == null);  // there's a constraint only if there's a variable to be constrained
        Contract.Assert(decl.WitnessKind == SubsetTypeDecl.WKind.CompiledZero);  // a witness makes sense only if there is a constraint
        Contract.Assert(decl.Witness == null);  // a witness makes sense only if there is a constraint
        return;
      }
      Contract.Assert(decl.Constraint != null);  // follows from the test above and the RedirectingTypeDecl class invariant

      currentModule = decl.Module;
      codeContext = new CallableWrapper(decl, true);
      var etran = new ExpressionTranslator(this, predef, decl.tok);

      // parameters of the procedure
      var inParams = MkTyParamFormals(decl.TypeArgs, true);
      Bpl.Type varType = TrType(decl.Var.Type);
      Bpl.Expr wh = GetWhereClause(decl.Var.tok, new Bpl.IdentifierExpr(decl.Var.tok, decl.Var.AssignUniqueName(decl.IdGenerator), varType), decl.Var.Type, etran, NOALLOC);
      inParams.Add(new Bpl.Formal(decl.Var.tok, new Bpl.TypedIdent(decl.Var.tok, decl.Var.AssignUniqueName(decl.IdGenerator), varType, wh), true));

      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == TypeContextHeight;
      req.Add(Requires(decl.tok, true, etran.HeightContext(decl), null, null, null));
      // modifies $Heap
      var mod = new List<Bpl.IdentifierExpr> {
        etran.HeapCastToIdentifierExpr,
      };
      var name = MethodName(decl, MethodTranslationKind.SpecWellformedness);
      var proc = new Bpl.Procedure(decl.tok, name, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        false, req, mod, new List<Bpl.Ensures>(), etran.TrAttributes(decl.Attributes, null));
      AddVerboseName(proc, decl.Name, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);

      // TODO: Can a checksum be inserted here?

      Contract.Assert(proc.InParams.Count == inParams.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this, options);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for {0} {1}", decl.WhatKind, decl)));
      builder.AddCaptureState(decl.tok, false, "initial state");
      isAllocContext = new IsAllocContext(options, true);

      DefineFrame(decl.tok, etran.ReadsFrame(decl.tok), new List<FrameExpression>(), builder, locals, null);

      // some initialization stuff;  // This is collected in builderInitializationArea
      // define frame;
      // if (*) {
      //   // The following is collected in constraintCheckBuilder:
      //   check constraint is well-formed;
      //   assume constraint;
      //   do reads checks;
      // } else {
      //   // The following is collected in witnessCheckBuilder:
      //   check witness;
      // }

      // check well-formedness of the constraint (including termination, and delayed reads checks)
      var constraintCheckBuilder = new BoogieStmtListBuilder(this, options);
      var builderInitializationArea = new BoogieStmtListBuilder(this, options);
      var delayer = new ReadsCheckDelayer(etran, null, locals, builderInitializationArea, constraintCheckBuilder);
      delayer.DoWithDelayedReadsChecks(false, wfo => {
        CheckWellformedAndAssume(decl.Constraint, wfo, locals, constraintCheckBuilder, etran, "predicate subtype constraint");
      });

      // Check that the type is inhabited.
      // Note, the possible witness in this check should be coordinated with the compiler, so the compiler knows how to do the initialization
      Expression witnessExpr = null;
      var witnessCheckBuilder = new BoogieStmtListBuilder(this, options);
      string witnessString = null;
      if (decl.Witness != null) {
        // check well-formedness of the witness expression (including termination, and reads checks)
        var ghostCodeContext = codeContext;
        codeContext = decl.WitnessKind == SubsetTypeDecl.WKind.Compiled ? new CallableWrapper(decl, false) : ghostCodeContext;
        CheckWellformed(decl.Witness, new WFOptions(null, true), locals, witnessCheckBuilder, etran);
        codeContext = ghostCodeContext;
        // check that the witness is assignable to the type of the given bound variable
        if (decl is SubsetTypeDecl) {
          // Note, for new-types, this has already been checked by CheckWellformed.
          CheckResultToBeInType(decl.Witness.tok, decl.Witness, decl.Var.Type, locals, witnessCheckBuilder, etran);
        }
        // check that the witness expression checks out
        witnessExpr = Substitute(decl.Constraint, decl.Var, decl.Witness);
      } else if (decl.WitnessKind == SubsetTypeDecl.WKind.CompiledZero) {
        var witness = Zero(decl.tok, decl.Var.Type);
        if (witness == null) {
          witnessString = "";
          witnessCheckBuilder.Add(Assert(decl.tok, Bpl.Expr.False, new PODesc.WitnessCheck(witnessString)));
        } else {
          // before trying 0 as a witness, check that 0 can be assigned to decl.Var
          witnessString = Printer.ExprToString(options, witness);
          CheckResultToBeInType(decl.tok, witness, decl.Var.Type, locals, witnessCheckBuilder, etran, $"trying witness {witnessString}: ");
          witnessExpr = Substitute(decl.Constraint, decl.Var, witness);
        }
      }
      if (witnessExpr != null) {
        var witnessCheckTok = decl.Witness != null ? GetToken(decl.Witness) : decl.tok;
        witnessCheckBuilder.Add(new Bpl.AssumeCmd(witnessCheckTok, CanCallAssumption(witnessExpr, etran)));
        var witnessCheck = etran.TrExpr(witnessExpr);

        bool splitHappened;
        var ss = TrSplitExpr(witnessExpr, etran, true, out splitHappened);
        var desc = new PODesc.WitnessCheck(witnessString);
        if (!splitHappened) {
          witnessCheckBuilder.Add(Assert(witnessCheckTok, etran.TrExpr(witnessExpr), desc));
        } else {
          foreach (var split in ss) {
            if (split.IsChecked) {
              var tok = witnessCheckTok is IToken t ? new NestedToken(t, split.Tok) : witnessCheckTok;
              witnessCheckBuilder.Add(AssertNS(tok, split.E, desc));
            }
          }
        }
      }

      builder.Add(new Bpl.IfCmd(decl.tok, null, constraintCheckBuilder.Collect(decl.tok), null, witnessCheckBuilder.Collect(decl.tok)));

      var s0 = builderInitializationArea.Collect(decl.tok);
      var s1 = builder.Collect(decl.tok);
      var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), decl.tok);

      if (EmitImplementation(decl.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(decl.Attributes, null);

        AddImplementationWithVerboseName(GetToken(decl), proc, implInParams, new List<Variable>(), locals, implBody, kv);
      }

      // TODO: Should a checksum be inserted here?

      Contract.Assert(currentModule == decl.Module);
      Contract.Assert(CodeContextWrapper.Unwrap(codeContext) == decl);
      isAllocContext = null;
      Reset();
    }

    void AddWellformednessCheck(ConstantField decl) {
      Contract.Requires(decl != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(decl.FullDafnyName, MethodTranslationKind.SpecWellformedness));
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
      var etran = new ExpressionTranslator(this, predef, decl.tok);

      // parameters of the procedure
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(decl.EnclosingClass), true);
      if (!decl.IsStatic) {
        var receiverType = ModuleResolver.GetThisType(decl.tok, (TopLevelDeclWithMembers)decl.EnclosingClass);
        Contract.Assert(VisibleInScope(receiverType));

        var th = new Bpl.IdentifierExpr(decl.tok, "this", TrReceiverType(decl));
        var wh = Bpl.Expr.And(
          ReceiverNotNull(th),
          etran.GoodRef(decl.tok, th, receiverType));
        // for class constructors, the receiver is encoded as an output parameter
        var thVar = new Bpl.Formal(decl.tok, new Bpl.TypedIdent(decl.tok, "this", TrReceiverType(decl), wh), true);
        inParams.Add(thVar);
      }

      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == TypeContextHeight;
      req.Add(Requires(decl.tok, true, etran.HeightContext(decl), null, null, null));
      var heapVar = new Bpl.IdentifierExpr(decl.tok, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar };
      var name = MethodName(decl, MethodTranslationKind.SpecWellformedness);
      var proc = new Bpl.Procedure(decl.tok, name, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        false, req, varlist, new List<Bpl.Ensures>(), etran.TrAttributes(decl.Attributes, null));
      AddVerboseName(proc, decl.FullDafnyName, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this, options);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for {0} {1}", decl.WhatKind, decl)));
      builder.AddCaptureState(decl.tok, false, "initial state");
      isAllocContext = new IsAllocContext(options, true);

      DefineFrame(decl.tok, etran.ReadsFrame(decl.tok), new List<FrameExpression>(), builder, locals, null);

      // check well-formedness of the RHS expression
      CheckWellformed(decl.Rhs, new WFOptions(null, true), locals, builder, etran);
      builder.Add(new Bpl.AssumeCmd(decl.Rhs.tok, CanCallAssumption(decl.Rhs, etran)));
      CheckSubrange(decl.Rhs.tok, etran.TrExpr(decl.Rhs), decl.Rhs.Type, decl.Type, builder);

      if (EmitImplementation(decl.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(decl.Attributes, null);
        var implBody = builder.Collect(decl.tok);

        AddImplementationWithVerboseName(GetToken(decl), proc, implInParams,
          new List<Variable>(), locals, implBody, kv);
      }

      Contract.Assert(currentModule == decl.EnclosingModule);
      Contract.Assert(codeContext == decl);
      isAllocContext = null;
      fuelContext = null;
      Reset();
    }

    void AddWellformednessCheck(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(ctor.FullName, MethodTranslationKind.SpecWellformedness));

      if (!InVerificationScope(ctor)) {
        // Checked in other file
        return;
      }

      // If there are no parameters with default values, there's nothing to do
      if (ctor.Formals.TrueForAll(f => f.DefaultValue == null)) {
        return;
      }

      currentModule = ctor.EnclosingDatatype.EnclosingModuleDefinition;
      codeContext = ctor.EnclosingDatatype;
      fuelContext = FuelSetting.NewFuelContext(ctor.EnclosingDatatype);
      var etran = new ExpressionTranslator(this, predef, ctor.tok);

      // parameters of the procedure
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(ctor.EnclosingDatatype), true);
      foreach (var p in ctor.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(ctor.IdGenerator), varType), p.Type, etran, NOALLOC);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(ctor.IdGenerator), varType, wh), true));
      }

      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == TypeContextHeight;
      req.Add(Requires(ctor.tok, true, etran.HeightContext(ctor.EnclosingDatatype), null, null, null));
      var heapVar = new Bpl.IdentifierExpr(ctor.tok, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar };
      var proc = new Bpl.Procedure(ctor.tok, "CheckWellformed" + NameSeparator + ctor.FullName, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        false, req, varlist, new List<Bpl.Ensures>(), etran.TrAttributes(ctor.Attributes, null));
      AddVerboseName(proc, ctor.FullName, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this, options);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for datatype constructor {0}", ctor)));
      builder.AddCaptureState(ctor.tok, false, "initial state");
      isAllocContext = new IsAllocContext(options, true);

      DefineFrame(ctor.tok, etran.ReadsFrame(ctor.tok), new List<FrameExpression>(), builder, locals, null);

      // check well-formedness of each default-value expression
      foreach (var formal in ctor.Formals.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformed(e, new WFOptions(null, true, false, true), locals, builder, etran);
        builder.Add(new Bpl.AssumeCmd(e.tok, CanCallAssumption(e, etran)));
        CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, builder);
      }

      if (EmitImplementation(ctor.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(ctor.Attributes, null);
        var implBody = builder.Collect(ctor.tok);
        AddImplementationWithVerboseName(GetToken(ctor), proc, implInParams,
          new List<Variable>(), locals, implBody, kv);
      }

      Contract.Assert(currentModule == ctor.EnclosingDatatype.EnclosingModuleDefinition);
      Contract.Assert(codeContext == ctor.EnclosingDatatype);
      isAllocContext = null;
      fuelContext = null;
      Reset();
    }

    /// <summary>
    /// If "declareLocals" is "false", then the locals are added only if they are new, that is, if
    /// they don't already exist in "locals".
    /// </summary>
    Bpl.Expr CtorInvocation(MatchCase mc, Type sourceType, ExpressionTranslator etran, List<Variable> locals, BoogieStmtListBuilder localTypeAssumptions, IsAllocType isAlloc, bool declareLocals = true) {
      Contract.Requires(mc != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      sourceType = sourceType.NormalizeExpand();
      Contract.Assert(sourceType.TypeArgs.Count == mc.Ctor.EnclosingDatatype.TypeArgs.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (var i = 0; i < mc.Ctor.EnclosingDatatype.TypeArgs.Count; i++) {
        subst.Add(mc.Ctor.EnclosingDatatype.TypeArgs[i], sourceType.TypeArgs[i]);
      }

      List<Bpl.Expr> args = new List<Bpl.Expr>();
      for (int i = 0; i < mc.Arguments.Count; i++) {
        BoundVar p = mc.Arguments[i];
        var nm = p.AssignUniqueName(currentDeclaration.IdGenerator);
        Bpl.Variable local = declareLocals ? null : locals.FirstOrDefault(v => v.Name == nm);  // find previous local
        if (local == null) {
          local = new Bpl.LocalVariable(p.tok, new Bpl.TypedIdent(p.tok, nm, TrType(p.Type)));
          locals.Add(local);
        } else {
          Contract.Assert(Bpl.Type.Equals(local.TypedIdent.Type, TrType(p.Type)));
        }
        var pFormalType = mc.Ctor.Formals[i].Type.Subst(subst);
        var pIsAlloc = (isAlloc == ISALLOC) ? isAllocContext.Var(p) : NOALLOC;
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, local), pFormalType, etran, pIsAlloc);
        if (wh != null) {
          localTypeAssumptions.Add(TrAssumeCmd(p.tok, wh));
        }
        CheckSubrange(p.tok, new Bpl.IdentifierExpr(p.tok, local), pFormalType, p.Type, localTypeAssumptions);
        args.Add(CondApplyBox(mc.tok, new Bpl.IdentifierExpr(p.tok, local), cce.NonNull(p.Type), mc.Ctor.Formals[i].Type));
      }
      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(mc.tok, mc.Ctor.FullName, predef.DatatypeType);
      return new Bpl.NAryExpr(mc.tok, new Bpl.FunctionCall(id), args);
    }

    Bpl.Expr CtorInvocation(IToken tok, DatatypeCtor ctor, ExpressionTranslator etran, List<Variable> locals, BoogieStmtListBuilder localTypeAssumptions) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // create local variables for the formals
      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("a#");
      var args = new List<Bpl.Expr>();
      foreach (Formal arg in ctor.Formals) {
        Contract.Assert(arg != null);
        var nm = varNameGen.FreshId(string.Format("#{0}#", args.Count));
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
        var r = CanCallAssumption(e.Obj, etran);
        if (e.Member is DatatypeDestructor) {
          var dtor = (DatatypeDestructor)e.Member;
          if (dtor.EnclosingCtors.Count == dtor.EnclosingCtors[0].EnclosingDatatype.Ctors.Count) {
            // Every constructor has this destructor; might as well assume that here.
            var correctConstructor = BplOr(dtor.EnclosingCtors.ConvertAll(
              ctor => FunctionCall(e.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Obj))));
            r = BplAnd(r, correctConstructor);
          }
        }
        return r;
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        Bpl.Expr total = CanCallAssumption(e.Seq, etran);
        if (e.E0 != null) {
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
        Bpl.Expr r = CanCallAssumption(e.Receiver, etran);
        r = BplAnd(r, CanCallAssumption(e.Args, etran));
        if (!(e.Function is SpecialFunction)) {
          // get to assume canCall
          Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null, null);
          Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(GetToken(expr), new Bpl.FunctionCall(canCallFuncID), args);
          r = BplAnd(r, canCallFuncAppl);
        }
        return r;
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        return CanCallAssumption(dtv.Arguments, etran);
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        return BplAnd(CanCallAssumption(e.N, etran), CanCallAssumption(e.Initializer, etran));
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return CanCallAssumption(e.E, etran.OldAt(e.AtLabel));
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        Bpl.Expr be = Bpl.Expr.True;
        foreach (var fe in e.Frame) {
          be = BplAnd(be, CanCallAssumption(fe.E, etran));
        }
        return be;
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is BinaryExpr) {
        // The short-circuiting boolean operators &&, ||, and ==> end up duplicating their
        // left argument. Therefore, we first try to re-associate the expression to make
        // left arguments smaller.
        if (ReAssociateToTheRight(ref expr)) {
          return CanCallAssumption(expr, etran);
        }
        var e = (BinaryExpr)expr;

        Bpl.Expr t0 = CanCallAssumption(e.E0, etran);
        Bpl.Expr t1 = CanCallAssumption(e.E1, etran);
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp:
            t1 = BplImp(etran.TrExpr(e.E0), t1);
            break;
          case BinaryExpr.ResolvedOpcode.Or:
            t1 = BplImp(Bpl.Expr.Not(etran.TrExpr(e.E0)), t1);
            break;
          case BinaryExpr.ResolvedOpcode.EqCommon:
          case BinaryExpr.ResolvedOpcode.NeqCommon: {
              Bpl.Expr r = Bpl.Expr.True;
              var dt = e.E0.Type.AsDatatype;
              if (dt != null) {
                var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(expr.tok, "$IsA#" + dt.FullSanitizedName, Bpl.Type.Bool));
                if (!(e.E0.Resolved is DatatypeValue)) {
                  r = BplAnd(r, new Bpl.NAryExpr(expr.tok, funcID, new List<Bpl.Expr> { etran.TrExpr(e.E0) }));
                }
                if (!(e.E1.Resolved is DatatypeValue)) {
                  r = BplAnd(r, new Bpl.NAryExpr(expr.tok, funcID, new List<Bpl.Expr> { etran.TrExpr(e.E1) }));
                }
              }
              return BplAnd(r, BplAnd(t0, t1));
            }
          case BinaryExpr.ResolvedOpcode.Mul:
            if (7 <= options.ArithMode) {
              if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int) && !options.DisableNLarith) {
                // Produce a useful fact about the associativity of multiplication. It is a bit dicey to do as an axiom.
                // Change (k*A)*B or (A*k)*B into (A*B)*k, where k is a numeric literal
                var left = e.E0.Resolved as BinaryExpr;
                if (left != null && left.ResolvedOp == BinaryExpr.ResolvedOpcode.Mul) {
                  Bpl.Expr r = Bpl.Expr.True;
                  if (left.E0.Resolved is LiteralExpr) {
                    // (K*A)*B == (A*B)*k
                    var y = Expression.CreateMul(Expression.CreateMul(left.E1, e.E1), left.E0);
                    var eq = Expression.CreateEq(e, y, e.E0.Type);
                    r = BplAnd(r, etran.TrExpr(eq));
                  }
                  if (left.E1.Resolved is LiteralExpr) {
                    // (A*k)*B == (A*B)*k
                    var y = Expression.CreateMul(Expression.CreateMul(left.E0, e.E1), left.E1);
                    var eq = Expression.CreateEq(e, y, e.E0.Type);
                    r = BplAnd(r, etran.TrExpr(eq));
                  }
                  if (r != Bpl.Expr.True) {
                    return BplAnd(BplAnd(t0, t1), r);
                  }
                }
              }
            }
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
        if (!e.Exact) {
          // CanCall[[ var b0,b1 :| RHS(b0,b1,g); Body(b0,b1,g,h) ]] =
          //   $let$canCall(g) &&
          //   CanCall[[ Body($let$b0(g), $let$b1(g), h) ]]
          LetDesugaring(e);  // call LetDesugaring to prepare the desugaring and populate letSuchThatExprInfo with something for e
          var info = letSuchThatExprInfo[e];
          // $let$canCall(g)
          var canCall = info.CanCallFunctionCall(this, etran);
          Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
          foreach (var bv in e.BoundVars) {
            // create a call to $let$x(g)
            var args = info.SkolemFunctionArgs(bv, this, etran);
            var call = new BoogieFunctionCall(bv.tok, info.SkolemFunctionName(bv), info.UsesHeap, info.UsesOldHeap, info.UsesHeapAt, args.Item1, args.Item2);
            call.Type = bv.Type;
            substMap.Add(bv, call);
          }
          var p = Substitute(e.Body, null, substMap);
          var cc = BplAnd(canCall, CanCallAssumption(p, etran));
          return cc;
        } else {
          // CanCall[[ var b := RHS(g); Body(b,g,h) ]] =
          //   CanCall[[ RHS(g) ]] &&
          //   (var lhs0,lhs1,... := rhs0,rhs1,...;  CanCall[[ Body ]])
          Bpl.Expr canCallRHS = Bpl.Expr.True;
          foreach (var rhs in e.RHSs) {
            canCallRHS = BplAnd(canCallRHS, CanCallAssumption(rhs, etran));
          }

          var bodyCanCall = CanCallAssumption(e.Body, etran);
          // We'd like to compute the free variables if "bodyCanCall". It would be nice to use the Boogie
          // routine Bpl.Expr.ComputeFreeVariables for this purpose. However, calling it requires the Boogie
          // expression to be resolved. Instead, we do the cheesy thing of computing the set of names of
          // free variables in "bodyCanCall".
          var vis = new VariableNameVisitor();
          vis.Visit(bodyCanCall);

          List<Bpl.Variable> lhssAll;
          List<Bpl.Expr> rhssAll;
          etran.TrLetExprPieces(e, out lhssAll, out rhssAll);
          Contract.Assert(lhssAll.Count == rhssAll.Count);

          // prune lhss,rhss to contain only those pairs where the LHS is used in the body
          var lhssPruned = new List<Bpl.Variable>();
          var rhssPruned = new List<Bpl.Expr>();
          for (var i = 0; i < lhssAll.Count; i++) {
            var bv = lhssAll[i];
            if (vis.Names.Contains(bv.Name)) {
              lhssPruned.Add(bv);
              rhssPruned.Add(rhssAll[i]);
            }
          }
          Bpl.Expr let = lhssPruned.Count == 0 ? bodyCanCall : new Bpl.LetExpr(e.tok, lhssPruned, rhssPruned, null, bodyCanCall);
          return BplAnd(canCallRHS, let);
        }

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;

        var bvarsAndAntecedents = new List<Tuple<Bpl.Variable, Bpl.Expr>>();
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("$l#");

        Bpl.Expr heap; var hVar = BplBoundVar(varNameGen.FreshId("#heap#"), predef.HeapType, out heap);
        var et = new ExpressionTranslator(etran, heap);

        Dictionary<IVariable, Expression> subst = new Dictionary<IVariable, Expression>();
        foreach (var bv in e.BoundVars) {
          Bpl.Expr ve; var yVar = BplBoundVar(varNameGen.FreshId(string.Format("#{0}#", bv.Name)), TrType(bv.Type), out ve);
          var wh = GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, yVar), bv.Type, et, NOALLOC);
          bvarsAndAntecedents.Add(Tuple.Create<Bpl.Variable, Bpl.Expr>(yVar, wh));
          subst[bv] = new BoogieWrapper(ve, bv.Type);
        }

        var canCall = CanCallAssumption(Substitute(e.Body, null, subst), et);
        if (e.Range != null) {
          var range = Substitute(e.Range, null, subst);
          canCall = BplAnd(CanCallAssumption(range, etran), BplImp(etran.TrExpr(range), canCall));
        }

        // It's important to add the heap last to "bvarsAndAntecedents", because the heap may occur in the antecedents of
        // the other variables and BplForallTrim processes the given tuples in order.
        var goodHeap = FunctionCall(e.tok, BuiltinFunction.IsGoodHeap, null, heap);
        bvarsAndAntecedents.Add(Tuple.Create<Bpl.Variable, Bpl.Expr>(hVar, goodHeap));

        //TRIG (forall $l#0#heap#0: Heap, $l#0#x#0: int :: true)
        //TRIG (forall $l#0#heap#0: Heap, $l#0#t#0: DatatypeType :: _module.__default.TMap#canCall(_module._default.TMap$A, _module._default.TMap$B, $l#0#heap#0, $l#0#t#0, f#0))
        //TRIG (forall $l#4#heap#0: Heap, $l#4#x#0: Box :: _0_Monad.__default.Bind#canCall(Monad._default.Associativity$B, Monad._default.Associativity$C, $l#4#heap#0, Apply1(Monad._default.Associativity$A, #$M$B, f#0, $l#4#heap#0, $l#4#x#0), g#0))
        return BplForallTrim(bvarsAndAntecedents, null, canCall); // L_TRIGGER

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        if (e is QuantifierExpr q && q.SplitQuantifier != null) {
          return CanCallAssumption(q.SplitQuantifierExpression, etran);
        }

        // Determine the CanCall's for the range and term
        var canCall = CanCallAssumption(e.Term, etran);
        if (e.Range != null) {
          canCall = BplAnd(CanCallAssumption(e.Range, etran), BplImp(etran.TrExpr(e.Range), canCall));
        }
        if (expr is MapComprehension mc && mc.IsGeneralMapComprehension) {
          canCall = BplAnd(canCall, CanCallAssumption(mc.TermLeft, etran));

          // The translation of "map x,y | R(x,y) :: F(x,y) := G(x,y)" makes use of projection
          // functions project_x,project_y.  These are functions defined here by the following axiom:
          //     forall x,y :: R(x,y) ==> var x',y' := project_x(F(x,y)),project_y(F(x,y)); R(x',y') && F(x',y') == F(x,y)
          // that is (without the let expression):
          //     forall x,y :: R(x,y) ==> R(project_x(F(x,y)), project_y(F(x,y))) && F(project_x(F(x,y)), project_y(F(x,y))) == F(x,y)
          // The triggers for the quantification are those detected for the given map comprehension, if any.
          List<Bpl.Variable> bvs;
          List<Bpl.Expr> args;
          CreateBoundVariables(mc.BoundVars, out bvs, out args);
          Contract.Assert(mc.BoundVars.Count == bvs.Count);
          CreateMapComprehensionProjectionFunctions(mc);
          Contract.Assert(mc.ProjectionFunctions != null);
          Contract.Assert(mc.ProjectionFunctions.Count == mc.BoundVars.Count);
          var substMap = new Dictionary<IVariable, Expression>();
          for (var i = 0; i < mc.BoundVars.Count; i++) {
            substMap.Add(mc.BoundVars[i], new BoogieWrapper(args[i], mc.BoundVars[i].Type));
          }
          var R = etran.TrExpr(Substitute(mc.Range, null, substMap));
          var F = etran.TrExpr(Substitute(mc.TermLeft, null, substMap));
          var trig = TrTrigger(etran, e.Attributes, expr.tok, substMap);
          substMap = new Dictionary<IVariable, Expression>();
          for (var i = 0; i < mc.BoundVars.Count; i++) {
            var p = new Bpl.NAryExpr(GetToken(mc), new Bpl.FunctionCall(mc.ProjectionFunctions[i]), new List<Bpl.Expr> { F });
            substMap.Add(e.BoundVars[i], new BoogieWrapper(p, e.BoundVars[i].Type));
          }
          var Rprime = etran.TrExpr(Substitute(mc.Range, null, substMap));
          var Fprime = etran.TrExpr(Substitute(mc.TermLeft, null, substMap));
          var defn = BplForall(bvs, trig, BplImp(R, BplAnd(Rprime, Bpl.Expr.Eq(F, Fprime))));
          canCall = BplAnd(canCall, defn);
        }
        // Create a list of all possible bound variables
        var bvarsAndAntecedents = etran.TrBoundVariables_SeparateWhereClauses(e.BoundVars);
        // Produce the quantified CanCall expression, with a suitably reduced set of bound variables
        var tr = TrTrigger(etran, e.Attributes, expr.tok);
        return BplForallTrim(bvarsAndAntecedents, tr, canCall);

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return CanCallAssumption(e.E, etran);
      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Bpl.Expr total = CanCallAssumption(e.Test, etran);
        Bpl.Expr test = etran.TrExpr(e.Test);
        total = BplAnd(total, BplImp(test, CanCallAssumption(e.Thn, etran)));
        total = BplAnd(total, BplImp(Bpl.Expr.Not(test), CanCallAssumption(e.Els, etran)));
        return total;
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return CanCallAssumption(e.ResolvedExpression, etran);
      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        return CanCallAssumption(nestedMatchExpr.Flattened, etran);
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

    void AddCasePatternVarSubstitutions(CasePattern<BoundVar> pat, Bpl.Expr rhs, Dictionary<IVariable, Expression> substMap) {
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

    /// <summary>
    /// If "expr" is a binary boolean operation, then try to re-associate it to make the left argument smaller.
    /// If it is possible, then "true" is returned and "expr" returns as the re-associated expression (no boolean simplifications are performed).
    /// If not, then "false" is returned and "expr" is unchanged.
    /// </summary>
    bool ReAssociateToTheRight(ref Expression expr) {
      if (expr is BinaryExpr top && Expression.StripParens(top.E0) is BinaryExpr left) {
        // We have an expression of the form "(A oo B) pp C"
        var A = left.E0;
        var oo = left.ResolvedOp;
        var B = left.E1;
        var pp = top.ResolvedOp;
        var C = top.E1;

        if (oo == BinaryExpr.ResolvedOpcode.And && pp == BinaryExpr.ResolvedOpcode.And) {
          // rewrite    (A && B) && C    into    A && (B && C)
          expr = Expression.CreateAnd(A, Expression.CreateAnd(B, C, false), false);
          return true;
        } else if (oo == BinaryExpr.ResolvedOpcode.And && pp == BinaryExpr.ResolvedOpcode.Imp) {
          // rewrite    (A && B) ==> C    into    A ==> (B ==> C)
          expr = Expression.CreateImplies(A, Expression.CreateImplies(B, C, false), false);
          return true;
        } else if (oo == BinaryExpr.ResolvedOpcode.Or && pp == BinaryExpr.ResolvedOpcode.Or) {
          // rewrite    (A || B) || C    into    A || (B || C)
          expr = Expression.CreateOr(A, Expression.CreateOr(B, C, false), false);
          return true;
        } else if (oo == BinaryExpr.ResolvedOpcode.Imp && pp == BinaryExpr.ResolvedOpcode.Or) {
          // rewrite    (A ==> B) || C    into    A ==> (B || C)
          expr = Expression.CreateImplies(A, Expression.CreateOr(B, C, false), false);
          return true;
        }
      }
      return false;
    }

    void CheckCasePatternShape<VT>(CasePattern<VT> pat, Bpl.Expr rhs, IToken rhsTok, Type rhsType, BoogieStmtListBuilder builder)
      where VT : class, IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(rhs != null);
      Contract.Requires(rhsTok != null);
      Contract.Requires(rhsType != null);
      Contract.Requires(builder != null);
      if (pat.Var != null) {
        CheckSubrange(rhsTok, rhs, rhsType, pat.Var.Type, builder);
      } else if (pat.Arguments != null) {
        Contract.Assert(pat.Ctor != null);  // follows from successful resolution
        Contract.Assert(pat.Arguments.Count == pat.Ctor.Destructors.Count);  // follows from successful resolution
        rhsType = rhsType.Normalize();
        Contract.Assert(rhsType is UserDefinedType && ((UserDefinedType)rhsType).ResolvedClass != null);
        var rhsTypeUdt = (UserDefinedType)rhsType;
        var typeSubstMap = TypeParameter.SubstitutionMap(rhsTypeUdt.ResolvedClass.TypeArgs, rhsTypeUdt.TypeArgs);

        var ctor = pat.Ctor;
        var correctConstructor = FunctionCall(pat.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, rhs);
        if (ctor.EnclosingDatatype.Ctors.Count == 1) {
          // There is only one constructor, so the value must have been constructed by it; might as well assume that here.
          builder.Add(TrAssumeCmd(pat.tok, correctConstructor));
        } else {
          builder.Add(Assert(pat.tok, correctConstructor, new PODesc.PatternShapeIsValid(ctor.Name)));
        }
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var dtor = ctor.Destructors[i];

          var r = new Bpl.NAryExpr(arg.tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          Type argType = dtor.Type.Subst(typeSubstMap);
          var de = CondApplyUnbox(arg.tok, r, dtor.Type, argType);
          CheckCasePatternShape(arg, de, arg.tok, argType, builder);
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

    void CheckNonNull(IToken tok, Expression e, BoogieStmtListBuilder builder, ExpressionTranslator etran, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (!e.Type.IsRefType) {
        // nothing to do
      } else if (e is ThisExpr) {
        // already known to be non-null
      } else if (e is StaticReceiverExpr) {
        // also ok
      } else {
        builder.Add(Assert(tok, Bpl.Expr.Neq(etran.TrExpr(e), predef.Null), new PODesc.NonNull("target object"), kv));
      }
    }

    void TrStmt_CheckWellformed(Expression expr, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, bool subsumption, bool lValueContext = false) {
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      Bpl.QKeyValue kv;
      if (subsumption) {
        kv = null;  // this is the default behavior of Boogie's assert
      } else {
        List<object> args = new List<object>();
        // {:subsumption 0}
        args.Add(Bpl.Expr.Literal(0));
        kv = new Bpl.QKeyValue(expr.tok, "subsumption", args, null);
      }
      var options = new WFOptions(kv);
      // Only do reads checks if reads clauses on methods are enabled and the reads clause is not *.
      // The latter is important to avoid any extra verification cost for backwards compatibility.
      if (etran.readsFrame != null) {
        options = options.WithReadsChecks(true);
      }
      if (lValueContext) {
        options = options.WithLValueContext(true);
      }
      CheckWellformed(expr, options, locals, builder, etran);
      builder.Add(TrAssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
    }

    /// <summary>
    /// Returns the translation of converting "r", whose Dafny type was "fromType", to a value of type "toType".
    /// The translation assumes that "r" is known to be a value of type "toType".
    /// </summary>
    Bpl.Expr ConvertExpression(IToken tok, Bpl.Expr r, Type fromType, Type toType) {
      Contract.Requires(tok != null);
      Contract.Requires(r != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);
      toType = toType.NormalizeExpand();
      fromType = fromType.NormalizeExpand();
      if (fromType.IsNumericBased(Type.NumericPersuasion.Int)) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
          // do nothing
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
        } else if (toType.IsCharType) {
          r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
        } else if (toType.IsBitVectorType) {
          r = IntToBV(tok, r, toType);
        } else if (toType.IsBigOrdinalType) {
          r = FunctionCall(tok, "ORD#FromNat", predef.BigOrdinalType, r);
        } else {
          Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
        }
        return r;
      } else if (fromType.IsBitVectorType) {
        var fromWidth = fromType.AsBitVectorType.Width;
        if (toType.IsBitVectorType) {
          // conversion from one bitvector type to another
          var toWidth = toType.AsBitVectorType.Width;
          if (fromWidth == toWidth) {
            // no conversion
          } else if (fromWidth < toWidth) {
            var zeros = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, toWidth - fromWidth);
            if (fromWidth == 0) {
              r = zeros;
            } else {
              var concat = new Bpl.BvConcatExpr(tok, zeros, r);
              // There's a bug in Boogie that causes a warning to be emitted if a BvConcatExpr is passed as the argument
              // to $Box, which takes a type argument.  The bug can apparently be worked around by giving an explicit
              // (and other redudant) type conversion.
              r = Bpl.Expr.CoerceType(tok, concat, BplBvType(toWidth));
            }
          } else if (toWidth == 0) {
            r = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, toWidth);
          } else {
            r = new Bpl.BvExtractExpr(tok, r, toWidth, 0);
          }
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
          r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
          r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
        } else if (toType.IsCharType) {
          r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
          r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
        } else if (toType.IsBigOrdinalType) {
          r = FunctionCall(tok, "nat_from_bv" + fromWidth, Bpl.Type.Int, r);
          r = FunctionCall(tok, "ORD#FromNat", predef.BigOrdinalType, r);
        } else {
          Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
        }
        return r;
      } else if (fromType.IsCharType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
          r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
        } else if (toType.IsCharType) {
          // do nothing
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
          r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
        } else if (toType.IsBitVectorType) {
          r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
          r = IntToBV(tok, r, toType);
        } else if (toType.IsBigOrdinalType) {
          r = FunctionCall(tok, BuiltinFunction.CharToInt, null, r);
          r = FunctionCall(tok, "ORD#FromNat", Bpl.Type.Int, r);
        } else {
          Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
        }
        return r;
      } else if (fromType.IsNumericBased(Type.NumericPersuasion.Real)) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          // do nothing
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
          r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
        } else if (toType.IsBitVectorType) {
          r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
          r = IntToBV(tok, r, toType);
        } else if (toType.IsCharType) {
          r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
          r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
        } else if (toType.IsBigOrdinalType) {
          r = FunctionCall(tok, BuiltinFunction.RealToInt, null, r);
          r = FunctionCall(tok, "ORD#FromNat", Bpl.Type.Int, r);
        } else {
          Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
        }
        return r;
        // "r" now denotes an integer
      } else if (fromType.IsBigOrdinalType) {
        if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
          r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
        } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
          r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
          r = FunctionCall(tok, BuiltinFunction.IntToReal, null, r);
        } else if (toType.IsCharType) {
          r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
          r = FunctionCall(tok, BuiltinFunction.CharFromInt, null, r);
        } else if (toType.IsBitVectorType) {
          r = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, r);
          r = IntToBV(tok, r, toType);
        } else if (toType.IsBigOrdinalType) {
          // do nothing
        } else {
          Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
        }
        return r;
      } else if (fromType.IsRefType && toType.IsRefType) {
        return r;
      } else if (fromType.IsRefType) {
        Contract.Assert(toType.IsTraitType);
        return BoxIfNecessary(r.tok, r, fromType);
      } else if (toType.IsRefType) {
        Contract.Assert(fromType.IsTraitType);
        return UnboxIfBoxed(r, toType);
      } else if (toType.IsTraitType) {
        // cast to a non-reference trait
        return BoxIfNecessary(r.tok, r, fromType);
      } else if (fromType.IsTraitType) {
        // cast from a non-reference trait
        return UnboxIfBoxed(r, toType);
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    }

    private Bpl.Expr IntToBV(IToken tok, Bpl.Expr r, Type toType) {
      var toWidth = toType.AsBitVectorType.Width;
      if (RemoveLit(r) is Bpl.LiteralExpr) {
        Bpl.LiteralExpr e = (Bpl.LiteralExpr)RemoveLit(r);
        if (e.isBigNum) {
          var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth);  // 1 << toWidth
          if (e.asBigNum <= toBound) {
            return BplBvLiteralExpr(r.tok, e.asBigNum, toType.AsBitVectorType);
          }
        }
      }
      return FunctionCall(tok, "nat_to_bv" + toWidth, BplBvType(toWidth), r);
    }

    /// <summary>
    /// Emit checks that "expr" (which may or may not be a value of type "expr.Type"!) is a value of type "toType".
    /// </summary>
    void CheckResultToBeInType(IToken tok, Expression expr, Type toType, List<Bpl.Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran, string errorMsgPrefix = "") {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(errorMsgPrefix != null);

      // Lazily create a local variable "o" to hold the value of the from-expression
      Bpl.IdentifierExpr o = null;
      void PutSourceIntoLocal() {
        if (o == null) {
          var oType = expr.Type.IsCharType ? Type.Int : expr.Type;
          var oVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("newtype$check#"), TrType(oType)));
          locals.Add(oVar);
          o = new Bpl.IdentifierExpr(tok, oVar);
          var rhs = etran.TrExpr(expr);
          if (expr.Type.IsCharType) {
            rhs = FunctionCall(expr.tok, "char#ToInt", Bpl.Type.Int, rhs);
          }
          builder.Add(Bpl.Cmd.SimpleAssign(tok, o, rhs));
        }
      }

      Contract.Assert(options.Get(CommonOptionBag.GeneralTraits) != CommonOptionBag.GeneralTraitsOptions.Legacy || expr.Type.IsRefType == toType.IsRefType);
      if (toType.IsRefType) {
        PutSourceIntoLocal();
        CheckSubrange(tok, o, expr.Type, toType, builder, errorMsgPrefix);
        return;
      } else if (expr.Type.IsTraitType) {
        PutSourceIntoLocal();
        CheckSubrange(tok, o, expr.Type, toType, builder, errorMsgPrefix);
        return;
      }

      if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real) && !toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        // this operation is well-formed only if the real-based number represents an integer
        //   assert Real(Int(o)) == o;
        PutSourceIntoLocal();
        Bpl.Expr from = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
        Bpl.Expr e = FunctionCall(tok, BuiltinFunction.IntToReal, null, from);
        e = Bpl.Expr.Binary(tok, Bpl.BinaryOperator.Opcode.Eq, e, o);
        builder.Add(Assert(tok, e, new PODesc.IsInteger(errorMsgPrefix)));
      }

      if (expr.Type.IsBigOrdinalType && !toType.IsBigOrdinalType) {
        PutSourceIntoLocal();
        Bpl.Expr boundsCheck = FunctionCall(tok, "ORD#IsNat", Bpl.Type.Bool, o);
        builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionIsNatural(errorMsgPrefix)));
      }

      if (toType.IsBitVectorType) {
        var toWidth = toType.AsBitVectorType.Width;
        var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth);  // 1 << toWidth
        Bpl.Expr boundsCheck = null;
        if (expr.Type.IsBitVectorType) {
          var fromWidth = expr.Type.AsBitVectorType.Width;
          if (toWidth < fromWidth) {
            // Check "expr < (1 << toWidth)" in type "fromType" (note that "1 << toWidth" is indeed a value in "fromType")
            PutSourceIntoLocal();
            var bound = BplBvLiteralExpr(tok, toBound, expr.Type.AsBitVectorType);
            boundsCheck = FunctionCall(expr.tok, "lt_bv" + fromWidth, Bpl.Type.Bool, o, bound);
          }
        } else if (expr.Type.IsNumericBased(Type.NumericPersuasion.Int) || expr.Type.IsCharType) {
          // Check "expr < (1 << toWdith)" in type "int"
          PutSourceIntoLocal();
          var bound = Bpl.Expr.Literal(toBound);
          boundsCheck = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), o), Bpl.Expr.Lt(o, bound));
        } else if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          // Check "Int(expr) < (1 << toWdith)" in type "int"
          PutSourceIntoLocal();
          var bound = Bpl.Expr.Literal(toBound);
          var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
          boundsCheck = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), oi), Bpl.Expr.Lt(oi, bound));
        } else if (expr.Type.IsBigOrdinalType) {
          var bound = Bpl.Expr.Literal(toBound);
          var oi = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, o);
          boundsCheck = Bpl.Expr.Lt(oi, bound);
        }

        if (boundsCheck != null) {
          builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionFit("value", toType, errorMsgPrefix)));
        }
      }

      if (toType.IsCharType) {
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          PutSourceIntoLocal();
          var boundsCheck = FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null, o);
          builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionFit("value", toType, errorMsgPrefix)));
        } else if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
          var boundsCheck = FunctionCall(Token.NoToken, BuiltinFunction.IsChar, null, oi);
          builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionFit("real value", toType, errorMsgPrefix)));
        } else if (expr.Type.IsBitVectorType) {
          PutSourceIntoLocal();
          var fromWidth = expr.Type.AsBitVectorType.Width;
          var toWidth = 16;
          if (toWidth < fromWidth) {
            // Check "expr < (1 << toWidth)" in type "fromType" (note that "1 << toWidth" is indeed a value in "fromType")
            PutSourceIntoLocal();
            var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth); // 1 << toWidth
            var bound = BplBvLiteralExpr(tok, toBound, expr.Type.AsBitVectorType);
            var boundsCheck = FunctionCall(expr.tok, "lt_bv" + fromWidth, Bpl.Type.Bool, o, bound);
            builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionFit("bit-vector value", toType, errorMsgPrefix)));
          }
        } else if (expr.Type.IsBigOrdinalType) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, o);
          int toWidth = 16;
          var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth); // 1 << toWidth
          var bound = Bpl.Expr.Literal(toBound);
          var boundsCheck = Bpl.Expr.Lt(oi, bound);
          builder.Add(Assert(tok, boundsCheck, new PODesc.ConversionFit("ORDINAL value", toType, errorMsgPrefix)));
        }
      } else if (toType.IsBigOrdinalType) {
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          PutSourceIntoLocal();
          Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), o);
          var desc = new PODesc.ConversionPositive("integer", toType, errorMsgPrefix);
          builder.Add(Assert(tok, boundsCheck, desc));
        }
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
          Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), oi);
          var desc = new PODesc.ConversionPositive("real", toType, errorMsgPrefix);
          builder.Add(Assert(tok, boundsCheck, desc));
        }
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Int)) {
        // already checked that BigOrdinal or real inputs are integral
      } else if (toType.IsNumericBased(Type.NumericPersuasion.Real)) {
        // already checked that BigOrdinal is integral
      }

      if (toType.NormalizeExpandKeepConstraints().AsRedirectingType != null) {
        PutSourceIntoLocal();
        Bpl.Expr be;
        if (expr.Type.IsNumericBased() || expr.Type.IsBitVectorType) {
          be = ConvertExpression(expr.tok, o, expr.Type, toType);
        } else if (expr.Type.IsCharType) {
          be = ConvertExpression(expr.tok, o, Dafny.Type.Int, toType);
        } else if (expr.Type.IsBigOrdinalType) {
          be = FunctionCall(expr.tok, "ORD#Offset", Bpl.Type.Int, o);
          be = ConvertExpression(expr.tok, be, Dafny.Type.Int, toType);
        } else {
          be = o;
        }
        var dafnyType = toType.NormalizeExpand();
        CheckResultToBeInType_Aux(tok, new BoogieWrapper(be, dafnyType), toType.NormalizeExpandKeepConstraints(), builder, etran, errorMsgPrefix);
      }
    }

    void CheckResultToBeInType_Aux(IToken tok, Expression expr, Type toType, BoogieStmtListBuilder builder, ExpressionTranslator etran, string errorMsgPrefix) {
      Contract.Requires(tok != null);
      Contract.Requires(expr != null);
      Contract.Requires(toType != null && toType.AsRedirectingType != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(errorMsgPrefix != null);
      // First, check constraints of base types
      var udt = (UserDefinedType)toType;
      var rdt = (RedirectingTypeDecl)udt.ResolvedClass;
      Type baseType;
      string kind;
      if (rdt is SubsetTypeDecl) {
        baseType = ((SubsetTypeDecl)rdt).RhsWithArgument(udt.TypeArgs);
        kind = "subset type";
      } else if (rdt is NewtypeDecl) {
        baseType = ((NewtypeDecl)rdt).BaseType;
        kind = "newtype";
      } else {
        baseType = ((TypeSynonymDecl)rdt).RhsWithArgument(udt.TypeArgs);
        kind = "type synonym";
      }

      if (baseType.AsRedirectingType != null) {
        CheckResultToBeInType_Aux(tok, expr, baseType, builder, etran, errorMsgPrefix);
      }
      // Check any constraint defined in 'dd'
      if (rdt.Var != null) {
        // TODO: use TrSplitExpr
        var substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(rdt.Var, expr);
        var typeMap = TypeParameter.SubstitutionMap(rdt.TypeArgs, udt.TypeArgs);
        var constraint = etran.TrExpr(Substitute(rdt.Constraint, null, substMap, typeMap));
        builder.Add(Assert(tok, constraint, new PODesc.ConversionSatisfiesConstraints(errorMsgPrefix, kind, rdt.Name)));
      }
    }


    void CheckFunctionSelectWF(string what, BoogieStmtListBuilder builder, ExpressionTranslator etran, Expression e, string hint) {
      if (e is MemberSelectExpr sel && sel.Member is Function fn) {
        Bpl.Expr assertion = !InVerificationScope(fn) ? Bpl.Expr.True : Bpl.Expr.Not(etran.HeightContext(fn));
        builder.Add(Assert(GetToken(e), assertion, new PODesc.ValidInRecursion(what, hint)));
      }
    }

    void CloneVariableAsBoundVar(IToken tok, IVariable iv, string prefix, out BoundVar bv, out IdentifierExpr ie) {
      Contract.Requires(tok != null);
      Contract.Requires(iv != null);
      Contract.Requires(prefix != null);
      Contract.Ensures(Contract.ValueAtReturn(out bv) != null);
      Contract.Ensures(Contract.ValueAtReturn(out ie) != null);

      bv = new BoundVar(tok, CurrentIdGenerator.FreshId(prefix), iv.Type); // use this temporary variable counter, but for a Dafny name (the idea being that the number and the initial "_" in the name might avoid name conflicts)
      ie = new IdentifierExpr(tok, bv.Name);
      ie.Var = bv;  // resolve here
      ie.Type = bv.Type;  // resolve here
    }

    // Use trType to translate types in the args list
    Bpl.Expr ClassTyCon(UserDefinedType cl, List<Bpl.Expr> args) {
      Contract.Requires(cl != null);
      Contract.Requires(cce.NonNullElements(args));
      return ClassTyCon(cl.ResolvedClass, args);
    }

    Bpl.Expr ClassTyCon(TopLevelDecl cl, List<Bpl.Expr> args) {
      Contract.Requires(cl != null);
      Contract.Requires(cce.NonNullElements(args));
      return FunctionCall(cl.tok, GetClassTyCon(cl), predef.Ty, args);
    }

    // Takes a Bpl.Constant, which typically will be one from GetClass,
    // or some built-in type which has a class name, like Arrays or Arrows.
    // Note: Prefer to call ClassTyCon or TypeToTy instead.
    private string GetClassTyCon(TopLevelDecl dl) {
      Contract.Requires(dl != null);
      if (dl is InternalTypeSynonymDecl isyn) {
        dl = ((UserDefinedType)isyn.Rhs).ResolvedClass;
      }
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

    public static string Apply(int arity) {
      return "Apply" + arity;
    }

    public static string Requires(int arity) {
      return "Requires" + arity;
    }

    public static string Reads(int arity) {
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
        var argsRequires = new List<Bpl.Expr>(args); // Requires don't have reveal parameters
        var formals = MkTyParamFormals(GetTypeParams(f), false, true);
        var tyargs = new List<Bpl.Expr>();
        foreach (var fm in f.Formals) {
          tyargs.Add(TypeToTy(fm.Type));
        }
        tyargs.Add(TypeToTy(f.ResultType));
        if (f.IsFuelAware()) {
          vars.Add(BplBoundVar("$ly", predef.LayerType, out var ly));
          args.Add(ly);
          argsRequires.Add(ly);
          formals.Add(BplFormalVar("$fuel", predef.LayerType, true));
          AddFuelSuccSynonymAxiom(f, true);
        }
        if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
          vars.Add(BplBoundVar("$reveal", Boogie.Type.Bool, out var reveal));
          args.Add(reveal);
          formals.Add(BplFormalVar("$reveal", Boogie.Type.Bool, true));
        }

        Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocSelf = x => x;
        Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocPrevH = x => x;
        Expression selfExpr;
        Dictionary<IVariable, Expression> rhs_dict = new Dictionary<IVariable, Expression>();
        if (f is TwoStateFunction) {
          // also add previous-heap to the list of fixed arguments of the handle
          var prevH = BplBoundVar("$prevHeap", predef.HeapType, vars);
          formals.Add(BplFormalVar("h", predef.HeapType, true));
          SnocPrevH = xs => Snoc(xs, prevH);
        }
        if (f.IsStatic) {
          selfExpr = null;
        } else {
          var selfTy = TrType(UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass));
          var self = BplBoundVar("$self", selfTy, vars);
          formals.Add(BplFormalVar("self", selfTy, true));
          SnocSelf = xs => Snoc(xs, self);
          var wrapperType = UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass);
          selfExpr = new BoogieWrapper(self, wrapperType);
        }

        // F#Handle(Ty, .., Ty, LayerType, ref) : HandleType
        sink.AddTopLevelDeclaration(
          new Bpl.Function(f.tok, name, formals, BplFormalVar(null, predef.HandleType, false)));

        var bvars = new List<Bpl.Variable>();
        var lhs_args = new List<Bpl.Expr>();
        var rhs_args = new List<Bpl.Expr>();
        var func_vars = new List<Bpl.Variable>();
        var func_args = new List<Bpl.Expr>();
        var boxed_func_args = new List<Bpl.Expr>();

        var idGen = f.IdGenerator.NestedFreshIdGenerator("$fh$");
        foreach (var fm in f.Formals) {
          string fm_name = idGen.FreshId("x#");
          // Box and its [Unbox]args
          var fe = BplBoundVar(fm_name, predef.BoxType, bvars);
          lhs_args.Add(fe);
          var be = UnboxIfBoxed(fe, fm.Type);
          rhs_args.Add(be);

          rhs_dict[fm] = new BoogieWrapper(be, fm.Type);
          // args and its [Box]args
          var arg = BplBoundVar(fm_name, TrType(fm.Type), func_vars);
          func_args.Add(arg);
          var boxed = BoxIfUnboxed(arg, fm.Type);
          boxed_func_args.Add(boxed);
        }

        var h = BplBoundVar("$heap", predef.HeapType, vars);

        int arity = f.Formals.Count;

        {
          // Apply(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
          //   = [Box] F(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          var lhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType),
            Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
          var rhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), rhs_args));
          var rhs_boxed = BoxIfUnboxed(rhs, f.ResultType);

          AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs_boxed)))));
        }

        {
          // As a first approximation, the following axiom is of the form:
          // Requires(Ty.., F#Handle( Ty1, ..., TyN, Layer, reveal, self), Heap, arg1, ..., argN)
          //   = F#Requires(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)
          // However, .reads ands .requires functions require special attention.
          // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
          // The requires clause of the .requires function is simply true.
          // The requires clause of the .reads function checks that the precondtion of the receiving function holds.

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          var lhs = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
          Bpl.Expr rhs;
          if (f.EnclosingClass is ArrowTypeDecl && f.Name == "requires") {
            AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.tok,
                BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, Bpl.Expr.True))));
          } else if (f.EnclosingClass is ArrowTypeDecl && f.Name == "reads") {
            var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
            var pre = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
            AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
              BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, pre)))));
          } else {
            var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
            rhs = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, Concat(SnocSelf(args_h), rhs_args));
            AddOtherDefinition(GetOrCreateFunction(f), new Axiom(f.tok,
              BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
          }


        }

        {
          // As a first approximation, the following axiom is of the form:
          // Reads(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
          //   =  $Frame_F(args...)
          // However, .reads ands .requires functions require special attention.
          // To understand the rationale for these axioms, refer to the section on arrow types of the reference manual.
          // In both cases, the precondition of the receiving function must be checked before its reads clause can
          // be referred to.

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          Bpl.Expr lhs_inner = FunctionCall(f.tok, Reads(arity), TrType(program.SystemModuleManager.ObjectSetType()), Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));

          Bpl.Expr bx; var bxVar = BplBoundVar("$bx", predef.BoxType, out bx);
          Bpl.Expr unboxBx = FunctionCall(f.tok, BuiltinFunction.Unbox, predef.RefType, bx);
          Bpl.Expr lhs = Bpl.Expr.SelectTok(f.tok, lhs_inner, bx);

          var et = new ExpressionTranslator(this, predef, h);
          var rhs = InRWClause_Aux(f.tok, unboxBx, bx, null, f.Reads.Expressions, false, et, selfExpr, rhs_dict);

          if (f.EnclosingClass is ArrowTypeDecl) {
            var args_h = f.ReadsHeap ? Snoc(SnocPrevH(argsRequires), h) : argsRequires;
            var precondition = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(SnocSelf(args_h), lhs_args));
            sink.AddTopLevelDeclaration(new Axiom(f.tok,
              BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Imp(precondition, Bpl.Expr.Eq(lhs, rhs)))));
          } else {
            sink.AddTopLevelDeclaration(new Axiom(f.tok,
              BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
          }
        }

        {
          // F(Ty1, .., TyN, Layer, Heap, self, arg1, .., argN)
          // = [Unbox]Apply1(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, [Box]arg1, ..., [Box]argN)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          var args_h = f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
          var lhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), func_args));
          var rhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(h, Cons(fhandle, boxed_func_args))));
          var rhs_unboxed = UnboxIfBoxed(rhs, f.ResultType);
          var tr = BplTriggerHeap(this, f.tok, lhs, f.ReadsHeap ? null : h);

          AddOtherDefinition(GetOrCreateFunction(f), (new Axiom(f.tok,
            BplForall(Concat(vars, func_vars), tr, Bpl.Expr.Eq(lhs, rhs_unboxed)))));
        }
      }
      return name;
    }

    private Expr NewOneHeapExpr(IToken tok) {
      return new Bpl.IdentifierExpr(tok, "$OneHeap", predef.HeapType);
    }

    /// <summary>
    /// For expression "e" that is expected to come from a modifies/unchanged frame, return information
    /// that is useful for checking every reference from "e". More precisely,
    ///  * If "e" denotes a reference, then return
    ///       -- "description" as the string "object",
    ///       -- "type" as the type of that reference,
    ///       -- "obj" as the translation of that reference, and
    ///       -- "antecedent" as "true".
    ///  * If "e" denotes a set of references, then return
    ///       -- "description" as the string "set element",
    ///       -- "type" as the element type of that set,
    ///       -- "obj" as a new identifier of type "type", and
    ///       -- "antecedent" as "obj in e".
    ///  * If "e" denotes a multiset of references, then return
    ///       -- "description" as the string "multiset element",
    ///       -- "type" as the element type of that multiset,
    ///       -- "obj" as a new identifier of type "type", and
    ///       -- "antecedent" as "e[obj] > 0".
    ///  * If "e" denotes a sequence of references, then return
    ///       -- "description" as the string "sequence element",
    ///       -- "type" as the element type of that sequence,
    ///       -- "obj" as an expression "e[i]", where "i" is a new identifier, and
    ///       -- "antecedent" as "0 <= i < |e|".
    /// </summary>
    void EachReferenceInFrameExpression(Expression e, List<Bpl.Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran,
      out string description, out Type type, out Bpl.Expr obj, out Bpl.Expr antecedent) {
      Contract.Requires(e != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);

      if (e.Type.IsRefType) {
        description = "object";
        type = e.Type;
        obj = etran.TrExpr(e);
        antecedent = Bpl.Expr.True;
        return;
      }

      var isSetType = e.Type.AsSetType != null;
      var isMultisetType = e.Type.AsMultiSetType != null;
      Contract.Assert(isSetType || isMultisetType || e.Type.AsSeqType != null);
      var sType = e.Type.AsCollectionType;
      Contract.Assert(sType != null);
      type = sType.Arg;
      // var $x
      var name = CurrentIdGenerator.FreshId("$unchanged#x");
      var xVar = new Bpl.LocalVariable(e.tok, new Bpl.TypedIdent(e.tok, name, isSetType || isMultisetType ? TrType(type) : Bpl.Type.Int));
      locals.Add(xVar);
      var x = new Bpl.IdentifierExpr(e.tok, xVar);
      // havoc $x
      builder.Add(new Bpl.HavocCmd(e.tok, new List<Bpl.IdentifierExpr>() { x }));

      var s = etran.TrExpr(e);
      if (isSetType) {
        description = "set element";
        obj = x;
        antecedent = Bpl.Expr.SelectTok(e.tok, s, BoxIfNecessary(e.tok, x, type));
      } else if (isMultisetType) {
        description = "multiset element";
        obj = x;
        antecedent = Boogie.Expr.Gt(Bpl.Expr.SelectTok(e.tok, s, BoxIfNecessary(e.tok, x, type)), Boogie.Expr.Literal(0));
      } else {
        description = "sequence element";
        obj = UnboxIfBoxed(FunctionCall(e.tok, BuiltinFunction.SeqIndex, predef.BoxType, s, x), type);
        antecedent = InSeqRange(e.tok, x, Type.Int, s, true, null, false);
      }
    }

    private Bpl.Function GetOrCreateTypeConstructor(TopLevelDecl td) {
      if (declarationMapping.TryGetValue(td, out var result)) {
        return result;
      }

      Bpl.Function func;
      if (td is TraitDecl { IsObjectTrait: true }) {
        // the type constructor for "object" is in DafnyPrelude.bpl
        func = predef.ObjectTypeConstructor;
      } else if (td is TupleTypeDecl ttd && ttd.Dims == 2 && ttd.NonGhostDims == 2) {
        // the type constructor for "Tuple2" is in DafnyPrelude.bpl
        func = this.predef.Tuple2TypeConstructor;
      } else {
        var inner_name = GetClass(td).TypedIdent.Name;
        string name = "T" + inner_name;

        Bpl.Variable tyVarOut = BplFormalVar(null, predef.Ty, false);
        var args = td.TypeArgs.ConvertAll(_ => (Bpl.Variable)BplFormalVar(null, predef.Ty, true));
        func = new Bpl.Function(td.tok, name, args, tyVarOut);
        sink.AddTopLevelDeclaration(func);

        if (td is AbstractTypeDecl or InternalTypeSynonymDecl) {
          // axiom (forall T0, T1, ... { T(T0, T1, T2) } :: WhereClause( T(T0, T1, T2) ));
          var argBoundVars = new List<Bpl.Variable>();
          var argExprs = td.TypeArgs.ConvertAll(ta => BplBoundVar(ta.Name, predef.Ty, argBoundVars));
          var funcAppl = FunctionCall(td.tok, name, predef.Ty, argExprs);
          var characteristics = td is AbstractTypeDecl ? ((AbstractTypeDecl)td).Characteristics : ((InternalTypeSynonymDecl)td).Characteristics;
          var whereClause = GetTyWhereClause(funcAppl, characteristics);
          if (whereClause != null) {
            Bpl.Expr axiom;
            if (td.TypeArgs.Count == 0) {
              axiom = whereClause;
            } else {
              var tr = new Bpl.Trigger(td.tok, true, new List<Bpl.Expr> { funcAppl });
              axiom = new Bpl.ForallExpr(td.tok, new List<Bpl.TypeVariable>(), argBoundVars, null, tr, whereClause);
            }
            AddOtherDefinition(func, BplAxiom(axiom));
          }
        }
      }

      declarationMapping[td] = func;
      return func;
    }

    Bpl.Constant GetClass(TopLevelDecl cl) {
      Contract.Requires(cl != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      if (classes.TryGetValue(cl, out var cc)) {
        Contract.Assert(cc != null);
      } else {
        var name = cl.FullSanitizedName;
        if (cl is ClassLikeDecl { NonNullTypeDecl: { } }) {
          name = name + "?";  // TODO: this doesn't seem like the best place to do this name transformation
        }
        cc = new Bpl.Constant(cl.tok, new Bpl.TypedIdent(cl.tok, "class." + name, predef.ClassNameType), !cl.EnclosingModuleDefinition.IsFacade);
        classes.Add(cl, cc);
      }
      return cc;
    }

    Bpl.Constant GetFieldNameFamily(string n) {
      Contract.Requires(n != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      if (fieldConstants.TryGetValue(n, out var cc)) {
        Contract.Assert(cc != null);
      } else {
        cc = new Bpl.Constant(Token.NoToken, new Bpl.TypedIdent(Token.NoToken, "field$" + n, predef.NameFamilyType), true);
        fieldConstants.Add(n, cc);
      }
      return cc;
    }

    Bpl.Constant GetField(Field f) {
      Contract.Requires(f != null && f.IsMutable);
      Contract.Requires(sink != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      Contract.Assert(VisibleInScope(f));

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
        AddOtherDefinition(fc, ax);
      }
      return fc;
    }


    Bpl.Function GetReadonlyField(Field f) {
      Contract.Requires(f != null && !f.IsMutable);
      Contract.Requires(sink != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.Function>() != null);

      Contract.Assert(VisibleInScope(f));

      Bpl.Function ff;
      if (fieldFunctions.TryGetValue(f, out ff)) {
        Contract.Assert(ff != null);
      } else {
        // Here are some built-in functions defined in "predef" (so there's no need to cache them in "fieldFunctions")
        if (f.EnclosingClass is ArrayClassDecl && f.Name == "Length") {
          return predef.ArrayLength;
        } else if (f.EnclosingClass is ValuetypeDecl { Name: "real" } && f.Name == "Floor") {
          return predef.RealFloor;
        } else if (f is SpecialField && !(f is DatatypeDestructor || f.EnclosingClass is TopLevelDeclWithMembers and not ValuetypeDecl)) {
          if (f.Name is "Keys" or "Values" or "Items") {
            var fType = f.Type.NormalizeExpand();
            Contract.Assert(fType is SetType);
            var setType = (SetType)fType;
            return f.Name switch {
              "Keys" => setType.Finite ? predef.MapDomain : predef.IMapDomain,
              "Values" => setType.Finite ? predef.MapValues : predef.IMapValues,
              _ => setType.Finite ? predef.MapItems : predef.IMapItems
            };
          }
          if (f.Name == "IsLimit") {
            return predef.ORDINAL_IsLimit;
          } else if (f.Name == "IsSucc") {
            return predef.ORDINAL_IsSucc;
          } else if (f.Name == "Offset") {
            return predef.ORDINAL_Offset;
          } else if (f.Name == "IsNat") {
            return predef.ORDINAL_IsNat;
          }
        } else if (f.FullSanitizedName == "_System.Tuple2._0") {
          return predef.Tuple2Destructors0;
        } else if (f.FullSanitizedName == "_System.Tuple2._1") {
          return predef.Tuple2Destructors1;
        }

        // Create a new function
        // function f(Ref): ty;
        List<Variable> formals = new List<Variable>();
        if (f is ConstantField) {
          formals.AddRange(MkTyParamFormals(GetTypeParams(f.EnclosingClass), false));
        }
        if (!f.IsStatic) {
          var udt = UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass);
          Bpl.Type receiverType = TrType(udt);
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, f is ConstantField ? "this" : Bpl.TypedIdent.NoName, receiverType), true));
        }
        Bpl.Formal result = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.Type)), false);
        ff = new Bpl.Function(f.tok, f.FullSanitizedName, new List<TypeVariable>(), formals, result, null, null);

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
            var etran = new ExpressionTranslator(this, predef, NewOneHeapExpr(f.tok));
            if (!IsOpaque(cf)) {
              sink.AddTopLevelDeclaration(ff.CreateDefinitionAxiom(etran.TrExpr(cf.Rhs)));
            }
          }
          sink.AddTopLevelDeclaration(ff);

        } else if (f.EnclosingClass is ArrayClassDecl) {
          // add non-negative-range axioms for array Length fields
          // axiom (forall o: Ref :: 0 <= array.Length(o));
          Bpl.BoundVariable oVar = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "o", predef.RefType));
          Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(f.tok, oVar);
          var rhs = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o });
          Bpl.Expr body = Bpl.Expr.Le(Bpl.Expr.Literal(0), rhs);
          var trigger = BplTrigger(rhs);
          Bpl.Expr qq = new Bpl.ForallExpr(f.tok, new List<Variable> { oVar }, trigger, body);
          sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, qq));
        }
      }
      return ff;
    }

    Bpl.Expr GetField(MemberSelectExpr fse) {
      Contract.Requires(fse != null);
      Contract.Requires(fse.Member != null && fse.Member is Field && ((Field)(fse.Member)).IsMutable);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return new Bpl.IdentifierExpr(fse.tok, GetField((Field)fse.Member));
    }

    /// <summary>
    /// This method is expected to be called just once for each function in the program.
    /// </summary>
    Bpl.Function GetOrCreateFunction(Function f) {
      if (this.declarationMapping.TryGetValue(f, out var result)) {
        return result;
      }

      Contract.Requires(f != null);
      Contract.Requires(predef != null && sink != null);

      // declare the function
      Bpl.Function func;
      {
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f), false));
        if (f.IsFuelAware()) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType), true));
        }

        if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$reveal", Boogie.Type.Bool), true));
        }
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType), true));
        }
        if (f.ReadsHeap) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
        }
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f)), true));
        }
        foreach (var p in f.Formals) {
          formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
        func = new Bpl.Function(f.tok, f.FullSanitizedName, new List<Bpl.TypeVariable>(), formals, res, "function declaration for " + f.FullName);
        if (InsertChecksums) {
          InsertChecksum(f, func);
        }
        sink.AddTopLevelDeclaration(func);
      }

      // declare the corresponding canCall function
      {
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f), false));
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType), true));
        }
        if (f.ReadsHeap) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
        }
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f)), true));
        }
        foreach (var p in f.Formals) {
          formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
        var canCallF = new Bpl.Function(f.tok, f.FullSanitizedName + "#canCall", new List<Bpl.TypeVariable>(), formals, res);
        sink.AddTopLevelDeclaration(canCallF);
      }

      declarationMapping[f] = func;
      return func;
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
    ///    This means that predicate definitions inlined only for non-protected predicates.
    /// IntraModuleCall
    ///    This procedure is suitable for non-co-call intra-module callers.
    ///    This means that predicates can be inlined in the usual way.
    /// CoCall
    ///    This procedure is suitable for (intra-module) co-calls.
    ///    In these calls, some uses of greatest predicates may be replaced by
    ///    proof certificates.  Note, unless the method is a greatest lemma, there
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
    enum MethodTranslationKind { SpecWellformedness, Call, CoCall, Implementation, OverrideCheck }

    private static readonly Dictionary<MethodTranslationKind, string> kindSanitizedPrefix =
      new Dictionary<MethodTranslationKind, string>() {
        {MethodTranslationKind.SpecWellformedness, "CheckWellFormed"},
        {MethodTranslationKind.Call, "Call"},
        {MethodTranslationKind.CoCall, "CoCall"},
        {MethodTranslationKind.Implementation, "Impl"},
        {MethodTranslationKind.OverrideCheck, "OverrideCheck"},
      };

    static string MethodName(ICodeContext m, MethodTranslationKind kind) {
      Contract.Requires(m != null);
      return $"{kindSanitizedPrefix[kind]}{NameSeparator}{m.FullSanitizedName}";
    }

    private static readonly Dictionary<MethodTranslationKind, string> kindDescription =
      new Dictionary<MethodTranslationKind, string>() {
        {MethodTranslationKind.SpecWellformedness, "well-formedness"},
        {MethodTranslationKind.Call, "call"},
        {MethodTranslationKind.CoCall, "co-call"},
        {MethodTranslationKind.Implementation, "correctness"},
        {MethodTranslationKind.OverrideCheck, "override check"},
      };

    static string MethodVerboseName(string fullName, MethodTranslationKind kind) {
      Contract.Requires(fullName != null);
      return $"{fullName} ({kindDescription[kind]})";
    }

    private static void AddVerboseName(Bpl.NamedDeclaration boogieDecl, string dafnyName, MethodTranslationKind kind) {
      var verboseName = MethodVerboseName(dafnyName, kind);
      AddVerboseName(boogieDecl, verboseName);
    }

    private static void AddVerboseName(Bpl.NamedDeclaration targetDecl, string verboseName) {
      targetDecl.AddAttribute("verboseName", new object[] { verboseName });
    }

    private static CallCmd Call(IToken tok, string methodName, List<Expr> ins, List<Bpl.IdentifierExpr> outs) {
      Contract.Requires(tok != null);
      Contract.Requires(methodName != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);

      CallCmd call;
      call = new CallCmd(tok, methodName, ins, outs);
      // CLEMENT enable this: call.ErrorData = "possible violation of function precondition";
      return call;
    }

    private void GenerateMethodParameters(IToken tok, Method m, MethodTranslationKind kind, ExpressionTranslator etran, List<Variable> inParams, out List<Variable> outParams) {
      GenerateMethodParametersChoose(tok, m, kind, !m.IsStatic, true, true, etran, inParams, out outParams);
    }

    private void GenerateMethodParametersChoose(IToken tok, IMethodCodeContext m, MethodTranslationKind kind, bool includeReceiver, bool includeInParams, bool includeOutParams,
      ExpressionTranslator etran, List<Variable> inParams, out List<Variable> outParams) {
      outParams = new List<Variable>();
      // Add type parameters first, always!
      inParams.AddRange(MkTyParamFormals(GetTypeParams(m), true));
      if (includeReceiver) {
        var receiverType = m is MemberDecl ? ModuleResolver.GetReceiverType(tok, (MemberDecl)m) : ModuleResolver.GetThisType(tok, (IteratorDecl)m);
        Contract.Assert(VisibleInScope(receiverType));

        Bpl.Expr wh;
        if (m is Constructor && kind == MethodTranslationKind.Implementation) {
          var th = new Bpl.IdentifierExpr(tok, "this", TrType(receiverType));
          wh = Bpl.Expr.And(
            ReceiverNotNull(th),
            GetWhereClause(tok, th, receiverType, etran, IsAllocType.NEVERALLOC));
        } else {
          var th = new Bpl.IdentifierExpr(tok, "this", TrType(receiverType));
          wh = Bpl.Expr.And(
            ReceiverNotNull(th),
            (m is TwoStateLemma ? etran.Old : etran).GoodRef(tok, th, receiverType));
        }
        // for class constructors, the receiver is encoded as an output parameter
        Bpl.Formal thVar = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", TrType(receiverType), wh), !(m is Constructor && kind != MethodTranslationKind.SpecWellformedness));
        if (thVar.InComing) {
          inParams.Add(thVar);
        } else {
          outParams.Add(thVar);
        }
      }
      if (includeInParams) {
        foreach (Formal p in m.Ins) {
          Contract.Assert(VisibleInScope(p.Type));
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetExtendedWhereClause(p.tok,
            new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), varType),
            p.Type, p.IsOld ? etran.Old : etran, isAllocContext.Var(p));
          inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), varType, wh), true));
        }
      }
      if (includeOutParams) {
        Contract.Assume(definiteAssignmentTrackers.Count == 0);
        foreach (Formal p in m.Outs) {
          Contract.Assert(VisibleInScope(p.Type));
          Contract.Assert(!p.IsOld);  // out-parameters are never old (perhaps we want to relax this condition in the future)
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetWhereClause(p.tok,
            new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), varType),
            p.Type, etran, isAllocContext.Var(p));
          if (kind == MethodTranslationKind.Implementation) {
            var tracker = AddDefiniteAssignmentTracker(p, outParams, true, m.IsGhost);
            if (wh != null && tracker != null) {
              wh = BplImp(tracker, wh);
            }
          }
          outParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), varType, wh), false));
        }
        // tear down definite-assignment trackers
        m.Outs.ForEach(RemoveDefiniteAssignmentTracker);
        Contract.Assert(definiteAssignmentTrackers.Count == 0);

        if (kind == MethodTranslationKind.Implementation) {
          outParams.Add(new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "$_reverifyPost", Bpl.Type.Bool), false));
        }
      }
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
      public readonly string SuccessMessage;
      public readonly string Comment;


      public BoilerplateTriple(IToken tok, bool isFree, Bpl.Expr expr, string errorMessage, string successMessage, string comment) {
        Contract.Requires(tok != null);
        Contract.Requires(expr != null);
        Contract.Requires(isFree || errorMessage != null);
        this.tok = tok;
        IsFree = isFree;
        Expr = expr;
        ErrorMessage = errorMessage;
        SuccessMessage = successMessage;
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
    List<BoilerplateTriple/*!*/>/*!*/ GetTwoStateBoilerplate(IToken/*!*/ tok,
      List<FrameExpression/*!*/>/*!*/ modifiesClause, bool isGhostContext, bool canAllocate,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod) {
      Contract.Requires(tok != null);
      Contract.Requires(modifiesClause != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(etran != null);
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<BoilerplateTriple>>()));

      var boilerplate = new List<BoilerplateTriple>();
      if (!canAllocate && modifiesClause.Count == 0) {
        // plain and simple:  S1 == S2
        boilerplate.Add(new BoilerplateTriple(tok, true, Bpl.Expr.Eq(etranPre.HeapExpr, etran.HeapExpr), null, null, "frame condition"));
      } else {
        bool fieldGranularity = true;
        bool objectGranularity = !fieldGranularity;
        // the frame condition, which is free since it is checked with every heap update and call
        boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, canAllocate, FrameExpressionUse.Modifies, etranPre, etran, etranMod, objectGranularity), null, null, "frame condition: object granularity"));
        if (modifiesClause.Exists(fe => fe.FieldName != null)) {
          boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, canAllocate, FrameExpressionUse.Modifies, etranPre, etran, etranMod, fieldGranularity), null, null, "frame condition: field granularity"));
        }
        // HeapSucc(S1, S2) or HeapSuccGhost(S1, S2)
        Bpl.Expr heapSucc = HeapSucc(etranPre.HeapExpr, etran.HeapExpr, isGhostContext);
        boilerplate.Add(new BoilerplateTriple(tok, true, heapSucc, null, null, "boilerplate"));
      }
      return boilerplate;
    }

    /// <summary>
    /// There are 3 states of interest when generating a frame condition:
    ///  S0. the beginning of the method/loop, which is where the frame is interpreted
    ///  S1. the pre-state of the two-state interval
    ///  S2. the post-state of the two-state interval
    /// This method assumes that etranPre denotes S1, etran denotes S2, and that etranMod denotes S0.
    /// "use" being "Modifies" says to produce this frame condition:
    ///      if it's not in the frame, then it is unchanged
    /// "use" being "Reads" says to produce this frame condition:
    ///      if it's in the frame, then it is unchanged
    /// "use" being "Unchanged" says to produce this frame condition:
    ///      if it's in the frame, then it is unchanged,
    ///      and if it has a field designation, then furthermore 'alloc' is unchanged
    /// </summary>
    Bpl.Expr/*!*/ FrameCondition(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frame, bool canAllocate, FrameExpressionUse use,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod, bool fieldGranularity) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(cce.NonNullElements(frame));
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // read is handled in AddFrameAxiom
      //
      // if field granularity:
      // generate:
      //  (forall<alpha> o: ref, f: Field alpha :: { $Heap[o][f] }
      //      o != null
      // #if use==Modifies
      //      && old($Heap)[o][alloc]                     // include only in contexts that can allocate
      // #endif
      //      ==>
      // #if use==Modifies
      //        $Heap[o][f] == PreHeap[o][f] ||
      //        (o,f) in modifiesClause)
      // #else
      //        (o,f) in readsClause
      // #if use==Unchanged
      //        or f==alloc && there's some f' such that (o,f') in readsClause
      // #endif
      //        ==>
      //        $Heap[o][f] == PreHeap[o][f])
      // #endif
      //
      // if object granularity:
      // generate:
      //  (forall o: ref :: { $Heap[o] }
      //      o != null
      // #if use==Modifies
      //      && old($Heap)[o][alloc]                     // include only in contexts that can allocate
      // #endif
      //      ==>
      // #if use==Modifies
      //        $Heap[o] == PreHeap[o] ||
      //        o in modifiesClause)
      // #else
      //        o in readsClause
      //        ==>
      //        $Heap[o] == PreHeap[o])
      // #endif
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);

      Bpl.TypeVariable alpha;
      Bpl.Expr f;
      List<Variable> quantifiedVars;
      List<TypeVariable> typeVars;
      Bpl.Expr heapOF;
      Bpl.Expr preHeapOF;
      if (fieldGranularity) {
        alpha = new Bpl.TypeVariable(tok, "alpha");
        typeVars = new List<TypeVariable> { alpha };
        var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", predef.FieldName(tok, alpha)));
        f = new Bpl.IdentifierExpr(tok, fVar);
        quantifiedVars = new List<Variable> { oVar, fVar };
        heapOF = ReadHeap(tok, etran.HeapExpr, o, f, alpha);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f, alpha);
      } else {
        // object granularity
        typeVars = new List<TypeVariable>();
        f = null;
        quantifiedVars = new List<Variable> { oVar };
        heapOF = ReadHeap(tok, etran.HeapExpr, o);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o);
      }

      Bpl.Expr ante = Bpl.Expr.Neq(o, predef.Null);
      if (canAllocate && use == FrameExpressionUse.Modifies) {
        ante = Bpl.Expr.And(ante, etranMod.IsAlloced(tok, o));
      }
      var eq = Bpl.Expr.Eq(heapOF, preHeapOF);
      var ofInFrame = InRWClause(tok, o, f, frame, use == FrameExpressionUse.Unchanged, etranMod, null, null);
      Bpl.Expr consequent = use == FrameExpressionUse.Modifies ? Bpl.Expr.Or(eq, ofInFrame) : Bpl.Expr.Imp(ofInFrame, eq);

      var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, typeVars, quantifiedVars, null, tr, Bpl.Expr.Imp(ante, consequent));
    }

    Bpl.Expr/*!*/ FrameConditionUsingDefinedFrame(IToken/*!*/ tok, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod, Boogie.IdentifierExpr frameExpr) {
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

      Bpl.Expr heapOF = ReadHeap(tok, etran.HeapExpr, o, f, alpha);
      Bpl.Expr preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f, alpha);
      Bpl.Expr ante = Bpl.Expr.And(Bpl.Expr.Neq(o, predef.Null), etranPre.IsAlloced(tok, o));
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = Bpl.Expr.Or(consequent, Bpl.Expr.SelectTok(tok, frameExpr, o, f));

      Bpl.Trigger tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, Bpl.Expr.Imp(ante, consequent));
    }
    // ----- Type ---------------------------------------------------------------------------------
    // Translates a type into the representation Boogie type,
    // c.f. TypeToTy which translates a type to its Boogie expression
    // to be used in $Is and $IsAlloc.
    Bpl.Type TrType(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Type>() != null);

      while (true) {
        type = type.NormalizeExpand();
        if (type is TypeProxy) {
          Contract.Assume(false);  // we assume that all proxies should have been dealt with in the resolver
        }
        var d = type.AsNewtype;
        if (d == null) {
          break;
        } else {
          type = d.BaseType;  // the Boogie type to be used for the newtype is the same as for the base type
        }
      }

      if (type is BoolType) {
        return Bpl.Type.Bool;
      } else if (type is CharType) {
        return predef.CharType;
      } else if (type is IntType) {
        return Bpl.Type.Int;
      } else if (type is RealType) {
        return Bpl.Type.Real;
      } else if (type is BigOrdinalType) {
        return predef.BigOrdinalType;
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        return BplBvType(t.Width);
      } else if (type is IteratorDecl.EverIncreasingType) {
        return Bpl.Type.Int;
      } else if (type is ArrowType) {
        return predef.HandleType;
      } else if (type.IsTypeParameter || type.IsAbstractType) {
        return predef.BoxType;
      } else if (type.IsInternalTypeSynonym) {
        return predef.BoxType;
      } else if (type.IsRefType) {
        // object and class types translate to ref
        return predef.RefType;
      } else if (type is UserDefinedType { ResolvedClass: TraitDecl }) {
        // non-reference trait type
        return predef.BoxType;
      } else if (type.IsDatatype) {
        return predef.DatatypeType;
      } else if (type is SetType) {
        return predef.SetType(Token.NoToken, ((SetType)type).Finite, predef.BoxType);
      } else if (type is MultiSetType) {
        return predef.MultiSetType(Token.NoToken, predef.BoxType);
      } else if (type is MapType) {
        return predef.MapType(Token.NoToken, ((MapType)type).Finite, predef.BoxType, predef.BoxType);
      } else if (type is SeqType) {
        return predef.SeqType(Token.NoToken, predef.BoxType);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    public Bpl.Expr CondApplyBox(Bpl.IToken tok, Bpl.Expr e, Type fromType, Type toType) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (!ModeledAsBoxType(fromType) && (toType == null || ModeledAsBoxType(toType))) {
        // if "e" denotes "Unbox(E): T", then just return "E"
        var coerce = e as Bpl.NAryExpr;
        if (coerce != null && coerce.Fun is Bpl.TypeCoercion) {
          Contract.Assert(coerce.Args.Count == 1);
          Contract.Assert(Bpl.Type.Equals(((Bpl.TypeCoercion)coerce.Fun).Type, TrType(fromType))); ;
          var call = coerce.Args[0] as Bpl.NAryExpr;
          if (call != null && call.Fun is Bpl.FunctionCall) {
            var fn = (Bpl.FunctionCall)call.Fun;
            if (fn.FunctionName == "$Unbox") {
              Contract.Assert(call.Args.Count == 1);
              return call.Args[0];
            }
          }
        }
        // return "Box(e)"
        return FunctionCall(tok, BuiltinFunction.Box, null, e);
      } else {
        return e;
      }
    }

    public Bpl.Expr BoxIfNecessary(Bpl.IToken tok, Bpl.Expr e, Type fromType) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return CondApplyBox(tok, e, fromType, null);
    }

    public Bpl.Expr CondApplyUnbox(Bpl.IToken tok, Bpl.Expr e, Type fromType, Type toType) {
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
    /// KRML: The name of this method is really confusing. It seems it should be named something like UnboxUnlessInherentlyBoxed.
    /// </summary>
    public Bpl.Expr UnboxIfBoxed(Bpl.Expr e, Type t) {
      if (!ModeledAsBoxType(t)) {
        return FunctionCall(e.tok, BuiltinFunction.Unbox, TrType(t), e);
      } else {
        return e;
      }
    }

    public Boogie.Expr BoxifyForTraitParent(Bpl.IToken tok, Boogie.Expr obj, MemberDecl member, Type fromType) {
      return BoxifyForTraitParent(tok, obj, member.EnclosingClass, fromType);
    }

    public Boogie.Expr BoxifyForTraitParent(Bpl.IToken tok, Boogie.Expr obj, TopLevelDecl topLevelDecl, Type fromType) {
      if (topLevelDecl is TraitDecl { IsReferenceTypeDecl: false }) {
        return BoxIfNecessary(tok, obj, fromType);
      }
      return obj;
    }

    public static bool ModeledAsBoxType(Type t) {
      Contract.Requires(t != null);
      t = t.NormalizeExpand();
      if (t is TypeProxy) {
        // unresolved proxy
        return false;
      }
      var res = t.IsTypeParameter || (t.IsTraitType && !t.IsRefType) || t.IsAbstractType || t.IsInternalTypeSynonym;
      Contract.Assert(t.IsArrowType ? !res : true);
      return res;
    }

    // ----- Statement ----------------------------------------------------------------------------

    /// <summary>
    /// A ForceCheckToken is a token wrapper whose purpose is to hide inheritance.
    /// </summary>
    public class ForceCheckToken : TokenWrapper {
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

      public override IToken WithVal(string newVal) {
        return new ForceCheckToken(WrappedToken.WithVal(newVal));
      }
    }

    Bpl.PredicateCmd Assert(IToken tok, Bpl.Expr condition, PODesc.ProofObligationDescription description, Bpl.QKeyValue kv = null) {
      var cmd = Assert(tok, condition, description, tok, kv);
      return cmd;
    }

    Bpl.PredicateCmd Assert(IToken tok, Bpl.Expr condition, PODesc.ProofObligationDescription description, IToken refinesToken, Bpl.QKeyValue kv = null) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      Bpl.PredicateCmd cmd;
      if (assertAsAssume
          || (assertionOnlyFilter != null && !assertionOnlyFilter(tok))
          || (RefinementToken.IsInherited(refinesToken, currentModule) && (codeContext == null || !codeContext.MustReverify))) {
        // produce an assume instead
        cmd = TrAssumeCmd(tok, condition, kv);
        proofDependencies?.AddProofDependencyId(cmd, tok, new AssumedProofObligationDependency(tok, description));
      } else {
        cmd = TrAssertCmdDesc(ForceCheckToken.Unwrap(tok), condition, description, kv);
        proofDependencies?.AddProofDependencyId(cmd, tok, new ProofObligationDependency(tok, description));
      }
      return cmd;
    }

    Bpl.PredicateCmd AssertNS(IToken tok, Bpl.Expr condition, PODesc.ProofObligationDescription desc) {
      return AssertNS(tok, condition, desc, tok, null);
    }

    Bpl.PredicateCmd AssertNS(IToken tok, Bpl.Expr condition, PODesc.ProofObligationDescription desc, IToken refinesTok, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(desc != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      Bpl.PredicateCmd cmd;
      if ((assertionOnlyFilter != null && !assertionOnlyFilter(tok)) ||
          (RefinementToken.IsInherited(refinesTok, currentModule) && (codeContext == null || !codeContext.MustReverify))) {
        // produce a "skip" instead
        cmd = TrAssumeCmd(tok, Bpl.Expr.True, kv);
      } else {
        tok = ForceCheckToken.Unwrap(tok);
        var args = new List<object>();
        args.Add(Bpl.Expr.Literal(0));
        cmd = TrAssertCmdDesc(tok, condition, desc, new Bpl.QKeyValue(tok, "subsumption", args, kv));
      }

      proofDependencies?.AddProofDependencyId(cmd, tok, new ProofObligationDependency(tok, desc));
      return cmd;
    }

    Bpl.Ensures EnsuresWithDependencies(IToken tok, bool free, Expression dafnyCondition, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(dafnyCondition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var ens = Ensures(tok, free, condition, errorMessage, successMessage, comment);
      proofDependencies?.AddProofDependencyId(ens, tok, new EnsuresDependency(dafnyCondition));
      return ens;
    }

    Bpl.Ensures Ensures(IToken tok, bool free, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var unwrappedToken = ForceCheckToken.Unwrap(tok);
      Bpl.Ensures ens = new Bpl.Ensures(unwrappedToken, free, condition, comment);
      var description = new PODesc.EnsuresDescription(errorMessage, successMessage);
      ens.Description = description;
      if (!free) {
        ReportAssertion(unwrappedToken, description);
      }
      return ens;
    }

    Bpl.Requires RequiresWithDependencies(IToken tok, bool free, Expression dafnyCondition, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(dafnyCondition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var req = Requires(tok, free, condition, errorMessage, successMessage, comment);
      proofDependencies?.AddProofDependencyId(req, tok, new RequiresDependency(dafnyCondition));
      return req;
    }

    Bpl.Requires Requires(IToken tok, bool free, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.Requires>() != null);
      Bpl.Requires req = new Bpl.Requires(ForceCheckToken.Unwrap(tok), free, condition, comment);
      req.Description = new PODesc.RequiresDescription(errorMessage, successMessage);
      return req;
    }

    Bpl.StmtList TrStmt2StmtList(BoogieStmtListBuilder builder, Statement block, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(builder != null);
      Contract.Requires(block != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
      Contract.Ensures(Contract.Result<Bpl.StmtList>() != null);

      TrStmt(block, builder, locals, etran);
      return builder.Collect(block.Tok);  // TODO: would be nice to have an end-curly location for "block"
    }

    /// <summary>
    /// Add to "builder" the following:
    ///     if (*) { S ; assume false; }
    /// where "S" is the given "builderToCollect".  This method consumes what has been built up in "builderToCollect".
    /// </summary>
    void PathAsideBlock(IToken tok, BoogieStmtListBuilder builderToCollect, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(builderToCollect != null);
      Contract.Requires(builderToCollect != null);

      builderToCollect.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.False));
      var ifCmd = new Bpl.IfCmd(tok, null, builderToCollect.Collect(tok), null, null);
      builder.Add(ifCmd);
    }

    (string, string) CustomErrorMessage(Attributes attrs) {
      if (attrs == null) { return (null, null); }
      List<Expression> args = Attributes.FindExpressions(attrs, "error");
      if (args == null) { return (null, null); }
      if (args.Count > 0) {
        var lErr = (string)(args[0] as StringLiteralExpr)?.Value;
        var lSucc = args.Count > 1 ? (string)(args[1] as StringLiteralExpr).Value : null;
        return (lErr, lSucc);
      } else {
        return (null, null);
      }
    }

    /// <summary>
    /// Generates a Boogie expression "lo <= x <= hi", but leaving the lo/hi bound if null.
    /// </summary>
    private static Bpl.Expr ForLoopBounds(Bpl.Expr x, Bpl.Expr/*?*/ lo, Bpl.Expr/*?*/ hi) {
      Bpl.Expr r = Bpl.Expr.True;
      if (lo != null) {
        r = BplAnd(r, Bpl.Expr.Le(lo, x));
      }
      if (hi != null) {
        r = BplAnd(r, Bpl.Expr.Le(x, hi));
      }
      return r;
    }

    delegate Bpl.Expr ExpressionConverter(Dictionary<IVariable, Expression> substMap, ExpressionTranslator etran);

    // Note: not trying to reduce duplication between this and TrAssertCmdDesc because this one should ultimately be removed.
    Bpl.AssertCmd TrAssertCmd(IToken tok, Bpl.Expr expr, Bpl.QKeyValue attributes = null) {
      // TODO: move the following comment once this method disappears

      // It may be that "expr" is a Lit expression. It might seem we don't need a Lit expression
      // around the boolean expression that is being asserted. However, we keep it. For one,
      // it doesn't change the semantics of the assert command. More importantly, leaving
      // a Lit around the expression is useful to avoid sending an "assert false;" to Boogie--since
      // Boogie looks especially for "assert false;" commands and processes them in such a way
      // that loops no longer are loops (which is confusing for Dafny users).
      return attributes == null ? new Bpl.AssertCmd(tok, expr) : new Bpl.AssertCmd(tok, expr, attributes);
    }

    Bpl.AssertCmd TrAssertCmdDesc(IToken tok, Bpl.Expr expr, PODesc.ProofObligationDescription description, Bpl.QKeyValue attributes = null) {
      ReportAssertion(tok, description);
      return new Bpl.AssertCmd(tok, expr, description, attributes);
    }

    private ISet<(Uri, int)> reportedAssertions = new HashSet<(Uri, int)>();
    private void ReportAssertion(IToken tok, PODesc.ProofObligationDescription description) {
      if (!reportedAssertions.Add((tok.Uri, tok.pos))) {
        return;
      }

      if (options.Get(CommonOptionBag.ShowAssertions) > CommonOptionBag.AssertionShowMode.None && description.IsImplicit) {
        reporter.Info(MessageSource.Translator, ToDafnyToken(false, tok), "Implicit assertion: " + description.ShortDescription, "isAssertion");
      } else if (options.Get(CommonOptionBag.ShowAssertions) == CommonOptionBag.AssertionShowMode.All) {
        reporter.Info(MessageSource.Translator, ToDafnyToken(false, tok), "Explicit assertion: " + description.ShortDescription, "isAssertion");
      }
    }

    delegate void BodyTranslator(BoogieStmtListBuilder builder, ExpressionTranslator etr);

    List<Bpl.Expr> trTypeArgs(Dictionary<TypeParameter, Type> tySubst, List<TypeParameter> tyArgs) {
      var res = new List<Bpl.Expr>();
      foreach (var p in tyArgs) {
        res.Add(TypeToTy(tySubst[p]));
      }
      return res;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, out Bpl.Expr typeAntecedent,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
      string nameSuffix = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.ValueAtReturn(out typeAntecedent) != null);

      typeAntecedent = Bpl.Expr.True;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (BoundVar bv in boundVars) {
        LocalVariable local = new LocalVariable(bv.RangeToken, nameSuffix == null ? bv.Name : bv.Name + nameSuffix, bv.Type, bv.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(bv, ie);
        Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type)));
        locals.Add(bvar);
        var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
        builder.Add(new Bpl.HavocCmd(bv.tok, new List<Bpl.IdentifierExpr> { bIe }));
        Bpl.Expr wh = GetWhereClause(bv.tok, bIe, local.Type, etran, IsAllocType.ISALLOC);
        if (wh != null) {
          typeAntecedent = BplAnd(typeAntecedent, wh);
        }
      }
      return substMap;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, BoogieStmtListBuilder builder,
      List<Variable> locals, ExpressionTranslator etran,
      string nameSuffix = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var substMap = SetupBoundVarsAsLocals(boundVars, out var typeAntecedent, builder, locals, etran, nameSuffix);
      builder.Add(TrAssumeCmd(typeAntecedent.tok, typeAntecedent));
      return substMap;
    }

    /// <summary>
    /// Clone Dafny variable "v" into a new Dafny local variable "l".
    /// Add to "substMap" the substitution from "v" to an IdentifierExpr for "l".
    /// Also, generate a Boogie variable "bvar" for "l", add "bvar" to "locals", and
    /// emit to "builder" a havoc statement for "bvar". The type antecedent for "bvar"
    /// is NOT emitted; rather, it is returned by this method.
    /// </summary>
    Bpl.Expr SetupVariableAsLocal(IVariable v, Dictionary<IVariable, Expression> substMap,
      BoogieStmtListBuilder builder, List<Bpl.Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(v != null);
      Contract.Requires(substMap != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var local = new LocalVariable(v.RangeToken, v.Name, v.Type, v.IsGhost);
      local.type = local.OptionalType;  // resolve local here
      var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
      ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
      substMap.Add(v, ie);

      var bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type)));
      locals.Add(bvar);
      var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
      builder.Add(new Bpl.HavocCmd(v.Tok, new List<Bpl.IdentifierExpr> { bIe }));
      var wh = GetWhereClause(v.Tok, bIe, local.Type, etran, ISALLOC);
      return wh ?? Bpl.Expr.True;
    }

    List<Bpl.Expr> RecordDecreasesValue(List<Expression> decreases, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, string varPrefix) {
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(varPrefix != null);
      Contract.Requires(builder != null);
      Contract.Requires(decreases != null);
      List<Bpl.Expr> oldBfs = new List<Bpl.Expr>();
      var idGen = new FreshIdGenerator();
      foreach (Expression e in decreases) {
        Contract.Assert(e != null);
        Bpl.LocalVariable bfVar = new Bpl.LocalVariable(e.tok, new Bpl.TypedIdent(e.tok, idGen.FreshId(varPrefix), TrType(cce.NonNull(e.Type))));
        locals.Add(bfVar);
        Bpl.IdentifierExpr bf = new Bpl.IdentifierExpr(e.tok, bfVar);
        oldBfs.Add(bf);
        // record value of each decreases expression at beginning of the loop iteration
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(e.tok, bf, etran.TrExpr(e));
        builder.Add(cmd);
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
                              Expression receiverReplacement, Dictionary<IVariable, Expression> substMap,
                              Dictionary<TypeParameter, Type> typeMap,
                              ExpressionTranslator etranCurrent, ExpressionTranslator etranInitial, BoogieStmtListBuilder builder, bool inferredDecreases, string hint) {
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
        Expression e0 = Substitute(calleeDecreases[i], receiverReplacement, substMap, typeMap);
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
      builder.Add(Assert(tok, decrExpr, new PODesc.Terminates(inferredDecreases, false, hint)));
    }

    /// <summary>
    /// Returns the expression that says whether or not the decreases function has gone down (if !allowNoChange)
    /// or has gone down or stayed the same (if allowNoChange).
    /// ee0 represents the new values and ee1 represents old values.
    /// If builder is non-null, then the check '0 ATMOST decr' is generated to builder.
    /// Requires all types in types0 and types1 to be non-proxy non-synonym types (that is, callers should invoke NormalizeExpand)
    /// </summary>
    Bpl.Expr DecreasesCheck(List<IToken> toks, List<Type> types0, List<Type> types1, List<Bpl.Expr> ee0, List<Bpl.Expr> ee1,
                            BoogieStmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound) {
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

      // compute eq and less for each component of the lexicographic tuple
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
          if (types0[k].IsNumericBased(Type.NumericPersuasion.Int)) {
            zero = Bpl.Expr.Literal(0);
            zeroStr = "0";
          } else if (types0[k].IsNumericBased(Type.NumericPersuasion.Real)) {
            zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
            zeroStr = "0.0";
          }
          if (zero != null) {
            Bpl.Expr bounded = Bpl.Expr.Le(zero, ee1[k]);
            for (int i = 0; i < k; i++) {
              bounded = Bpl.Expr.Or(bounded, Less[i]);
            }
            Bpl.Cmd cmd = Assert(toks[k], Bpl.Expr.Or(bounded, Eq[k]), new PODesc.DecreasesBoundedBelow(N, k, zeroStr, suffixMsg));
            builder.Add(cmd);
          }
        }
      }
      // check: ee0 < ee1 (or ee0 <= ee1, if allowNoChange)
      Bpl.Expr decrCheck = allowNoChange ? Bpl.Expr.True : Bpl.Expr.False;
      for (int i = N; 0 <= --i;) {
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
      } else if (t is CharType) {
        return u is CharType;
      } else if (t.IsNumericBased(Type.NumericPersuasion.Int)) {
        // we can allow different kinds of int-based types
        return u.IsNumericBased(Type.NumericPersuasion.Int);
      } else if (t.IsNumericBased(Type.NumericPersuasion.Real)) {
        // we can allow different kinds of real-based types
        return u.IsNumericBased(Type.NumericPersuasion.Real);
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
        return u is MapType && ((MapType)t).Finite == ((MapType)u).Finite;
      } else if (t is ArrowType) {
        return u is ArrowType;
      } else if (t is BitvectorType) {
        return u is BitvectorType;
      } else if (t is BigOrdinalType) {
        return u is BigOrdinalType;
      } else {
        Contract.Assert(t.IsTypeParameter || t.IsAbstractType || t.IsInternalTypeSynonym);
        return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
      }
    }

    Nullable<BuiltinFunction> RankFunction(Type/*!*/ ty) {
      Contract.Requires(ty != null);
      if (ty is SeqType) {
        return BuiltinFunction.SeqRank;
      } else if (ty.IsIndDatatype) {
        return BuiltinFunction.DtRank;
      } else {
        return null;
      }
    }

    void ComputeLessEq(IToken tok, Type ty0, Type ty1, Bpl.Expr e0, Bpl.Expr e1, out Bpl.Expr less, out Bpl.Expr atmost, out Bpl.Expr eq, bool includeLowerBound) {
      Contract.Requires(tok != null);
      Contract.Requires(ty0 != null);
      Contract.Requires(ty1 != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ValueAtReturn(out less) != null);
      Contract.Ensures(Contract.ValueAtReturn(out atmost) != null);
      Contract.Ensures(Contract.ValueAtReturn(out eq) != null);

      ty0 = ty0.NormalizeExpand();
      ty1 = ty1.NormalizeExpand();
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
      } else if (ty0 is CharType) {
        eq = Bpl.Expr.Eq(e0, e1);
        var operand0 = FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, e0);
        var operand1 = FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, e1);
        less = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Lt, operand0, operand1);
        atmost = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Le, operand0, operand1);
      } else if (ty0.IsNumericBased(Type.NumericPersuasion.Int) || ty0 is SeqType || ty0.IsDatatype) {
        Bpl.Expr b0, b1;
        if (ty0.IsNumericBased(Type.NumericPersuasion.Int)) {
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
        if (ty0.IsNumericBased(Type.NumericPersuasion.Int) && includeLowerBound) {
          less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), less);
          atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), b0), atmost);
        }

      } else if (ty0.IsNumericBased(Type.NumericPersuasion.Real)) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.Le(e0, Bpl.Expr.Sub(e1, Bpl.Expr.Literal(BaseTypes.BigDec.FromInt(1))));
        atmost = Bpl.Expr.Le(e0, e1);
        if (includeLowerBound) {
          less = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), less);
          atmost = Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(BaseTypes.BigDec.ZERO), e0), atmost);
        }

      } else if (ty0 is IteratorDecl.EverIncreasingType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.Gt(e0, e1);
        atmost = Bpl.Expr.Ge(e0, e1);

      } else if ((ty0 is SetType && ((SetType)ty0).Finite) || (ty0 is MapType && ((MapType)ty0).Finite)) {
        Bpl.Expr b0, b1;
        if (ty0 is SetType) {
          b0 = e0;
          b1 = e1;
        } else {
          // for maps, compare their domains as sets
          b0 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType(tok, true, predef.BoxType, predef.BoxType), e0);
          b1 = FunctionCall(tok, BuiltinFunction.MapDomain, predef.MapType(tok, true, predef.BoxType, predef.BoxType), e1);
        }
        eq = FunctionCall(tok, BuiltinFunction.SetEqual, null, b0, b1);
        less = ProperSubset(tok, b0, b1);
        atmost = FunctionCall(tok, BuiltinFunction.SetSubset, null, b0, b1);

      } else if (ty0 is SetType || ty0 is MapType) {
        Bpl.Expr b0, b1;
        if (ty0 is SetType) {
          Contract.Assert(!((SetType)ty0).Finite);
          b0 = e0;
          b1 = e1;
        } else {
          Contract.Assert(!((MapType)ty0).Finite);
          // for maps, compare their domains as sets
          b0 = FunctionCall(tok, BuiltinFunction.IMapDomain, predef.MapType(tok, false, predef.BoxType, predef.BoxType), e0);
          b1 = FunctionCall(tok, BuiltinFunction.IMapDomain, predef.MapType(tok, false, predef.BoxType, predef.BoxType), e1);
        }
        eq = FunctionCall(tok, BuiltinFunction.ISetEqual, null, b0, b1);
        less = Bpl.Expr.False;
        atmost = BplOr(less, eq);

      } else if (ty0 is MultiSetType) {
        eq = FunctionCall(tok, BuiltinFunction.MultiSetEqual, null, e0, e1);
        less = ProperMultiset(tok, e0, e1);
        atmost = FunctionCall(tok, BuiltinFunction.MultiSetSubset, null, e0, e1);

      } else if (ty0 is ArrowType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.False;  // TODO: try to do better than this
        atmost = BplOr(less, eq);

      } else if (ty0 is BitvectorType) {
        BitvectorType bv = (BitvectorType)ty0;
        eq = Bpl.Expr.Eq(e0, e1);
        less = FunctionCall(tok, "lt_bv" + bv.Width, Bpl.Type.Bool, e0, e1);
        atmost = FunctionCall(tok, "le_bv" + bv.Width, Bpl.Type.Bool, e0, e1);

      } else if (ty0 is BigOrdinalType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, e0, e1);
        atmost = BplOr(eq, less);

      } else if (ty0.IsTypeParameter || ty0.IsAbstractType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = Bpl.Expr.False;
        atmost = BplOr(less, eq);

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

    void AddComment(BoogieStmtListBuilder builder, Statement stmt, string comment) {
      Contract.Requires(builder != null);
      Contract.Requires(stmt != null);
      Contract.Requires(comment != null);
      builder.Add(new Bpl.CommentCmd(string.Format("----- {0} ----- {1}({2},{3})", comment, stmt.Tok.Filepath, stmt.Tok.line, stmt.Tok.col)));
    }

    /// <summary>
    /// Therefore, these properties are applied to method in-parameters.
    /// For now, this only allows you to case split on incoming data type values.
    /// This used to add IsGood[Multi]Set_Extendend, but that is always
    /// added for sets & multisets now in the prelude.
    /// </summary>
    Bpl.Expr GetExtendedWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran, IsAllocType alloc) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      var r = GetWhereClause(tok, x, type, etran, alloc);
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

      type = type.NormalizeExpandKeepConstraints();

      if (type.IsTypeParameter) {
        var udt = (UserDefinedType)type;
        return TrTypeParameter((TypeParameter)udt.ResolvedClass);
      } else if (type.IsAbstractType) {
        var udt = (UserDefinedType)type;
        return TrAbstractType((AbstractTypeDecl)udt.ResolvedClass, udt.TypeArgs);
      } else if (type is UserDefinedType) {
        // Classes, (co-)datatypes, newtypes, subset types, ...
        var args = type.TypeArgs.ConvertAll(TypeToTy);
        return ClassTyCon(((UserDefinedType)type), args);
      } else if (type is SetType) {
        bool finite = ((SetType)type).Finite;
        return FunctionCall(Token.NoToken, finite ? "TSet" : "TISet", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MultiSetType) {
        return FunctionCall(Token.NoToken, "TMultiSet", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is SeqType) {
        return FunctionCall(Token.NoToken, "TSeq", predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MapType) {
        bool finite = ((MapType)type).Finite;
        return FunctionCall(Token.NoToken, finite ? "TMap" : "TIMap", predef.Ty,
          TypeToTy(((MapType)type).Domain),
          TypeToTy(((MapType)type).Range));
      } else if (type is BoolType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TBool", predef.Ty);
      } else if (type is CharType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TChar", predef.Ty);
      } else if (type is RealType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TReal", predef.Ty);
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        return FunctionCall(Token.NoToken, "TBitvector", predef.Ty, Bpl.Expr.Literal(t.Width));
      } else if (type is IntType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TInt", predef.Ty);
      } else if (type is BigOrdinalType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TORDINAL", predef.Ty);
      } else if (type is ParamTypeProxy) {
        return TrTypeParameter(((ParamTypeProxy)type).orig);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    static string NameTypeParam(TypeParameter tp) {
      if (tp.Parent != null) {
        return tp.Parent.FullName + "$" + tp.Name;
      } else {
        // This happens for builtins, like arrays, that don't have a parent
        return "#$" + tp.Name;
      }
    }

    Bpl.Expr TrTypeParameter(TypeParameter tp) {
      var nm = NameTypeParam(tp);
      // return an identifier denoting a constant
      return new Bpl.IdentifierExpr(tp.tok, nm, predef.Ty);
    }

    Bpl.Expr TrAbstractType(AbstractTypeDecl abstractType, List<Type> tyArguments) {
      Contract.Requires(tyArguments != null);

      var fn = GetOrCreateTypeConstructor(abstractType);
      var args = tyArguments.ConvertAll(TypeToTy);
      return FunctionCall(abstractType.tok, fn.Name, predef.Ty, args);
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
      Contract.Requires(d is ClassLikeDecl || d is DatatypeDecl || d is NewtypeDecl || d is ValuetypeDecl);
      return d.TypeArgs;
    }

    static List<TypeParameter> GetTypeParams(Function f) {
      if (f.EnclosingClass == null) {
        return f.TypeArgs;
      } else {
        return Concat(GetTypeParams(f.EnclosingClass), f.TypeArgs);
      }
    }

    /// <summary>
    /// Return $IsBox(x, t).
    /// </summary>
    Bpl.Expr MkIsBox(Bpl.Expr x, Type t) {
      return MkIs(x, TypeToTy(t), true);
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
    Bpl.Expr MkIsAlloc(Bpl.Expr x, Type t, Bpl.Expr h) {
      return MkIsAlloc(x, TypeToTy(t), h, ModeledAsBoxType(t));
    }

    Bpl.Expr MkIsAllocBox(Bpl.Expr x, Type t, Bpl.Expr h) {
      return MkIsAlloc(x, TypeToTy(t), h, true);
    }

    Bpl.Expr MkIsAlloc(Bpl.Expr x, Bpl.Expr t, Bpl.Expr h, bool box = false) {
      if (box) {
        return FunctionCall(x.tok, BuiltinFunction.IsAllocBox, null, x, t, h);
      } else {
        return FunctionCall(x.tok, BuiltinFunction.IsAlloc, null, x, t, h);
      }
    }

    /// <summary>
    /// A "where" clause for a variable in Boogie turns into an assumption anytime that Boogie is tasked
    /// with assigning an arbitrary value to that variable. This happens at the beginning of a procedure
    /// implementation, after a procedure call, or as part of a "havoc" command. Each one of these can
    /// easily be followed by a manual "assume" command. However, the use-case that makes "where" clauses
    /// especially valuable is in loops, because when Boogie cuts the backedge, it inserts "havoc" commands.
    /// To do this in Dafny, Dafny would have to compute loop targets, which is better done in Boogie (which
    /// already has to do it).
    /// </summary>
    Bpl.Expr GetWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran, IsAllocType alloc,
      bool allocatednessOnly = false, bool alwaysUseSymbolicName = false) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      if (type.NormalizeExpand() is TypeProxy) {
        // Unresolved proxy
        // Omit where clause (in other places, unresolved proxies are treated as a reference type; we could do that here too, but
        // we might as well leave out the where clause altogether).
        return null;
      }

      var normType = type.NormalizeExpandKeepConstraints();
      Bpl.Expr isAlloc;
      if (type.IsNumericBased() || type.IsBitVectorType || type.IsBoolType || type.IsCharType || type.IsBigOrdinalType) {
        isAlloc = null;
      } else if (alloc == ISALLOC && etran.HeapExpr != null) {
        isAlloc = MkIsAlloc(x, normType, etran.HeapExpr);
      } else {
        isAlloc = null;
      }
      if (allocatednessOnly) {
        return isAlloc;
      }

      Bpl.Expr isPred = null;
      if (alwaysUseSymbolicName) {
        // go for the symbolic name
        isPred = MkIs(x, normType);
      } else if (normType is BoolType || normType is IntType || normType is RealType || normType is BigOrdinalType) {
        // nothing to do
      } else if (normType is BitvectorType) {
        var t = (BitvectorType)normType;
        if (t.Width == 0) {
          // type bv0 has only one value
          return Bpl.Expr.Eq(BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, t), x);
        }
      } else if ((normType.AsTypeSynonym != null || normType.AsNewtype != null) &&
        (normType.IsNumericBased() || normType.IsBitVectorType || normType.IsBoolType)) {
        var constraint = ModuleResolver.GetImpliedTypeConstraint(new BoogieWrapper(x, normType), normType);
        isPred = etran.TrExpr(constraint);
      } else {
        // go for the symbolic name
        isPred = MkIs(x, normType);
      }
      return isAlloc == null ? isPred : isPred == null ? isAlloc : BplAnd(isPred, isAlloc);
    }

    // Returns an expression, which, if false, means that the two LHS expressions are
    // not distinct; if null then the LHSs are trivially distinct
    Bpl.Expr CheckDistinctness(Expression lhsa, Expression lhsb, ExpressionTranslator etran) {
      {
        if (lhsa is IdentifierExpr iea && lhsb is IdentifierExpr ieb) {
          if (iea.Name != ieb.Name) {
            return null;
          }

          return Bpl.Expr.False;
        }
      }
      {
        if (lhsa is MemberSelectExpr iea && lhsb is MemberSelectExpr ieb) {
          if (iea.Member is Field fa && ieb.Member is Field fb) {
            if (fa != fb) {
              return null;
            }

            return Bpl.Expr.Neq(etran.TrExpr(iea.Obj), etran.TrExpr(ieb.Obj));
          }
        }
      }
      {
        if (lhsa is SeqSelectExpr iea && lhsb is SeqSelectExpr ieb) {
          Bpl.Expr ex = Bpl.Expr.Neq(etran.TrExpr(iea.Seq), etran.TrExpr(ieb.Seq));
          if (iea.E1 == null && ieb.E1 == null) {
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Neq(etran.TrExpr(iea.E0), etran.TrExpr(ieb.E0)));
          } else if (iea.E1 == null && ieb.E1 != null) {
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Le(etran.TrExpr(ieb.E1), etran.TrExpr(iea.E0)));
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Lt(etran.TrExpr(iea.E0), etran.TrExpr(ieb.E0)));
          } else if (iea.E1 != null && ieb.E1 == null) {
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Le(etran.TrExpr(iea.E1), etran.TrExpr(ieb.E0)));
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Lt(etran.TrExpr(ieb.E0), etran.TrExpr(iea.E0)));
          } else {
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Le(etran.TrExpr(iea.E1), etran.TrExpr(ieb.E0)));
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Le(etran.TrExpr(ieb.E1), etran.TrExpr(iea.E0)));
          }
          return ex;
        }
      }
      {
        if (lhsa is MultiSelectExpr iea && lhsb is MultiSelectExpr ieb && iea.Indices.Count == ieb.Indices.Count) {
          Bpl.Expr ex = Bpl.Expr.Neq(etran.TrExpr(iea.Array), etran.TrExpr(ieb.Array));
          for (int i = 0; i < iea.Indices.Count; i++) {
            ex = Bpl.Expr.Or(ex, Bpl.Expr.Neq(etran.TrExpr(iea.Indices[i]), etran.TrExpr(ieb.Indices[i])));
          }
          return ex;
        }
      }

      return null;
    }

    /// <summary>
    /// Returns the name of the local variable used as a stand-in for a field in the BodyInit part of a divided
    /// constructor body.
    /// </summary>
    string SurrogateName(Field field) {
      Contract.Requires(field != null);
      return "this." + field.Name;
    }

    Bpl.Expr GetSubrangeCheck(Bpl.Expr bSource, Type sourceType, Type targetType, out PODesc.ProofObligationDescription desc, string errorMessagePrefix = "") {
      Contract.Requires(bSource != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(targetType != null);

      if (Type.IsSupertype(targetType, sourceType) && !(sourceType.IsRefType && !sourceType.IsNonNullRefType && !targetType.IsRefType)) {
        // We should always be able to use Is, but this is an optimisation.
        desc = null;
        return null;
      }
      targetType = targetType.NormalizeExpandKeepConstraints();
      var udt = targetType as UserDefinedType;
      Bpl.Expr cre;
      if (udt?.ResolvedClass is RedirectingTypeDecl redirectingTypeDecl &&
          ModeledAsBoxType((redirectingTypeDecl as NewtypeDecl)?.BaseType ?? redirectingTypeDecl.Var.Type)) {
        cre = MkIs(BoxIfNecessary(bSource.tok, bSource, sourceType), TypeToTy(targetType), true);
      } else if (ModeledAsBoxType(sourceType)) {
        cre = MkIs(bSource, TypeToTy(targetType), true);
      } else if (targetType is UserDefinedType targetUdt) {
        cre = MkIs(BoxifyForTraitParent(bSource.tok, bSource, udt.ResolvedClass, sourceType), targetType);
      } else {
        cre = MkIs(bSource, targetType);
      }
      if (udt != null && udt.IsRefType) {
        var s = sourceType.NormalizeExpandKeepConstraints();
        var certain = false;
        string cause = null;
        if (s is UserDefinedType sudt && udt.ResolvedClass is NonNullTypeDecl nntd && nntd.Class == sudt.ResolvedClass) {
          certain = udt.ResolvedClass.TypeArgs.Count == 0;
          cause = "it may be null";
        }
        desc = new PODesc.SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), false, certain, cause);
      } else if (udt != null && ArrowType.IsTotalArrowTypeName(udt.Name)) {
        desc = new PODesc.SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), true, false,
          "it may be partial or have read effects");
      } else if (udt != null && ArrowType.IsPartialArrowTypeName(udt.Name)) {
        desc = new PODesc.SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), true, false,
          "it may have read effects");
      } else {
        desc = new PODesc.SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(),
          targetType.NormalizeExpandKeepConstraints() is UserDefinedType
          {
            ResolvedClass: SubsetTypeDecl or NewtypeDecl { Var: { } }
          },
          false, null);
      }
      return cre;
    }

    void CheckSubrange(IToken tok, Bpl.Expr bSource, Type sourceType, Type targetType, BoogieStmtListBuilder builder, string errorMsgPrefix = "") {
      Contract.Requires(tok != null);
      Contract.Requires(bSource != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(targetType != null);
      Contract.Requires(builder != null);

      var cre = GetSubrangeCheck(bSource, sourceType, targetType, out var desc, errorMsgPrefix);
      if (cre != null) {
        builder.Add(Assert(tok, cre, desc));
      }
    }

    void Check_NewRestrictions(IToken tok, Bpl.Expr obj, Field f, Bpl.Expr rhs, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
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
        var subset = FunctionCall(tok, BuiltinFunction.SetSubset, null, rhs, ReadHeap(tok, etran.HeapExpr, obj, fId, TrType(f.Type)));
        builder.Add(Assert(tok, subset, new PODesc.AssignmentShrinks(f.Name)));
      }
    }

    Bpl.AssumeCmd AssumeGoodHeap(IToken tok, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<AssumeCmd>() != null);

      return TrAssumeCmd(tok, FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr));
    }

    /// <summary>
    /// Idempotently fills in "mc.ProjectionFunctions"
    /// </summary>
    void CreateMapComprehensionProjectionFunctions(MapComprehension mc) {
      Contract.Requires(mc != null && mc.TermLeft != null);
      if (mc.ProjectionFunctions == null) {
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator(string.Format("map$project${0}#", projectionFunctionCount));
        projectionFunctionCount++;
        mc.ProjectionFunctions = new List<Bpl.Function>();
        foreach (var bv in mc.BoundVars) {
          var arg = BplFormalVar(null, TrType(mc.TermLeft.Type), false);
          var res = BplFormalVar(null, TrType(bv.Type), true);
          var projectFn = new Bpl.Function(mc.tok, varNameGen.FreshId(string.Format("#{0}#", bv.Name)), new List<Variable>() { arg }, res);
          mc.ProjectionFunctions.Add(projectFn);
          sink.AddTopLevelDeclaration(projectFn);
        }
      }
    }

    int projectionFunctionCount = 0;

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
    private Declaration currentDeclaration;

    // ----- Expression ---------------------------------------------------------------------------

    /// <summary>
    /// This class gives a way to represent a Boogie translation target as if it were still a Dafny expression.
    /// </summary>
    internal class BoogieWrapper : Expression {
      public readonly Bpl.Expr Expr;

      public BoogieWrapper(Bpl.Expr expr, Type dafnyType)
        : base(ToDafnyToken(false, expr.tok)) {
        Contract.Requires(expr != null);
        Contract.Requires(dafnyType != null);
        RangeToken = ToDafnyToken(true, expr.tok).ToRange();
        Expr = expr;
        Type = dafnyType;  // resolve immediately
      }
    }

    internal class BoogieFunctionCall : Expression {
      public readonly string FunctionName;
      public readonly bool UsesHeap;
      public readonly bool UsesOldHeap;
      public readonly List<Label> HeapAtLabels;
      public readonly List<Type> TyArgs; // Note: also has a bunch of type arguments
      public readonly List<Expression> Args;
      public BoogieFunctionCall(IToken tok, string functionName, bool usesHeap, bool usesOldHeap, List<Label> heapAtLabels, List<Expression> args, List<Type> tyArgs)
        : base(tok) {
        Contract.Requires(tok != null);
        Contract.Requires(functionName != null);
        Contract.Requires(heapAtLabels != null);
        Contract.Requires(args != null);
        FunctionName = functionName;
        UsesHeap = usesHeap;
        UsesOldHeap = usesOldHeap;
        HeapAtLabels = heapAtLabels;
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

    internal class SubstLetExpr : LetExpr {
      public LetExpr orgExpr;
      public Dictionary<IVariable, Expression> substMap;
      public Dictionary<TypeParameter, Type> typeMap;

      public SubstLetExpr(IToken tok, List<CasePattern<BoundVar>> lhss, List<Expression> rhss, Expression body, bool exact,
         LetExpr orgExpr, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap, List<ComprehensionExpr.BoundedPool>/*?*/ constraintBounds)
        : base(tok, lhss, rhss, body, exact) {
        this.orgExpr = orgExpr;
        this.substMap = substMap;
        this.typeMap = typeMap;
        this.Constraint_Bounds = constraintBounds;
      }
    }

    internal class FuelSettingPair {
      public int low;
      public int high;

      public FuelSettingPair(int low = (int)FuelSetting.FuelAmount.LOW, int high = (int)FuelSetting.FuelAmount.HIGH) {
        this.low = low;
        this.high = high;
      }
    }

    // C#'s version of a type alias
    internal class FuelContext : Dictionary<Function, FuelSettingPair> { }
    internal class CustomFuelSettings : Dictionary<Function, FuelSetting> { }

    internal class FuelConstant {
      public Function f;
      public Bpl.Expr baseFuel;
      public Bpl.Expr startFuel;
      public Bpl.Expr startFuelAssert;

      public FuelConstant(Function f, Bpl.Expr baseFuel, Bpl.Expr startFuel, Bpl.Expr startFuelAssert) {
        this.f = f;
        this.baseFuel = baseFuel;
        this.startFuel = startFuel;
        this.startFuelAssert = startFuelAssert;
      }

      public Bpl.Expr MoreFuel(Bpl.Program sink, PredefinedDecls predef, FreshIdGenerator idGen) {
        string uniqueId = idGen.FreshId("MoreFuel_" + f.FullName);
        Bpl.Constant moreFuel = new Bpl.Constant(f.tok, new Bpl.TypedIdent(f.tok, uniqueId, predef.LayerType), false);
        sink.AddTopLevelDeclaration(moreFuel);
        Bpl.Expr moreFuel_expr = new Bpl.IdentifierExpr(f.tok, moreFuel);
        return moreFuel_expr;
      }
    }

    internal class FuelSetting {

      public enum FuelAmount { NONE, LOW, HIGH };
      public static AsyncLocal<Stack<FuelContext>> SavedContexts = new();

      public static FuelSettingPair FuelAttrib(Function f, out bool found) {
        Contract.Requires(f != null);
        Contract.Ensures(Contract.Result<FuelSettingPair>() != null);
        FuelSettingPair setting = new FuelSettingPair();
        found = false;

        if (f.Attributes != null) {
          List<Expression> args = Attributes.FindExpressions(f.Attributes, "fuel");
          if (args != null) {
            found = true;
            if (args.Count >= 2) {
              LiteralExpr literalLow = args[0] as LiteralExpr;
              LiteralExpr literalHigh = args[1] as LiteralExpr;

              if (literalLow != null && literalLow.Value is BigInteger && literalHigh != null && literalHigh.Value is BigInteger) {
                setting.low = (int)((BigInteger)literalLow.Value);
                setting.high = (int)((BigInteger)literalHigh.Value);
              }
            } else if (args.Count >= 1) {
              LiteralExpr literal = args[0] as LiteralExpr;
              if (literal != null && literal.Value is BigInteger) {
                setting.low = (int)((BigInteger)literal.Value);
                setting.high = setting.low + 1;
              }
            }
          }
        }

        return setting;
      }

      public int amount;        // Amount of fuel above that represented by start
      private Bpl.Expr start;   // Starting fuel argument (null indicates LZ)
      private BoogieGenerator boogieGenerator;
      private CustomFuelSettings customFuelSettings;

      public FuelSetting(BoogieGenerator boogieGenerator, int amount, Bpl.Expr start = null, CustomFuelSettings customFuelSettings = null) {
        this.boogieGenerator = boogieGenerator;
        this.amount = amount;
        this.start = start;
        this.customFuelSettings = customFuelSettings;
      }

      public FuelSetting Offset(int offset) {
        return new FuelSetting(boogieGenerator, this.amount + offset, start);
      }

      public FuelSetting Decrease(int offset) {
        Contract.Ensures(this.amount - offset >= 0);
        return new FuelSetting(boogieGenerator, this.amount - offset, start);
      }

      public FuelSetting WithLayer(Bpl.Expr layer) {
        return new FuelSetting(boogieGenerator, amount, layer);
      }

      public FuelSetting WithContext(CustomFuelSettings settings) {
        return new FuelSetting(boogieGenerator, amount, start, settings);
      }

      public Bpl.Expr LayerZero() {
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$LZ", boogieGenerator.predef.LayerType);
      }

      public Bpl.Expr LayerN(int n) {
        Contract.Requires(0 <= n);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return boogieGenerator.LayerSucc(LayerZero(), n);
      }

      public Bpl.Expr LayerN(int n, Bpl.Expr baseLayer) {
        Contract.Requires(0 <= n);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return boogieGenerator.LayerSucc(baseLayer, n);
      }

      private Bpl.Expr ToExpr(int amount) {
        if (start == null) {
          return LayerN(amount);
        } else {
          return boogieGenerator.LayerSucc(start, amount);
        }
      }

      public Bpl.Expr ToExpr() {
        return this.ToExpr(this.amount);
      }

      /// <summary>
      /// Get the fuel value for this function, given the ambient environment (represented by the fuel setting)
      /// the function itself, and the function call's context (if any)
      /// </summary>
      public Bpl.Expr GetFunctionFuel(Function f) {
        Contract.Requires(f != null);
        Bpl.Expr finalFuel;
        if (customFuelSettings != null && customFuelSettings.ContainsKey(f)) {
          finalFuel = customFuelSettings[f].GetFunctionFuel(f);
        } else if (this.amount == (int)FuelAmount.NONE) {
          finalFuel = this.ToExpr();
        } else {
          FuelSettingPair setting = null;
          var found = boogieGenerator.fuelContext.TryGetValue(f, out setting);

          if (!found) {  // If the context doesn't define fuel for this function, check for a fuel attribute (which supplies a default value if none is found)
            setting = FuelAttrib(f, out found);
          }

          FuelConstant fuelConstant = boogieGenerator.functionFuel.Find(x => x.f == f);
          if (this.amount == (int)FuelAmount.LOW) {
            finalFuel = GetFunctionFuel(setting.low > 0 ? setting.low : this.amount, found, fuelConstant);
          } else if (this.amount >= (int)FuelAmount.HIGH) {
            finalFuel = GetFunctionFuel(setting.high > 0 ? setting.high : this.amount, found, fuelConstant);
          } else {
            Contract.Assert(false); // Should not reach here
            finalFuel = null;
          }
        }
        return finalFuel;
      }

      private Bpl.Expr GetFunctionFuel(int amount, bool hasFuel, FuelConstant fuelConstant) {
        if (fuelConstant != null) {
          /*
          if (hasFuel) {
            // it has fuel context
            return LayerN(amount, fuelConstant.baseFuel);
          } else {
           */
          // startfuel
          if (amount == (int)FuelAmount.LOW) {
            return fuelConstant.startFuel;
          } else {
            return fuelConstant.startFuelAssert;
          }
          //}
        } else {
          return ToExpr(amount);
        }
      }

      /// <summary>
      /// Finds all fuel related attributes of the form {:fuel function low [high]}
      /// Adds the setting to the context _if_ the context does not already have a setting for that function.
      /// In other words, it should be called in order from most to least specific context scope.
      /// </summary>
      public static void FindFuelAttributes(Attributes attribs, FuelContext fuelContext) {
        Function f = null;
        FuelSettingPair setting = null;

        if (attribs != null) {
          List<List<Expression>> results = Attributes.FindAllExpressions(attribs, "fuel");

          if (results != null) {
            foreach (List<Expression> args in results) {
              if (args != null && args.Count >= 2) {
                // Try to extract the function from the first argument
                MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
                if (selectExpr != null) {
                  f = selectExpr.Member as Function;
                }

                // Try to extract the lower fuel setting
                LiteralExpr literalLow = args[1] as LiteralExpr;
                if (literalLow != null && literalLow.Value is BigInteger) {
                  setting = new FuelSettingPair();
                  setting.low = (int)((BigInteger)literalLow.Value);
                }

                // The user may supply an additional high argument; if not, it defaults to low + 1
                if (f != null && args.Count >= 3) {
                  LiteralExpr literalHigh = args[2] as LiteralExpr;
                  if (setting != null && literalHigh != null && literalHigh.Value is BigInteger) {
                    setting.high = (int)((BigInteger)literalHigh.Value);
                    if (!fuelContext.ContainsKey(f)) {
                      fuelContext.Add(f, setting);
                    }
                  }
                } else if (f != null && setting != null) {
                  setting.high = setting.low + 1;
                  if (!fuelContext.ContainsKey(f)) {
                    fuelContext.Add(f, setting);
                  }
                }
              }
            }
          }
        }
      }

      /// <summary>
      /// Extend the given context with fuel information from the declaration itself, and enclosing modules
      /// </summary>
      private static void AddFuelContext(FuelContext context, TopLevelDecl decl) {
        FindFuelAttributes(decl.Attributes, context);

        var module = decl.EnclosingModuleDefinition;
        while (module != null) {
          FindFuelAttributes(module.Attributes, context);
          module = module.EnclosingModule;
        }
      }

      /// <summary>
      /// Creates a summary of all fuel settings in scope, starting from the given class declaration
      /// </summary>
      public static FuelContext NewFuelContext(TopLevelDecl decl) {
        FuelContext context = new FuelContext();
        AddFuelContext(context, decl);
        return context;
      }

      /// <summary>
      /// Creates a summary of all fuel settings in scope, starting from the given member declaration
      /// </summary>
      public static FuelContext NewFuelContext(MemberDecl decl) {
        FuelContext context = new FuelContext();

        FindFuelAttributes(decl.Attributes, context);
        AddFuelContext(context, decl.EnclosingClass);

        return context;
      }

      /// <summary>
      /// Extends the given fuel context with any new fuel settings found in attribs
      /// </summary>
      public static FuelContext ExpandFuelContext(Attributes attribs, IToken tok, FuelContext oldFuelContext, ErrorReporter reporter) {
        Contract.Ensures(GetSavedContexts().Count == Contract.OldValue(GetSavedContexts().Count) + 1);
        FuelContext newContext = new FuelContext();
        FindFuelAttributes(attribs, newContext);
        if (newContext.Count > 0) {
          // first make sure that the fuel only increase relative to the oldContext
          foreach (var pair in newContext) {
            FuelSettingPair newSetting = pair.Value;
            FuelSettingPair oldSetting;
            var found = oldFuelContext.TryGetValue(pair.Key, out oldSetting);
            if (!found) {    // the default is {:fuel, 1, 2}
              oldSetting = new FuelSettingPair();
            }
            // make sure that the fuel can only increase within a given scope
            if (newSetting.low < oldSetting.low || newSetting.high < oldSetting.high) {
              reporter.Error(MessageSource.Translator, ErrorId.g_fuel_must_increase, tok, "Fuel can only increase within a given scope.");
            }
          }
          // add oldContext to newContext if it doesn't exist already
          foreach (var pair in oldFuelContext) {
            if (!newContext.ContainsKey(pair.Key)) {    // Local setting takes precedence over old context
              newContext.Add(pair.Key, pair.Value);
            }
          }
        } else {
          newContext = oldFuelContext;
        }
        GetSavedContexts().Push(oldFuelContext);

        return newContext;
      }

      private static Stack<FuelContext> GetSavedContexts() {
        var result = SavedContexts.Value;
        if (result == null) {
          SavedContexts.Value = result = new();
        }
        return result;
      }

      public static FuelContext PopFuelContext() {
        Contract.Requires(GetSavedContexts().Count > 0);
        return GetSavedContexts().Pop();
      }

    }

    internal enum IsAllocType { ISALLOC, NOALLOC, NEVERALLOC };  // NEVERALLOC is like NOALLOC, but overrides AlwaysAlloc
    static IsAllocType ISALLOC { get { return IsAllocType.ISALLOC; } }
    static IsAllocType NOALLOC { get { return IsAllocType.NOALLOC; } }

    internal class IsAllocContext {
      private DafnyOptions options;
      internal bool allVarsGhost;

      internal IsAllocContext(DafnyOptions options, bool allVarsGhost) {
        this.options = options;
        this.allVarsGhost = allVarsGhost;
      }

      internal IsAllocType Var(bool isGhost) {
        return ISALLOC;
      }

      internal IsAllocType Var(LocalVariable local) {
        return Var(allVarsGhost || local.IsGhost);
      }

      internal IsAllocType Var(NonglobalVariable var) {
        return Var(allVarsGhost || var.IsGhost);
      }

      internal IsAllocType Var(bool ghostStmt, LocalVariable var) {
        return Var(allVarsGhost || ghostStmt || var.IsGhost);
      }

      internal IsAllocType Var(bool ghostStmt, NonglobalVariable var) {
        return Var(allVarsGhost || ghostStmt || var.IsGhost);
      }
    }

    List<SplitExprInfo/*!*/>/*!*/ TrSplitExpr(Expression expr, ExpressionTranslator etran, bool apply_induction, out bool splitHappened) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, true, apply_induction, etran);
      return splits;
    }

    List<SplitExprInfo> TrSplitExprForMethodSpec(Expression expr, ExpressionTranslator etran, MethodTranslationKind kind) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      var apply_induction = kind == MethodTranslationKind.Implementation;
      bool splitHappened;  // we don't actually care
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, kind != MethodTranslationKind.Call, apply_induction, etran);
      return splits;
    }

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IToken tok, Dictionary<IVariable, Expression> substMap = null) {
      Contract.Requires(etran != null);
      Contract.Requires(tok != null);
      var argsEtran = etran.WithNoLits();
      Bpl.Trigger tr = null;
      foreach (var trigger in attribs.AsEnumerable().Where(aa => aa.Name == "trigger").Select(aa => aa.Args)) {
        List<Bpl.Expr> tt = new List<Bpl.Expr>();
        foreach (var arg in trigger) {
          if (substMap == null) {
            tt.Add(argsEtran.TrExpr(arg));
          } else {
            tt.Add(argsEtran.TrExpr(Substitute(arg, null, substMap)));
          }
        }
        tr = new Bpl.Trigger(tok, true, tt, tr);
      }
      return tr;
    }

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IToken tok, List<Variable> bvars, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(etran != null);
      Contract.Requires(tok != null);
      var argsEtran = etran.WithNoLits();
      Bpl.Trigger tr = null;
      var fueledTrigger = new Dictionary<List<Expression>, bool>();
      // translate the triggers once to see if fuel or the heap is used as quantifier boundvar
      foreach (var aa in attribs.AsEnumerable()) {
        if (aa.Name == "trigger") {
          int fuelCount = argsEtran.Statistics_CustomLayerFunctionCount;
          foreach (var arg in aa.Args) {
            argsEtran.TrExpr(arg);
          }
          fueledTrigger[aa.Args] = argsEtran.Statistics_CustomLayerFunctionCount > fuelCount;
        }
      }

      bool useFuelAsQuantifier = argsEtran.Statistics_CustomLayerFunctionCount > 0;
      bool useHeapAsQuantifier = argsEtran.Statistics_HeapAsQuantifierCount > 0;
      if (useHeapAsQuantifier) {
        var heapExpr = BplBoundVar(CurrentIdGenerator.FreshId("tr$heap#"), predef.HeapType, bvars);
        argsEtran = new ExpressionTranslator(argsEtran, heapExpr);
      }

      // now translate it with the correct layer and heapExpr
      foreach (var trigger in attribs.AsEnumerable().Where(aa => aa.Name == "trigger")) {
        List<Bpl.Expr> tt = new List<Bpl.Expr>();
        foreach (var arg in trigger.Args) {
          if (substMap == null) {
            tt.Add(argsEtran.TrExpr(arg));
          } else {
            tt.Add(argsEtran.TrExpr(Substitute(arg, null, substMap, typeMap)));
          }
        }
        if (useHeapAsQuantifier) {
          tt.Add(FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, argsEtran.HeapExpr));
        }
        tr = new Bpl.Trigger(tok, true, tt, tr);
      }
      return tr;
    }

    private class VariablesCollector : BottomUpVisitor {
      internal ISet<IVariable> variables;

      internal VariablesCollector() {
        this.variables = new HashSet<IVariable>();
      }

      protected override void VisitOneExpr(Expression expr) {
        if (expr is IdentifierExpr) {
          variables.Add((expr as IdentifierExpr).Var);
        }
      }
    }

    bool TrSplitNeedsTokenAdjustment(Expression expr) {
      Contract.Requires(expr != null);
      return RefinementToken.IsInherited(expr.tok, currentModule) && (codeContext == null || !codeContext.MustReverify) && RefinementTransformer.ContainsChange(expr, currentModule);
    }

    /// <summary>
    /// Return a list of variables specified by the arguments of :_induction in "attributes", if any.
    /// If an argument of :_induction is a ThisExpr, "null" is returned as the corresponding variable.
    /// </summary>
    List<VarType/*?*/> ApplyInduction<VarType>(List<VarType> boundVars, Attributes attributes) where VarType : class, IVariable {
      Contract.Requires(boundVars != null);
      Contract.Ensures(Contract.Result<List<VarType>>() != null);

      var args = Attributes.FindExpressions(attributes, "_induction");
      if (args == null) {
        return new List<VarType>();  // don't apply induction
      } else {
        return args.ConvertAll(e => e is ThisExpr ? null : (VarType)((IdentifierExpr)e).Var);
      }
    }

    // No expression introduces a type variable
    static void ComputeFreeTypeVariables(Expression expr, ISet<TypeParameter> fvs) {
      ComputeFreeTypeVariables(expr.Type, fvs);
      expr.ComponentTypes.ForEach(ty => ComputeFreeTypeVariables((Type)ty, fvs));
      expr.SubExpressions.ForEach(ee => ComputeFreeTypeVariables(ee, fvs));
    }

    static void ComputeFreeTypeVariables(Type ty, ISet<TypeParameter> fvs) {
      // Add type parameters
      var tp = ty.AsTypeParameter;
      if (tp != null) {
        Contract.Assert(ty.TypeArgs.Count == 0);
        fvs.Add(tp);
      } else {
        ty.NormalizeExpandKeepConstraints().TypeArgs.ForEach(tt => ComputeFreeTypeVariables(tt, fvs));
      }
    }

    static void ComputeFreeTypeVariables_All(Type ty, ISet<TypeParameter> fvs) {
      // Add type parameters
      if (ty.IsTypeParameter) {
        fvs.Add(ty.AsTypeParameter);
      }
      ty.NormalizeExpandKeepConstraints().TypeArgs.ForEach(tt => ComputeFreeTypeVariables_All(tt, fvs));
    }

    public bool UsesHeap(Expression expr) {
      UsesHeapVisitor visitor = new UsesHeapVisitor();
      visitor.Visit(expr);
      if (visitor.foundHeap) {
        return true;
      }
      bool usesHeap = false, usesOldHeap = false;
      var FVsHeapAt = new HashSet<Label>();
      Type usesThis = null;
      FreeVariablesUtil.ComputeFreeVariables(options, expr, new HashSet<IVariable>(), ref usesHeap, ref usesOldHeap, FVsHeapAt, ref usesThis, false);
      return usesHeap || usesOldHeap || FVsHeapAt.Count != 0;
    }

    class UsesHeapVisitor : BottomUpVisitor {
      internal bool foundHeap = false;
      Type usesThis = null;
      protected override void VisitOneExpr(Expression expr) {
        LetExpr letExpr = expr as LetExpr;
        if (letExpr != null && !letExpr.Exact) {
          foundHeap = true; // see comment in LetSuchThatExprInfo: "UsesHeap = true;  // note, we ignore "usesHeap" and always record it as "true", because various type antecedents need access to the heap (hopefully, this is okay in the contexts in which the let-such-that expression is used)"
        }
        FunctionCallExpr call = expr as FunctionCallExpr;
        if (call != null && call.Function != null && call.Function.ReadsHeap) {
          foundHeap = true;
        }
        if (expr is ApplyExpr || expr is SeqConstructionExpr) {
          foundHeap = true;
        }
        ThisExpr thisExpr = expr as ThisExpr;
        if (thisExpr != null && thisExpr.Type == null) { // this shouldn't happen, but there appears to be a bug in trait resolution (see TraitCompile.dfy); it causes ComputeFreeVariables to blow up
          foundHeap = true;
        } else if (thisExpr != null && usesThis != null && !thisExpr.Type.Equals(usesThis)) { // also causes ComputeFreeVariables to blow up (see TraitExample.dfy)
          foundHeap = true;
        } else if (thisExpr != null) {
          usesThis = thisExpr.Type;
        }
      }
    }

    /// <summary>
    /// Returns an expression like "expr", but where free occurrences of "v" have been replaced by "e".
    /// </summary>
    public static Expression Substitute(Expression expr, IVariable v, Expression e) {
      Contract.Requires(expr != null);
      Contract.Requires(v != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Expression>() != null);
      var substMap = new Dictionary<IVariable, Expression>();
      substMap.Add(v, e);
      return Substitute(expr, null, substMap);
    }

    public static Expression Substitute(Expression expr, Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap,
      Dictionary<TypeParameter, Type> typeMap = null, Label oldLabel = null) {
      Contract.Requires(expr != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new Substituter(receiverReplacement, substMap, typeMap ?? new Dictionary<TypeParameter, Type>(), oldLabel);
      return s.Substitute(expr);
    }

    public static Expression InlineLet(LetExpr letExpr) {
      Contract.Requires(letExpr.LHSs.All(p => p.Var != null));
      var substMap = new Dictionary<IVariable, Expression>();
      for (var i = 0; i < letExpr.LHSs.Count; i++) {
        substMap.Add(letExpr.LHSs[i].Var, letExpr.RHSs[i]);
      }
      return BoogieGenerator.Substitute(letExpr.Body, null, substMap);
    }

    Bpl.Expr HeapSameOrSucc(Bpl.Expr oldHeap, Bpl.Expr newHeap) {
      return Bpl.Expr.Or(
        Bpl.Expr.Eq(oldHeap, newHeap),
        FunctionCall(newHeap.tok, BuiltinFunction.HeapSucc, null, oldHeap, newHeap));
    }
    Bpl.Expr HeapSucc(Bpl.Expr oldHeap, Bpl.Expr newHeap, bool useGhostHeapSucc = false) {
      return FunctionCall(newHeap.tok, useGhostHeapSucc ? BuiltinFunction.HeapSuccGhost : BuiltinFunction.HeapSucc, null, oldHeap, newHeap);
    }

    // Bpl-making-utilities

    /// <summary>
    /// Create a Boogie quantifier with body "A ==> body" and triggers "trg", but use only the subset of bound
    /// variables from "varsAndAntecedents" that actually occur free in "body" or "trg", and "A" is the conjunction of
    /// antecedents for those corresponding bound variables.  If none of the bound variables is used, "body"
    /// is returned. Also, if none of the bound variables is used in "body" (whether or not they are used in "trg"),
    /// then "body" is returned.
    /// The order of the contents of "varsAndAntecedents" matters: For any index "i" into "varsAndAntecedents", the
    /// antecedent varsAndAntecedents[i].Item2 may depend on a variable varsAndAntecedents[j].Item1 if "j GREATER-OR-EQUAL i"
    /// but not if "j LESS i".
    /// Caution: if "trg" is null, makes a forall without any triggers.
    /// </summary>
    static Bpl.Expr BplForallTrim(IEnumerable<Tuple<Bpl.Variable, Bpl.Expr/*?*/>> varsAndAntecedents, Bpl.Trigger trg, Bpl.Expr body) {
      Contract.Requires(varsAndAntecedents != null);
      Contract.Requires(body != null);

      // We'd like to compute the free variables if "body" and "trg". It would be nice to use the Boogie
      // routine Bpl.Expr.ComputeFreeVariables for this purpose. However, calling it requires the Boogie
      // expression to be resolved. Instead, we do the cheesy thing of computing the set of names of
      // free variables in "body" and "trg".
      var vis = new VariableNameVisitor();
      vis.Visit(body);
      if (varsAndAntecedents.All(pair => !vis.Names.Contains(pair.Item1.Name))) {
        // the body doesn't mention any of the bound variables, so no point in wrapping a quantifier around it
        return body;
      }
      for (var tt = trg; tt != null; tt = tt.Next) {
        tt.Tr.ForEach(ee => vis.Visit(ee));
      }

      var args = new List<Bpl.Variable>();
      Bpl.Expr typeAntecedent = Bpl.Expr.True;
      foreach (var pair in varsAndAntecedents) {
        var bv = pair.Item1;
        var wh = pair.Item2;
        if (vis.Names.Contains(bv.Name)) {
          args.Add(bv);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
            vis.Visit(wh);  // this adds to "vis.Names" the free variables of "wh"
          }
        }
      }
      if (args.Count == 0) {
        return body;
      } else {
        return new Bpl.ForallExpr(body.tok, args, trg, BplImp(typeAntecedent, body));
      }
    }
    class VariableNameVisitor : Boogie.StandardVisitor {
      public readonly HashSet<string> Names = new HashSet<string>();
      public override Expr VisitIdentifierExpr(Bpl.IdentifierExpr node) {
        Names.Add(node.Name);
        return base.VisitIdentifierExpr(node);
      }
      public override BinderExpr VisitBinderExpr(BinderExpr node) {
        var vis = new VariableNameVisitor();
        vis.Visit(node.Body);
        var dummyNames = new HashSet<string>(node.Dummies.Select(v => v.Name));
        foreach (var nm in vis.Names) {
          if (!dummyNames.Contains(nm)) {
            Names.Add(nm);
          }
        }
        return (BinderExpr)base.VisitBinderExpr(node);
      }
    }

    List<Bpl.Variable> MkTyParamBinders(List<TypeParameter> args) {
      return MkTyParamBinders(args, out _);
    }

    List<Bpl.Variable> MkTyParamBinders(List<TypeParameter> args, out List<Bpl.Expr> exprs) {
      var vars = new List<Bpl.Variable>();
      exprs = new List<Bpl.Expr>();
      foreach (TypeParameter v in args) {
        vars.Add(BplBoundVar(NameTypeParam(v), predef.Ty, out var e));
        exprs.Add(e);
      }
      return vars;
    }

    // For incoming formals
    List<Variable> MkTyParamFormals(List<TypeParameter> args, bool includeWhereClause, bool named = true) {
      return MkTyParamFormals(args, out _, includeWhereClause, named);
    }

    // For incoming formals
    List<Bpl.Variable> MkTyParamFormals(List<TypeParameter> args, out List<Bpl.Expr> exprs, bool includeWhereClause, bool named) {
      var vars = new List<Bpl.Variable>();
      exprs = new List<Bpl.Expr>();
      foreach (TypeParameter v in args) {
        var whereClause = includeWhereClause ? GetTyWhereClause(new Bpl.IdentifierExpr(v.tok, NameTypeParam(v), predef.Ty), v.Characteristics) : null;
        vars.Add(BplFormalVar(named ? NameTypeParam(v) : null, predef.Ty, true, out var e, whereClause));
        exprs.Add(e);
      }
      return vars;
    }

    public Bpl.Expr/*?*/ GetTyWhereClause(Bpl.Expr expr, TypeParameter.TypeParameterCharacteristics characteristics) {
      Contract.Requires(expr != null);
      if (characteristics.ContainsNoReferenceTypes) {
        return FunctionCall(expr.tok, "$AlwaysAllocated", Bpl.Type.Bool, expr);
      }
      return null;
    }

    public static void MapM<A>(IEnumerable<A> xs, Action<A> K) {
      Contract.Requires(xs != null);
      Contract.Requires(K != null);
      foreach (A x in xs) {
        K(x);
      }
    }

    static readonly List<Boolean> Bools = new List<Boolean> { false, true };

    public Expr GetRevealConstant(Function f) {
      this.CreateRevealableConstant(f);
      return this.functionReveals[f];
    }
  }
}
