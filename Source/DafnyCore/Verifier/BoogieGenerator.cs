//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using System.Threading;
using DafnyCore;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;
using DafnyCore.Verifier;
using JetBrains.Annotations;
using Microsoft.Dafny;
using Microsoft.Dafny.Triggers;
using Serilog.Events;
using PODesc = Microsoft.Dafny.ProofObligationDescription;
using static Microsoft.Dafny.GenericErrors;

namespace Microsoft.Dafny {

  /// <summary>
  /// Used as an origin for Boogie implementations, to track which Dafny ICanVerify the implementation originated from
  /// When Dafny generates ICanVerify nodes from other ones, this should be used so we can backtrack to the original one.
  /// </summary>
  class CanVerifyOrigin : OriginWrapper {
    /// <summary>
    /// Used as an origin for Boogie implementations, to track which Dafny ICanVerify the implementation originated from
    /// When Dafny generates ICanVerify nodes from other ones, this should be used so we can backtrack to the original one.
    /// </summary>
    public CanVerifyOrigin(ICanVerify canVerify) : base(canVerify.Origin) {
      CanVerify = canVerify;
    }

    public ICanVerify CanVerify { get; }
  }

  public partial class BoogieGenerator {
    private DafnyOptions options;
    public DafnyOptions Options => options;
    public const string NameSeparator = "$$";
    public const string CallPrefix = "Call";
    private HashSet<Uri> filesWhereOnlyMembersAreVerified = [];

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
      this.reporter = reporter;
      if (flags == null) {
        flags = new TranslatorFlags(options) {
          ReportRanges = options.Get(Snippets.ShowSnippets)
        };
      }
      this.flags = flags;
      Bpl.Program boogieProgram = ReadPrelude();
      if (boogieProgram != null) {
        sink = boogieProgram;
        foreach (var function in boogieProgram.TopLevelDeclarations.OfType<Bpl.Function>()) {
          function.AlwaysRevealed = true;
        }
        Predef = FindPredefinedDecls(boogieProgram);
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
    readonly List<FuelConstant> functionFuel = [];
    readonly Dictionary<Function, Bpl.Expr> functionReveals = new();
    readonly Dictionary<Field/*!*/, Bpl.Constant/*!*/>/*!*/ fields = new Dictionary<Field/*!*/, Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/, Bpl.Function/*!*/>/*!*/ fieldFunctions = new Dictionary<Field/*!*/, Bpl.Function/*!*/>();
    readonly Dictionary<string, Bpl.Constant> fieldConstants = new Dictionary<string, Constant>();
    readonly Dictionary<string, Bpl.Constant> tytagConstants = new Dictionary<string, Constant>();

    private ProofDependencyManager proofDependencies;

    /**
     * The behavior around this field assumes that usages are visited before declarations
     * which is only the case when the usage is in a different module than the declaration.
     * However, we alleviate this problem by saying that any declaration must be kept
     * if any code in that module is verified.
     */
    readonly ISet<MemberDecl> referencedMembers = new HashSet<MemberDecl>();

    public void AddReferencedMember(MemberDecl m) {
      if (m is MethodOrConstructor && !InVerificationScope(m)) {
        referencedMembers.Add(m);
      }
    }

    FuelContext fuelContext = null;
    public IsAllocContext IsAllocContext { get; set; } = null;
    Program program;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Cce.NonNullDictionaryAndValues(classes));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(fields));
      Contract.Invariant(Cce.NonNullDictionaryAndValues(fieldFunctions));
      Contract.Invariant(codeContext == null || codeContext.EnclosingModule == currentModule);
    }

    [System.Diagnostics.Contracts.Pure]
    bool VisibleInScope(Declaration d) {
      Contract.Requires(d != null);
      if (d is ClassLikeDecl { NonNullTypeDecl: { } nntd }) {
        // "provides" is recorded in the non-null type declaration, not the class
        return nntd.IsVisibleInScope(currentScope);
      }
      return d.IsVisibleInScope(currentScope);
    }

    [System.Diagnostics.Contracts.Pure]
    bool VisibleInScope(Type t) {
      if (t is UserDefinedType udt && udt.ResolvedClass != null && !t.IsTypeParameter) {
        return VisibleInScope(udt.ResolvedClass);
      }
      return true;
    }

    [System.Diagnostics.Contracts.Pure]
    bool RevealedInScope(Declaration d) {
      Contract.Requires(d != null);
      return d.IsRevealedInScope(currentScope);
    }

    [System.Diagnostics.Contracts.Pure]
    bool RevealedInScope(RevealableTypeDecl d) {
      Contract.Requires(d != null);
      return RevealedInScope(d.AsTopLevelDecl);
    }

    [System.Diagnostics.Contracts.Pure]
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

    [System.Diagnostics.Contracts.Pure]
    bool InVerificationScope(RedirectingTypeDecl d) {
      Contract.Requires(d != null);
      Contract.Requires(d is Declaration);
      return InVerificationScope((Declaration)d);
    }

    private Bpl.Program sink;
    private VisibilityScope currentScope;
    private VisibilityScope verificationScope;
    private Dictionary<Declaration, Bpl.Function> declarationMapping = new();

    public PredefinedDecls Predef { get; }

    private TranslatorFlags flags;
    private bool InsertChecksums { get { return flags.InsertChecksums; } }
    private string UniqueIdPrefix { get { return flags.UniqueIdPrefix; } }

    public class PredefinedDecls {
      public readonly Bpl.Type CharType;
      public readonly Bpl.Type RefType;
      public readonly Bpl.Type BoxType;
      public readonly Bpl.Type SetType;
      public readonly Bpl.Type ISetType;
      public readonly Bpl.Type MultiSetType;
      public readonly Bpl.Type SeqType;
      public readonly Bpl.Type MapType;
      public readonly Bpl.Type IMapType;
      public Bpl.Type BigOrdinalType {
        get { return BoxType; }
      }
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
      readonly Bpl.TypeCtorDecl fieldNameFamily;
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
      public readonly Bpl.Expr Locals;
      public readonly Bpl.Constant AllocField;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(CharType != null);
        Contract.Invariant(RefType != null);
        Contract.Invariant(BoxType != null);
        Contract.Invariant(SetType != null);
        Contract.Invariant(ISetType != null);
        Contract.Invariant(MultiSetType != null);
        Contract.Invariant(SeqType != null);
        Contract.Invariant(MapType != null);
        Contract.Invariant(IMapType != null);
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

      public Bpl.Type FieldName(Bpl.IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(tok, fieldName, []);
      }

      public Bpl.Type FieldNameFamily(Bpl.IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(tok, fieldNameFamily, []);
      }

      public Bpl.IdentifierExpr Alloc(Bpl.IToken tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

        return new Bpl.IdentifierExpr(tok, AllocField);
      }

      public PredefinedDecls(Bpl.TypeCtorDecl charType, Bpl.TypeCtorDecl refType, Bpl.TypeCtorDecl boxType,
                             Bpl.TypeCtorDecl setTypeCtor, Bpl.TypeSynonymDecl isetTypeCtor, Bpl.TypeCtorDecl multiSetTypeCtor,
                             Bpl.TypeCtorDecl mapTypeCtor, Bpl.TypeCtorDecl imapTypeCtor,
                             Bpl.Function arrayLength, Bpl.Function realFloor,
                             Bpl.Function ORD_isLimit, Bpl.Function ORD_isSucc, Bpl.Function ORD_offset, Bpl.Function ORD_isNat,
                             Bpl.Function mapDomain, Bpl.Function imapDomain,
                             Bpl.Function mapValues, Bpl.Function imapValues, Bpl.Function mapItems, Bpl.Function imapItems,
                             Bpl.Function objectTypeConstructor,
                             Bpl.Function tuple2Destructors0, Bpl.Function tuple2Destructors1, Bpl.Function tuple2Constructor, Bpl.Function tuple2TypeConstructor,
                             Bpl.TypeCtorDecl seqTypeCtor, Bpl.TypeSynonymDecl bv0TypeDecl,
                             Bpl.TypeCtorDecl fieldNameType, Bpl.TypeCtorDecl fieldNameFamilyType, Bpl.TypeCtorDecl tyType, Bpl.TypeCtorDecl tyTagType, Bpl.TypeCtorDecl tyTagFamilyType,
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

        this.CharType = new Bpl.CtorType(Token.NoToken, charType, []);
        Bpl.CtorType refT = new Bpl.CtorType(Token.NoToken, refType, []);
        this.RefType = refT;
        this.BoxType = new Bpl.CtorType(Token.NoToken, boxType, []);
        this.SetType = new Bpl.CtorType(Token.NoToken, setTypeCtor, []);
        this.ISetType = new Bpl.TypeSynonymAnnotation(Token.NoToken, isetTypeCtor, []);
        this.MultiSetType = new Bpl.CtorType(Token.NoToken, multiSetTypeCtor, []);
        this.SeqType = new Bpl.CtorType(Token.NoToken, seqTypeCtor, []);
        this.MapType = new Bpl.CtorType(Token.NoToken, mapTypeCtor, []);
        this.IMapType = new Bpl.CtorType(Token.NoToken, imapTypeCtor, []);
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
        this.Bv0Type = new Bpl.TypeSynonymAnnotation(Token.NoToken, bv0TypeDecl, []);
        this.fieldName = fieldNameType;
        this.fieldNameFamily = fieldNameFamilyType;
        this.HeapType = heap.TypedIdent.Type;
        this.HeapVarName = heap.Name;
        this.Ty = new Bpl.CtorType(Token.NoToken, tyType, []);
        this.TyTag = new Bpl.CtorType(Token.NoToken, tyTagType, []);
        this.TyTagFamily = new Bpl.CtorType(Token.NoToken, tyTagFamilyType, []);
        this.ClassNameType = new Bpl.CtorType(Token.NoToken, classNameType, []);
        this.NameFamilyType = new Bpl.CtorType(Token.NoToken, nameFamilyType, []);
        this.DatatypeType = new Bpl.CtorType(Token.NoToken, datatypeType, []);
        this.HandleType = new Bpl.CtorType(Token.NoToken, handleType, []);
        this.LayerType = new Bpl.CtorType(Token.NoToken, layerType, []);
        this.DtCtorId = new Bpl.CtorType(Token.NoToken, dtCtorId, []);
        this.AllocField = allocField;
        this.Null = new Bpl.IdentifierExpr(Token.NoToken, "null", refT);
        this.Locals = new Bpl.IdentifierExpr(Token.NoToken, "locals", refT);
      }
    }

    PredefinedDecls FindPredefinedDecls(Bpl.Program prog) {
      Contract.Requires(prog != null);
      if (prog.Resolve(options) != 0) {
        options.OutputWriter.Exception("resolution errors encountered in Dafny prelude");
        return null;
      }

      Bpl.TypeCtorDecl charType = null;
      Bpl.TypeCtorDecl refType = null;
      Bpl.TypeCtorDecl setTypeCtor = null;
      Bpl.TypeSynonymDecl isetTypeCtor = null;
      Bpl.TypeCtorDecl multiSetTypeCtor = null;
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
      Bpl.TypeCtorDecl fieldFamilyNameType = null;
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
          } else if (dt.Name == "FieldFamily") {
            fieldFamilyNameType = dt;
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
          } else if (dt.Name == "Set") {
            setTypeCtor = dt;
          } else if (dt.Name == "MultiSet") {
            multiSetTypeCtor = dt;
          } else if (dt.Name == "Map") {
            mapTypeCtor = dt;
          } else if (dt.Name == "IMap") {
            imapTypeCtor = dt;
          }
        } else if (d is Bpl.TypeSynonymDecl) {
          Bpl.TypeSynonymDecl dt = (Bpl.TypeSynonymDecl)d;
          if (dt.Name == "ISet") {
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
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Seq");
      } else if (setTypeCtor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Set");
      } else if (isetTypeCtor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type ISet");
      } else if (multiSetTypeCtor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type MultiSet");
      } else if (mapTypeCtor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Map");
      } else if (imapTypeCtor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type IMap");
      } else if (arrayLength == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function _System.array.Length");
      } else if (realFloor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function _System.real.Floor");
      } else if (ORDINAL_isLimit == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function ORD#IsLimit");
      } else if (ORDINAL_isSucc == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function ORD#IsSucc");
      } else if (ORDINAL_offset == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function ORD#Offset");
      } else if (ORDINAL_isNat == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function ORD#IsNat");
      } else if (mapDomain == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function Map#Domain");
      } else if (imapDomain == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function IMap#Domain");
      } else if (mapValues == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function Map#Values");
      } else if (imapValues == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function IMap#Values");
      } else if (mapItems == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function Map#Items");
      } else if (imapItems == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function IMap#Items");
      } else if (tuple2Destructors0 == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function _System.Tuple2._0");
      } else if (tuple2Destructors1 == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function _System.Tuple2._1");
      } else if (tuple2Constructor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of function #_System._tuple#2._#Make2");
      } else if (bv0TypeDecl == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Bv0");
      } else if (fieldNameType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Field");
      } else if (fieldFamilyNameType == null) {
        options.OutputWriter.Exception("Error: Dafny prelude is missing declaration of type FieldFamily");
      } else if (classNameType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type ClassName");
      } else if (tyType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Ty");
      } else if (tyTagType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type TyTag");
      } else if (tyTagFamilyType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type TyTagFamily");
      } else if (nameFamilyType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type NameFamily");
      } else if (datatypeType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type DatatypeType");
      } else if (handleType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type HandleType");
      } else if (layerType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type LayerType");
      } else if (dtCtorId == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type DtCtorId");
      } else if (charType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type char");
      } else if (refType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type ref");
      } else if (boxType == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of type Box");
      } else if (heap == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of $Heap");
      } else if (allocField == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of constant alloc");
      } else if (tuple2TypeConstructor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of tuple2TypeConstructor");
      } else if (objectTypeConstructor == null) {
        options.OutputWriter.Exception("Dafny prelude is missing declaration of objectTypeConstructor");
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
                                   fieldNameType, fieldFamilyNameType, tyType, tyTagType, tyTagFamilyType,
                                   heap, classNameType, nameFamilyType,
                                   datatypeType, handleType, layerType, dtCtorId,
                                   allocField);
      }
      return null;
    }

    Bpl.Program ReadPrelude() {
      string preludePath = options.DafnyPrelude;
      if (preludePath == null) {
        //using (System.IO.Stream stream = Cce.NonNull( System.Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream("DafnyPrelude.bpl")) // Use this once Spec#/VSIP supports designating a non-.resx project item as an embedded resource
        string codebase = Cce.NonNull(System.IO.Path.GetDirectoryName(Cce.NonNull(System.Reflection.Assembly.GetExecutingAssembly().Location)));
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

    public Bpl.IdentifierExpr TrVar(IOrigin tok, IVariable var) {
      Contract.Requires(var != null);
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);
      return new Bpl.IdentifierExpr(tok, var.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(var.Type));
    }

    public Bpl.Program DoTranslation(Program p, ModuleDefinition forModule) {
      if (sink == null) {
        return new Bpl.Program();
      }

      if (Options.GetOrOptionDefault(CommonOptionBag.LogLevelOption).CompareTo(LogEventLevel.Verbose) <= 0) {
        _ = Options.OutputWriter.Status("Starting translation to Boogie of module " + forModule.FullDafnyName);
      }

      foreach (var plugin in p.Options.Plugins) {
        foreach (var rewriter in plugin.GetRewriters(p.Reporter)) {
          rewriter.PreVerify(forModule);
        }
      }

      program = p;
      this.forModule = forModule;
      triggersCollector = new TriggersCollector(new Dictionary<Expression, HashSet<OldExpr>>(), options, forModule);
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
        CurrentDeclaration = d;
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
        mods.SelectMany(m => m.TopLevelDecls.Where(VisibleInScope)).ToList();

      foreach (var d in visibleTopLevelDecls) {
        if (d is TopLevelDeclWithMembers memberContainer) {
          foreach (var member in memberContainer.Members) {
            if (Attributes.Contains(member.Attributes, "only")) {
              filesWhereOnlyMembersAreVerified.Add(member.Origin.Uri);
            }
          }
        }
      }

      foreach (TopLevelDecl d in visibleTopLevelDecls) {
        CurrentDeclaration = d;
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

      filesWhereOnlyMembersAreVerified = [];

      AddTraitParentAxioms();

      foreach (var c in tytagConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }
      foreach (var c in fieldConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }

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
    public static bool ShouldVerifyModule(Program program, ModuleDefinition m) {
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
        args = [a0, a1];
      } else {
        var a0 = BplFormalVar(null, t, true);
        args = [a0];
      }
      var r = BplFormalVar(null, resultType ?? t, false);
      Bpl.QKeyValue attr;
      if (w == 0) {
        attr = InlineAttribute(tok);
      } else {
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
      }
      var func = new Bpl.Function(tok, namePrefix + w, [], args, r, null, attr);
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
      args = [a0, a1];
      var r = BplFormalVar(null, t, false);
      Bpl.QKeyValue attr;
      if (w == 0) {
        attr = InlineAttribute(tok);
      } else {
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { smtFunctionName }, null);
      }
      var func = new Bpl.Function(tok, namePrefix + w, [], args, r, null, attr);
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
      func = new Bpl.Function(tok, "nat_to_bv" + w, [],
        [BplFormalVar(null, Bpl.Type.Int, true)], BplFormalVar(null, bv, false),
        null, attr);
      if (w == 0) {
        func.Body = BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, w);
      }
      sink.AddTopLevelDeclaration(func);

      if (w == 0) {
        // function {:inline} nat_from_bv0_smt(Bv0) : int { 0 }
        attr = InlineAttribute(tok);
        func = new Bpl.Function(tok, "nat_from_bv" + w, [],
          [BplFormalVar(null, bv, true)], BplFormalVar(null, Bpl.Type.Int, false),
          null, attr);
        func.Body = Bpl.Expr.Literal(0);
        sink.AddTopLevelDeclaration(func);
      } else {
        // function {:bvbuiltin "bv2int"} smt_nat_from_bv67(bv67) : int;
        attr = new Bpl.QKeyValue(tok, "bvbuiltin", new List<object>() { "bv2int" }, null);  // SMT-LIB 2 calls this function bv2nat, but Z3 apparently calls it bv2int
        var smtFunc = new Bpl.Function(tok, "smt_nat_from_bv" + w, [],
          [BplFormalVar(null, bv, true)], BplFormalVar(null, Bpl.Type.Int, false),
          null, attr);
        sink.AddTopLevelDeclaration(smtFunc);
        // function nat_from_bv67(bv67) : int;
        func = new Bpl.Function(tok, "nat_from_bv" + w, [],
          [BplFormalVar(null, bv, true)], BplFormalVar(null, Bpl.Type.Int, false),
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
        var ax = new Bpl.ForallExpr(tok, [bVar], BplTrigger(bv2nat), body);
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
                  Bpl.Constant baseFuel = new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, "BaseFuel_" + f.FullName, Predef.LayerType), false);
                  sink.AddTopLevelDeclaration(baseFuel);
                  Bpl.Expr baseFuel_expr = new Bpl.IdentifierExpr(f.Origin, baseFuel);
                  // const StartFuel_FunctionA : LayerType
                  Bpl.Constant startFuel = new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, "StartFuel_" + f.FullName, Predef.LayerType), false);
                  sink.AddTopLevelDeclaration(startFuel);
                  Bpl.Expr startFuel_expr = new Bpl.IdentifierExpr(f.Origin, startFuel);
                  // const StartFuelAssert_FunctionA : LayerType
                  Bpl.Constant startFuelAssert = new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, "StartFuelAssert_" + f.FullName, Predef.LayerType), false);
                  sink.AddTopLevelDeclaration(startFuelAssert);
                  Bpl.Expr startFuelAssert_expr = new Bpl.IdentifierExpr(f.Origin, startFuelAssert);
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
          new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, HideRevealStmt.RevealLemmaPrefix + f.FullName, Bpl.Type.Bool), false);
        sink.AddTopLevelDeclaration(revealTrigger);
        Bpl.Expr revealTrigger_expr = new Bpl.IdentifierExpr(f.Origin, revealTrigger);
        this.functionReveals[f] = revealTrigger_expr;

        // If this is an override, generate:
        //     axiom reveal_FunctionA ==> reveal_FunctionParent;
        if (f.OverriddenFunction is { IsOpaque: true }) {
          var revealParent = GetRevealConstant(f.OverriddenFunction);
          var implication = BplImp(revealTrigger_expr, revealParent);
          AddOtherDefinition(revealTrigger, new Axiom(f.Origin, implication));
        }
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
        foreach (var c in m.TopLevelDecls.OfType<TopLevelDeclWithMembers>().Where(RevealedInScope)) {
          foreach (var parentTypeInExtendsClause in c.Traits) {
            var childType = UserDefinedType.FromTopLevelDecl(c.Origin, c);
            var parentType = (UserDefinedType)parentTypeInExtendsClause;
            if (parentType.IsRefType) {
              // use the nullable versions of the types
              Contract.Assert(childType.IsRefType);
              parentType = UserDefinedType.CreateNullableType(parentType);
            } else {
              childType = UserDefinedType.CreateNonNullTypeIfReferenceType(childType);
            }

            var bvarsTypeParameters = MkTyParamBinders(GetTypeParams(c), out _);

            // axioms with "$IsBox(...) ==> ..." and "$IsAllocBox(...) ==> ..."
            TypeBoundAxiomExpressions(c.Origin, bvarsTypeParameters, childType, [parentType],
              out var isBoxExpr, out var isAllocBoxExpr);

            var heapVar = BplBoundVar("$heap", Predef.HeapType, out var heap);
            var oVar = BplBoundVar("$o", TrType(childType), out var o);

            var oj = BoxifyForTraitParent(c.Origin, o, ((UserDefinedType)parentType.NormalizeExpand()).ResolvedClass, childType);

            // axiom (forall T: Ty, $o: ref ::
            //     { $Is($o, C(T)) }
            //     $Is($o, C(T)) ==> $Is($o, J(G(T)));
            var isC = MkIs(o, childType);
            var isJ = MkIs(oj, parentType);
            var bvs = new List<Bpl.Variable>();
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            var tr = BplTrigger(isC);
            var body = BplImp(isC, isJ);

            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.Origin, new Bpl.ForallExpr(c.Origin, bvs, tr, body),
              $"type axiom for trait parent: {childType.Name} extends {parentType}"));
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.Origin, isBoxExpr));

            // axiom (forall T: Ty, $Heap: Heap, $o: ref ::
            //     { $IsAlloc($o, C(T), $Heap) }
            //     $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
            var isAllocC = MkIsAlloc(o, childType, heap);
            var isAllocJ = MkIsAlloc(oj, parentType, heap);
            bvs = [];
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            bvs.Add(heapVar);
            tr = BplTrigger(isAllocC);
            body = BplImp(isAllocC, isAllocJ);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.Origin, new Bpl.ForallExpr(c.Origin, bvs, tr, body),
              $"allocation axiom for trait parent: {childType.Name} extends {parentType}"));
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.Origin, isAllocBoxExpr));
          }
        }
      }
    }

    /// <summary>
    /// Construct an expression denoting the equality of e0 and e1, taking advantage of
    /// any available extensional equality based on the given Dafny type.
    /// </summary>
    public Expr TypeSpecificEqual(IOrigin tok, Dafny.Type type, Expr e0, Expr e1) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);

      type = type.NormalizeToAncestorType();
      if (type.AsSetType != null) {
        var finite = type.NormalizeToAncestorType().AsSetType.Finite;
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
    IEnumerable<Bpl.Expr> CoPrefixEquality(IOrigin tok, CoDatatypeDecl dt, List<Type> largs, List<Type> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, bool conjuncts = false) {
      Contract.Requires(tok != null);
      Contract.Requires(dt != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      Contract.Requires(l != null);
      Contract.Requires(Predef != null);
      var etran = new ExpressionTranslator(this, Predef, dt.Origin, dt);
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
          yield return Bpl.Expr.Binary(
            new NestedOrigin(tok, ctor.Origin, "this proposition could not be proved"),
            BinaryOperator.Opcode.Imp, aq, BplAnd(bq, chunk));
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
    Bpl.Expr CoEqualCall(CoDatatypeDecl codecl, List<Type> largs, List<Type> rargs, Bpl.Expr k, Bpl.Expr l, Bpl.Expr A, Bpl.Expr B, IOrigin tok = null) {
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
      Contract.Ensures(Cce.NonNullElements(Contract.ValueAtReturn(out args)));

      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("a#");
      bvs = [];
      args = [];
      foreach (var arg in formals) {
        Contract.Assert(arg != null);
        var nm = varNameGen.FreshId(string.Format("#{0}#", bvs.Count));
        Bpl.Variable bv = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, nm, TrType(arg.Type)));
        bvs.Add(bv);
        args.Add(new Bpl.IdentifierExpr(arg.Origin, bv));
      }
    }

    // This one says that this is /directly/ allocated, not that its "children" are,
    // i.e. h[x, alloc]
    public Bpl.Expr IsAlloced(IOrigin tok, Bpl.Expr heapExpr, Bpl.Expr e) {
      Contract.Requires(tok != null);
      Contract.Requires(heapExpr != null);
      Contract.Requires(e != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      return ApplyUnbox(tok, ReadHeap(tok, heapExpr, e, Predef.Alloc(tok)), Bpl.Type.Bool);
    }

    /// <summary>
    /// Returns read(heap: Heap, r: ref, f: Field) : Box.
    /// </summary>
    public Bpl.Expr ReadHeap(IOrigin tok, Expr heap, Expr r, Expr f) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);

      var res = new Bpl.NAryExpr(tok,
        new Bpl.FunctionCall(new Bpl.IdentifierExpr(tok, "read", Predef.BoxType)),
        new List<Bpl.Expr> { heap, r, f });
      res.Type = Predef.BoxType;
      return res;
    }

    public Bpl.NAryExpr ReadHeap(IOrigin tok, Expr heap, Expr r) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Ensures(Contract.Result<Bpl.NAryExpr>() != null);
      return new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> { heap, r });
    }

    /// <summary>
    /// Returns update(h: Heap, r: ref, f: Field, v: Box) : Heap.
    /// </summary>
    public Boogie.NAryExpr UpdateHeap(IOrigin tok, Expr heap, Expr r, Expr f, Expr v) {
      Contract.Requires(tok != null);
      Contract.Requires(heap != null);
      Contract.Requires(r != null);
      Contract.Requires(f != null);
      Contract.Requires(v != null);
      Contract.Ensures(Contract.Result<Boogie.NAryExpr>() != null);


      return new Boogie.NAryExpr(tok,
        new Boogie.FunctionCall(new Boogie.IdentifierExpr(tok, "update", heap.Type)),
        new List<Boogie.Expr> { heap, r, f, ApplyBox(tok, v) });
    }

    public Bpl.Expr DType(Bpl.Expr e, Bpl.Expr type) {
      return Bpl.Expr.Eq(FunctionCall(e.tok, BuiltinFunction.DynamicType, null, e), type);
    }

    public Bpl.Expr GetArrayIndexFieldName(IOrigin tok, List<Bpl.Expr> indices) {
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
    bool FunctionBodyIsAvailable(Function f, ModuleDefinition context, VisibilityScope scope) {
      Contract.Requires(f != null);
      Contract.Requires(context != null);
      return f.Body != null && !IsOpaque(f, options) && f.IsRevealedInScope(scope);
    }
    public static bool IsOpaque(MemberDecl f, DafnyOptions options) {
      Contract.Requires(f != null);
      if (f is Function f1) {
        return Attributes.Contains(f.Attributes, "opaque") || f.IsOpaque || f1.IsMadeImplicitlyOpaque(options);
      } else {
        return Attributes.Contains(f.Attributes, "opaque") || f.IsOpaque;
      }
    }
    static bool IsOpaqueRevealLemma(MethodOrConstructor m) {
      Contract.Requires(m != null);
      return Attributes.Contains(m.Attributes, "opaque_reveal");
    }


    void AddEnsures(List<Bpl.Ensures> list, Bpl.Ensures ens) {
      list.Add(ens);
      if (!ens.Free) {
        this.assertionCount++;
      }
    }

    private Implementation AddImplementationWithAttributes(CanVerifyOrigin tok, Procedure proc, List<Variable> inParams,
      List<Variable> outParams, Variables localVariables, StmtList stmts, QKeyValue kv) {
      Bpl.Implementation impl = new Bpl.Implementation(tok, proc.Name,
        [], inParams, outParams,
        localVariables.Values.ToList<Variable>(), stmts, kv);
      AddVerboseNameAttribute(impl, proc.VerboseName);
      if (options.IsUsingZ3()) {
        if (DisableNonLinearArithmetic) {
          AddSmtOptionAttribute(impl, "smt.arith.nl", "false");
        }

        AddSmtOptionAttribute(impl, "smt.arith.solver", ArithmeticSolver.ToString());
      }
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
      DefiniteAssignmentTrackers.Clear();
    }

    public static Bpl.QKeyValue InlineAttribute(Bpl.IToken tok, Bpl.QKeyValue/*?*/ next = null) {
      Contract.Requires(tok != null);
      return new QKeyValue(tok, "inline", new List<object>(), next);
    }

    public static Bpl.QKeyValue AlwaysAssumeAttribute(Bpl.IToken tok, Bpl.QKeyValue next = null) {
      Contract.Requires(tok != null);
      return new QKeyValue(tok, "always_assume", new List<object>(), next);
    }

    class Specialization {
      public readonly List<Formal/*!*/> Formals;
      public readonly List<Expression/*!*/> ReplacementExprs;
      public readonly List<BoundVar/*!*/> ReplacementFormals;
      public readonly Dictionary<IVariable, Expression> SubstMap;
      readonly BoogieGenerator boogieGenerator;
      [ContractInvariantMethod]
      void ObjectInvariant() {
        Contract.Invariant(Cce.NonNullElements(Formals));
        Contract.Invariant(Cce.NonNullElements(ReplacementExprs));
        Contract.Invariant(Formals.Count == ReplacementExprs.Count);
        Contract.Invariant(Cce.NonNullElements(ReplacementFormals));
        Contract.Invariant(SubstMap != null);
      }

      public Specialization(IVariable formal, MatchCase mc, Specialization prev, BoogieGenerator boogieGenerator) {
        Contract.Requires(formal is Formal || formal is BoundVar);
        Contract.Requires(mc != null);
        Contract.Requires(prev == null || formal is BoundVar || !prev.Formals.Contains((Formal)formal));
        Contract.Requires(boogieGenerator != null);

        this.boogieGenerator = boogieGenerator;

        List<Expression> rArgs = [];
        foreach (BoundVar p in mc.Arguments) {
          IdentifierExpr ie = new IdentifierExpr(p.Origin, p.AssignUniqueName(boogieGenerator.CurrentDeclaration.IdGenerator));
          ie.Var = p; ie.Type = ie.Var.Type;  // resolve it here
          rArgs.Add(ie);
        }
        // create and resolve datatype value
        var r = new DatatypeValue(mc.Origin, mc.Ctor.EnclosingDatatype.Name, mc.Ctor.Name, rArgs);
        r.Ctor = mc.Ctor;
        r.Type = new UserDefinedType(mc.Origin, mc.Ctor.EnclosingDatatype.Name,
          [] /*this is not right, but it seems like it won't matter here*/);

        Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(formal, r);

        // Fill in the fields
        Formals = [];
        ReplacementExprs = [];
        ReplacementFormals = [];
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

      var olderParameterCount = f.Ins.Count(formal => formal.IsOlder);
      if (olderParameterCount == 0) {
        // nothing to do
        return (olderParameterCount, Bpl.Expr.True);
      }

      // For a function F(older x: X, y: Y), generate:
      //     (forall h: Heap :: { OlderTag(h) }
      //         IsGoodHeap(h) && OlderTag(h) && F(x, y) && IsAlloc(y, Y, h)
      //         ==>  IsAlloc(x, X, h))
      var heapVar = BplBoundVar("$olderHeap", Predef.HeapType, out var heap);
      var etran = new ExpressionTranslator(this, Predef, heap, f);

      var isGoodHeap = FunctionCall(f.Origin, BuiltinFunction.IsGoodHeap, null, heap);
      var olderTag = FunctionCall(f.Origin, "$OlderTag", Bpl.Type.Bool, heap);
      Bpl.Expr older = Bpl.Expr.True;
      Bpl.Expr newer = Bpl.Expr.True;
      var i = 0;
      if (!f.IsStatic) {
        var th = new Bpl.IdentifierExpr(f.Origin, inParams[i]);
        i++;
        var wh = GetWhereClause(f.Origin, th, ModuleResolver.GetReceiverType(f.Origin, f), etran, ISALLOC, true);
        newer = BplAnd(newer, wh);
      }
      foreach (var formal in f.Ins) {
        var p = new Bpl.IdentifierExpr(f.Origin, inParams[i]);
        i++;
        var wh = GetWhereClause(formal.Origin, p, formal.Type, etran, ISALLOC, true);
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
      var tr = new Bpl.Trigger(f.Origin, true, new List<Bpl.Expr> { olderTag });
      var olderCondition = new Bpl.ForallExpr(f.Origin, [], [heapVar], null, tr, body);
      return (olderParameterCount, olderCondition);
    }

    Bpl.Type TrReceiverType(MemberDecl f) {
      Contract.Requires(f != null);
      return TrType(ModuleResolver.GetReceiverType(f.Origin, f));
    }

    Bpl.Expr ReceiverNotNull(Bpl.Expr th) {
      Contract.Requires(th != null);
      if (th.Type == Predef.RefType) {
        return Bpl.Expr.Neq(th, Predef.Null);
      } else {
        return Bpl.Expr.True;
      }
    }

    void AddFuelSuccSynonymAxiom(Function f, bool forHandle = false) {
      Contract.Requires(f != null);
      Contract.Requires(f.IsFuelAware());
      Contract.Requires(sink != null && Predef != null);
      // axiom  // layer synonym axiom
      //   (forall s, $Heap, formals ::
      //       { f(Succ(s), $Heap, formals) }
      //       f(Succ(s), $Heap, formals) == f(s, $Heap, formals));

      List<Bpl.Expr> tyargs;
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
      var args1 = new List<Bpl.Expr>(tyargs);
      var args0 = new List<Bpl.Expr>(tyargs);

      var bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$ly", Predef.LayerType));
      formals.Add(bv);
      var s = new Bpl.IdentifierExpr(f.Origin, bv);
      args1.Add(FunctionCall(f.Origin, BuiltinFunction.LayerSucc, null, s));
      args0.Add(s);
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        var bvReveal = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
        formals.Add(bvReveal);
        var sReveal = new Bpl.IdentifierExpr(f.Origin, bvReveal);
        args1.Add(sReveal);
        args0.Add(sReveal);
      }

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args1.Add(s);
        args0.Add(s);
      }
      if (!forHandle && f.ReadsHeap) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args1.Add(s);
        args0.Add(s);
      }

      if (!f.IsStatic) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args1.Add(s);
        args0.Add(s);
      }
      if (!forHandle) {
        foreach (var p in f.Ins) {
          bv = new Bpl.BoundVariable(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
          formals.Add(bv);
          s = new Bpl.IdentifierExpr(f.Origin, bv);
          args1.Add(s);
          args0.Add(s);
        }
      }

      var name = forHandle ? f.FullSanitizedName + "#Handle" : f.FullSanitizedName;
      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Origin, name, TrType(f.ResultType)));
      var funcAppl1 = new Bpl.NAryExpr(f.Origin, funcID, args1);
      var funcAppl0 = new Bpl.NAryExpr(f.Origin, funcID, args0);

      Bpl.Trigger tr = new Bpl.Trigger(f.Origin, true, new List<Bpl.Expr> { funcAppl1 });
      Bpl.Expr ax = new Bpl.ForallExpr(f.Origin, [], formals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
      AddOtherDefinition(GetOrCreateFunction(f), new Bpl.Axiom(f.Origin, ax, "layer synonym axiom"));
    }

    void AddFuelZeroSynonymAxiom(Function f) {
      // axiom  // fuel axiom
      //   (forall s, $Heap, formals ::
      //       { f(AsFuelBottom(s), $Heap, formals) }
      //       f(s, $Heap, formals) == f($LZ, $Heap, formals));
      Contract.Requires(f != null);
      Contract.Requires(f.IsFuelAware());
      Contract.Requires(sink != null && Predef != null);

      List<Bpl.Expr> tyargs;
      var formals = MkTyParamBinders(GetTypeParams(f), out tyargs);
      var args2 = new List<Bpl.Expr>(tyargs);
      var args1 = new List<Bpl.Expr>(tyargs);
      var args0 = new List<Bpl.Expr>(tyargs);

      var bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$ly", Predef.LayerType));
      formals.Add(bv);
      var s = new Bpl.IdentifierExpr(f.Origin, bv);
      args2.Add(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, s));
      args1.Add(s);
      args0.Add(new Bpl.IdentifierExpr(f.Origin, "$LZ", Predef.LayerType)); // $LZ
      if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
        var bvReveal = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool));
        formals.Add(bvReveal);
        var sReveal = new Bpl.IdentifierExpr(f.Origin, bvReveal);
        args2.Add(sReveal);
        args1.Add(sReveal);
        args0.Add(sReveal);
      }

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }
      if (f.ReadsHeap) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, Predef.HeapVarName, Predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }

      if (!f.IsStatic) {
        bv = new Bpl.BoundVariable(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }
      foreach (var p in f.Ins) {
        bv = new Bpl.BoundVariable(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.Origin, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }

      var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.Origin, f.FullSanitizedName, TrType(f.ResultType)));
      var funcAppl2 = new Bpl.NAryExpr(f.Origin, funcID, args2);
      var funcAppl1 = new Bpl.NAryExpr(f.Origin, funcID, args1);
      var funcAppl0 = new Bpl.NAryExpr(f.Origin, funcID, args0);

      Bpl.Trigger tr = new Bpl.Trigger(f.Origin, true, new List<Bpl.Expr> { funcAppl2 });
      Bpl.Expr ax = new Bpl.ForallExpr(f.Origin, [], formals, null, tr, Bpl.Expr.Eq(funcAppl1, funcAppl0));
      AddOtherDefinition(GetOrCreateFunction(f), (new Bpl.Axiom(f.Origin, ax, "fuel synonym axiom")));
    }

    Bpl.Expr InSeqRange(IOrigin tok, Bpl.Expr index, Type indexType, Bpl.Expr seq, bool isSequence, Bpl.Expr lowerBound, bool includeUpperBound) {
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

    public ImmutableDictionary<string, Bpl.IdentifierExpr> DefiniteAssignmentTrackers { get; set; } = ImmutableDictionary<string, Bpl.IdentifierExpr>.Empty;

    Func<Token, bool> assertionOnlyFilter = null; // generate assume statements instead of assert statements if not targeted by {:only}
    public enum StmtType { NONE, ASSERT, ASSUME };
    public StmtType stmtContext = StmtType.NONE;  // the Statement that is currently being translated
    public bool adjustFuelForExists = true;  // fuel need to be adjusted for exists based on whether exists is in assert or assume stmt.

    public readonly VerificationIdGenerator defaultIdGenerator = new VerificationIdGenerator();

    public VerificationIdGenerator CurrentIdGenerator {
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

    Bpl.IdentifierExpr GetTmpVar_IdExpr(Bpl.IToken tok, string name, Bpl.Type ty, Variables locals)  // local variable that's shared between statements that need it
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
        var v = locals.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, ty)));  // important for the "$nw" client: no where clause (see GetNewVar_IdExpr)
        ie = new Bpl.IdentifierExpr(tok, v);
        _tmpIEs.Add(name, ie);
      }
      return ie;
    }

    Bpl.IdentifierExpr GetPrevHeapVar_IdExpr(IOrigin tok, Variables locals)  // local variable that's shared between statements that need it
    {
      Contract.Requires(tok != null);
      Contract.Requires(locals != null); Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      return GetTmpVar_IdExpr(tok, "$prevHeap", Predef.HeapType, locals);
    }

    Bpl.IdentifierExpr GetNewVar_IdExpr(IOrigin tok, Variables locals)  // local variable that's shared between statements that need it
    {
      Contract.Requires(tok != null);
      Contract.Requires(locals != null);
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>() != null);

      // important: the following declaration produces no where clause (that's why we're going through the trouble of setting of this variable in the first place)
      return GetTmpVar_IdExpr(tok, "$nw", Predef.RefType, locals);
    }

    /// <summary>
    /// Returns an expression whose value is the same as "expr", but that is guaranteed to preserve the its value passed
    /// the evaluation of other expressions.  If necessary, a new local variable called "name" with type "ty" is added to "locals" and
    /// assigned in "builder" to be used to hold the value of "expr".  It is assumed that all requests for a given "name"
    /// have the same type "ty" and that these variables can be shared.
    /// As an optimization, if "otherExprsCanAffectPreviouslyKnownExpressions" is "false", then "expr" itself is returned.
    /// </summary>
    Bpl.Expr SaveInTemp(Bpl.Expr expr, bool otherExprsCanAffectPreviouslyKnownExpressions, string name, Bpl.Type ty, BoogieStmtListBuilder builder, Variables locals) {
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

    void InitializeFuelConstant(IOrigin tok, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
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
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, startFuel), startFuel)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, startFuelAssert), startFuelAssert)));
        } else {
          Bpl.Expr layer = etran.layerInterCluster.LayerN(settings.low, baseFuel);
          Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(settings.high, baseFuel);
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuel, layer)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuelAssert, layerAssert)));
          // assume AsFuelBottom(BaseFuel_F) == BaseFuel_F;
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(FunctionCall(f.Origin, BuiltinFunction.AsFuelBottom, null, baseFuel), baseFuel)));
        }
      }
    }

    bool DefineFuelConstant(IOrigin tok, Attributes attribs, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
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
          Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, Predef, f.IdGenerator);
          Bpl.Expr layer = etran.layerInterCluster.LayerN(settings.low, moreFuel_expr);
          Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(settings.high, moreFuel_expr);
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuel, layer)));
          builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(startFuelAssert, layerAssert)));
          defineFuel = true;
        }
      }
      return defineFuel;
    }

    internal static AssumeCmd optimizeExpr(bool minimize, Expression expr, IOrigin tok, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsIntegerType || expr.Type.IsRealType);
      Contract.Requires(tok != null && etran != null);

      var assumeCmd = new AssumeCmd(tok, Expr.True);
      assumeCmd.Attributes = new QKeyValue(expr.Origin, (minimize ? "minimize" : "maximize"), new List<object> { etran.TrExpr(expr) }, null);
      return assumeCmd;
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
        tyargs = f.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.Origin, tp));
      } else {
        var cl = (TopLevelDeclWithMembers)overridingFunction.EnclosingClass;
        var typeMap = cl.ParentFormalTypeParametersToActuals;
        tyargs = f.EnclosingClass.TypeArgs.ConvertAll(tp => typeMap[tp]);
      }
      tyargs.AddRange((overridingFunction ?? f).TypeArgs.ConvertAll(tp => new UserDefinedType(tp.Origin, tp)));
      return tyargs;
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
        printer.PrintAttributes(f.Attributes, false, -1);
        printer.PrintFormals(f.Ins, f);
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

    void GenerateImplPrelude(MethodOrConstructor m, bool wellformednessProc, List<Variable> inParams, List<Variable> outParams,
                             BoogieStmtListBuilder builder, Variables localVariables, ExpressionTranslator etran) {
      Contract.Requires(m != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(Predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);

      if (m is TwoStateLemma) {
        // $Heap := current$Heap;
        var heap = ExpressionTranslator.HeapIdentifierExpr(Predef, m.Origin);
        builder.Add(Bpl.Cmd.SimpleAssign(m.Origin, heap, new Bpl.IdentifierExpr(m.Origin, "current$Heap", Predef.HeapType)));
      }

      // set up the information used to verify the method's reads and modifies clauses
      if (etran.readsFrame != null) {
        DefineFrame(m.Origin, etran.ReadsFrame(m.Origin), m.Reads.Expressions, builder, localVariables, null);
      }
      DefineFrame(m.Origin, etran.ModifiesFrame(m.Origin), m.Mod.Expressions, builder, localVariables, null);
      if (wellformednessProc) {
        builder.AddCaptureState(m.Origin, false, "initial state");
      } else {
        Contract.Assert(m.Body != null);  // follows from precondition and the if guard
        // use the position immediately after the open-curly-brace of the body
        builder.AddCaptureState(m.Body.Origin, true, "initial state");
      }
    }

    public void DefineFrame(IOrigin/*!*/ tok, Boogie.IdentifierExpr frameIdentifier, List<FrameExpression/*!*/>/*!*/ frameClause,
      BoogieStmtListBuilder/*!*/ builder, Variables localVariables, string name, ExpressionTranslator/*?*/ etran = null) {
      Contract.Requires(tok != null);
      Contract.Requires(frameIdentifier != null);
      Contract.Requires(frameIdentifier.Type != null);
      Contract.Requires(Cce.NonNullElements(frameClause));
      Contract.Requires(builder != null);
      Contract.Requires(Predef != null);

      if (etran == null) {
        // This is the common case. It means that the frame will be defined in terms of the usual variable $Heap.
        // The one case where a frame is needed for a different heap is for lambda expressions, because they may
        // sit inside of an "old" expression.
        etran = new ExpressionTranslator(this, Predef, tok, null);
      }
      // Declare a local variable $_Frame: [ref, Field]bool
      var frame = localVariables.GetOrAdd(new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name ?? frameIdentifier.Name, frameIdentifier.Type)));
      // $_Frame := (lambda $o: ref, $f: Field :: $o != null && $Heap[$o,alloc] ==> ($o,$f) in Modifies/Reads-Clause);
      // $_Frame := (lambda $o: ref, $f: Field :: $o != null                    ==> ($o,$f) in Modifies/Reads-Clause);
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);
      Bpl.Expr oNotNull = Bpl.Expr.Neq(o, Predef.Null);
      Bpl.Expr ante = BplAnd(oNotNull, etran.IsAlloced(tok, o));
      Bpl.Expr consequent = InRWClause(tok, o, f, frameClause, etran, null, null);
      Bpl.Expr lambda = new Bpl.LambdaExpr(tok, [], [oVar, fVar], null,
                                           BplImp(ante, consequent));

      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, frame), lambda));
    }

    public void CheckFrameSubset(IOrigin tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable, Expression /*!*/> substMap,
                          ExpressionTranslator /*!*/ etran, Boogie.IdentifierExpr /*!*/ enclosingFrame,
                          BoogieStmtListBuilder /*!*/ builder,
                          ProofObligationDescription desc,
                          Bpl.QKeyValue kv) {
      CheckFrameSubset(tok, calleeFrame, receiverReplacement, substMap, etran, enclosingFrame,
        (t, e, d, q) => builder.Add(Assert(t, e, d, builder.Context, q)),
        (t, e) => builder.Add(TrAssumeCmd(t, e)),
        desc, kv);
    }

    void CheckFrameSubset(IOrigin tok, List<FrameExpression> calleeFrame,
                          Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/> substMap,
                          ExpressionTranslator/*!*/ etran, Boogie.IdentifierExpr /*!*/ enclosingFrame,
                          Action<IOrigin, Bpl.Expr, ProofObligationDescription, Bpl.QKeyValue> makeAssert,
                          Action<IOrigin, Bpl.Expr> makeAssume,
                          ProofObligationDescription desc,
                          Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(calleeFrame != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Requires(etran != null);
      Contract.Requires(makeAssert != null);
      Contract.Requires(Predef != null);

      foreach (var frameExpression in calleeFrame) {
        var e = substMap != null ? Substitute(frameExpression.E, receiverReplacement, substMap) : frameExpression.E;
        makeAssume(frameExpression.Origin, etran.CanCallAssumption(e));
      }

      // emit: assert (forall o: ref, f: Field :: o != null && $Heap[o,alloc] && (o,f) in subFrame ==> enclosingFrame[o,f]);
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);
      var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      var f = new Bpl.IdentifierExpr(tok, fVar);
      var ante = Bpl.Expr.And(Bpl.Expr.Neq(o, Predef.Null), etran.IsAlloced(tok, o));
      var oInCallee = InRWClause(tok, o, f, calleeFrame, etran, receiverReplacement, substMap);
      var inEnclosingFrame = Bpl.Expr.Select(enclosingFrame, o, f);

      var q = new Bpl.ForallExpr(tok, [], [oVar, fVar],
                                      BplImp(BplAnd(ante, oInCallee), inEnclosingFrame));
      if (IsExprAlways(q, true)) {
        return;
      }
      makeAssert(tok, q, desc, kv);
    }

    void CheckFrameEmpty(IOrigin tok,
                         ExpressionTranslator/*!*/ etran, Boogie.IdentifierExpr /*!*/ frame,
                         BoogieStmtListBuilder/*!*/ builder, ProofObligationDescription desc,
                         Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(frame != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);

      // emit: assert (forall o: ref, f: Field :: o != null && $Heap[o,alloc] ==> !frame[o,f]);
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);
      var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      var f = new Bpl.IdentifierExpr(tok, fVar);
      var ante = BplAnd(Bpl.Expr.Neq(o, Predef.Null), etran.IsAlloced(tok, o));
      var inFrame = Bpl.Expr.Select(frame, o, f);
      var notInFrame = Bpl.Expr.Not(inFrame);

      var q = new Bpl.ForallExpr(tok, [], [oVar, fVar],
        BplImp(ante, notInFrame));
      if (IsExprAlways(q, true)) {
        return;
      }
      builder.Add(Assert(tok, q, desc, builder.Context, kv));
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

    Bpl.Expr InRWClause(IOrigin tok, Bpl.Expr o, Bpl.Expr f, List<FrameExpression> rw, ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(Cce.NonNullElements(rw));
      Contract.Requires(substMap == null || Cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(Predef != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      return InRWClause(tok, o, f, rw, false, etran, receiverReplacement, substMap);
    }
    Bpl.Expr InRWClause(IOrigin tok, Bpl.Expr o, Bpl.Expr f, List<FrameExpression> rw, bool useInUnchanged,
                        ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(Cce.NonNullElements(rw));
      Contract.Requires(substMap == null || Cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(Predef != null);
      Contract.Requires(receiverReplacement == null || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      var boxO = Box(tok, o);
      return InRWClause_Aux(tok, o, boxO, f, rw, useInUnchanged, etran, receiverReplacement, substMap);
    }

    private NAryExpr Box(IOrigin tok, Expr o) {
      return FunctionCall(tok, BuiltinFunction.Box, null, o);
    }

    private bool ReferrersEnabled(Type elemType) {
      return Options.Get(CommonOptionBag.Referrers) && elemType.AsDatatype is TupleTypeDecl { Dims: 2 };
    }

    private bool ShouldExtractObjectFromMemoryLocation(Type elemType, Expr f) {
      return ReferrersEnabled(elemType) && f == null;
    }

    private void PairWithField(IOrigin tok, ref Expr o, ref Expr boxO, Expr f) {
      o = new NAryExpr(tok, new Bpl.FunctionCall(Predef.Tuple2Constructor), [boxO, Box(tok, f)]);
      boxO = Box(tok, o);
    }

    private bool ContainsFieldLocation(Type type) {
      return type switch {
        SetType setType => ReferrersEnabled(setType.Arg),
        SeqType seqType => ReferrersEnabled(seqType.Arg),
        MultiSetType multiSetType => ReferrersEnabled(multiSetType.Arg),
        _ => ReferrersEnabled(type)
      };
    }

    // From an expression that contains a memory location like o`f, extracts the object (first component of the tuple)
    Bpl.Expr MaybeExtractObjectFromMemoryLocation(IOrigin tok, Bpl.Expr xb, Type elemType, Bpl.Expr f, ExpressionTranslator etran) {
      if (ShouldExtractObjectFromMemoryLocation(elemType, f)) {
        return ExtractObjectFromMemoryLocation(tok, xb, elemType, etran);
      }

      return xb;
    }

    private Expr ExtractObjectFromMemoryLocation(IOrigin tok, Expr xb, Type elemType, ExpressionTranslator etran) {
      return etran.TrExpr(new MemberSelectExpr(tok, new BoogieWrapper(xb, elemType),
        program.SystemModuleManager.TupleType(tok, 2, false).Ctors[0].Destructors[0]));
    }

    private Func<Expr, Expr> ExtractObjectFromMemoryLocationCallback(IOrigin tok, Type elemType, ExpressionTranslator etran) {
      return (Expr xb) => ExtractObjectFromMemoryLocation(tok, xb, elemType, etran);
    }

    /// <summary>
    /// By taking both an "o" and a "boxO" parameter, the caller has a choice of passing in either
    /// "o, Box(o)" for some "o" or "Unbox(bx), bx" for some "bx".
    /// </summary>
    Bpl.Expr InRWClause_Aux(IOrigin tok, Bpl.Expr o, Bpl.Expr boxO, Bpl.Expr f, List<FrameExpression> rw, bool usedInUnchanged,
                        ExpressionTranslator etran,
                        Expression receiverReplacement, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(tok != null);
      Contract.Requires(o != null);
      Contract.Requires(boxO != null);
      // Contract.Requires(f != null); // f == null means approximate
      Contract.Requires(etran != null);
      Contract.Requires(Cce.NonNullElements(rw));
      Contract.Requires(substMap == null || Cce.NonNullDictionaryAndValues(substMap));
      Contract.Requires(Predef != null);
      Contract.Requires((substMap == null && receiverReplacement == null) || substMap != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // requires o to denote an expression of type RefType
      // "rw" is allowed to contain a WildcardExpr

      Bpl.Expr disjunction = Bpl.Expr.False;
      foreach (FrameExpression rwComponent in rw) {
        Expression e = rwComponent.E;
        var field = rwComponent.Field;

        if (f == null) {
          e = e switch {
            // Field granularity
            IndexFieldLocationExpression { Lhs: var lhs } => lhs,
            FieldLocationExpression { Lhs: var lhs2 } => lhs2,
            _ => e
          };
        }
        if (substMap != null) {
          e = Substitute(e, receiverReplacement, substMap);
        }

        Bpl.Expr disjunct;
        // We revert back to the previous handling for backward compatibility and avoiding triggers
        if (e is FieldLocationExpression fle && f != null) {
          Contract.Assert(rwComponent.Field == null);
          field = fle.ResolvedField;
          e = fle.Lhs;
        }
        var eType = e.Type.NormalizeToAncestorType();
        if (ContainsFieldLocation(eType) && f != null) {
          PairWithField(tok, ref o, ref boxO, f);
        }

        if (e is WildcardExpr) {
          // For /allocated:{0,1,3}, "function f(...)... reads *"
          // is more useful if "reads *" excludes unallocated references,
          // because otherwise, "reads *" lets f depend on unallocated state,
          // which means that f may change whenever any new allocation occurs,
          // which is generally undesirable.  Also, Dafny doesn't let you
          // say "reads set o :: allocated(o)", so it's hard to work around
          // this issue.
          disjunct = etran.IsAlloced(tok, o);
        } else if (eType is SetType setType) {

          // e[Box(o)]
          bool pr;
          disjunct = etran.TrInSet_Aux(tok, o, boxO, e, setType.Finite, true, out pr,
            ShouldExtractObjectFromMemoryLocation(setType.Arg, f) ? ExtractObjectFromMemoryLocationCallback(tok, setType.Arg, etran) : null);
        } else if (eType is MultiSetType multisetType) {
          // e[Box(o)] > 0
          disjunct = etran.TrInMultiSet_Aux(tok, o, boxO, e, true);
        } else if (eType is SeqType seqType) {
          // (exists i: int :: 0 <= i && i < Seq#Length(e) && Seq#Index(e,i) == Box(o))
          Bpl.Variable iVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$i", Bpl.Type.Int));
          Bpl.Expr i = new Bpl.IdentifierExpr(tok, iVar);
          Bpl.Expr iBounds = InSeqRange(tok, i, Type.Int, etran.TrExpr(e), true, null, false);
          Bpl.Expr XsubI = FunctionCall(tok, BuiltinFunction.SeqIndex, Predef.BoxType, etran.TrExpr(e), i);
          XsubI = MaybeExtractObjectFromMemoryLocation(tok, XsubI, seqType.Arg, f, etran);
          // TODO: the equality in the next line should be changed to one that understands extensionality
          //TRIG (exists $i: int :: 0 <= $i && $i < Seq#Length(read($h0, this, _module.DoublyLinkedList.Nodes)) && Seq#Index(read($h0, this, _module.DoublyLinkedList.Nodes), $i) == $Box($o))


          disjunct = new Bpl.ExistsExpr(tok, [iVar], BplAnd(iBounds, Bpl.Expr.Eq(XsubI, boxO)));  // LL_TRIGGER
        } else {
          // o == e
          disjunct = Bpl.Expr.Eq(o, MaybeExtractObjectFromMemoryLocation(tok, etran.TrExpr(e), e.Type, f, etran));
        }
        if (field != null && f != null) {
          Bpl.Expr q = Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.Origin, GetField(field)));
          if (usedInUnchanged) {
            q = BplOr(q,
              Bpl.Expr.Eq(f, new Bpl.IdentifierExpr(rwComponent.E.Origin, Predef.AllocField)));
          }
          disjunct = BplAnd(disjunct, q);
        }
        disjunction = BplOr(disjunction, disjunct);
      }
      return disjunction;
    }

    public Bpl.Expr CtorInvocation(IOrigin tok, DatatypeCtor ctor, ExpressionTranslator etran,
      Variables locals, BoogieStmtListBuilder localTypeAssumptions) {
      Contract.Requires(tok != null);
      Contract.Requires(ctor != null);
      Contract.Requires(etran != null);
      Contract.Requires(locals != null);
      Contract.Requires(localTypeAssumptions != null);
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // create local variables for the formals
      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("a#");
      var args = new List<Bpl.Expr>();
      foreach (Formal arg in ctor.Formals) {
        Contract.Assert(arg != null);
        var nm = varNameGen.FreshId(string.Format("#{0}#", args.Count));
        var bv = locals.GetOrAdd(new Bpl.LocalVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, nm, TrType(arg.Type))));
        args.Add(new Bpl.IdentifierExpr(arg.Origin, bv));
      }

      Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(tok, ctor.FullName, Predef.DatatypeType);
      return new Bpl.NAryExpr(tok, new Bpl.FunctionCall(id), args);
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
          var r = new Bpl.NAryExpr(pat.Origin, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          var de = CondApplyUnbox(pat.Origin, r, dtor.Type, arg.Expr.Type);
          AddCasePatternVarSubstitutions(arg, de, substMap);
        }
      }
    }

    void CheckCasePatternShape<VT>(CasePattern<VT> pat, Expression dRhs, Bpl.Expr rhs, IOrigin rhsTok, Type rhsType, BoogieStmtListBuilder builder)
      where VT : class, IVariable {
      Contract.Requires(pat != null);
      Contract.Requires(rhs != null);
      Contract.Requires(rhsTok != null);
      Contract.Requires(rhsType != null);
      Contract.Requires(builder != null);
      if (pat.Var != null) {
        CheckSubrange(rhsTok, rhs, rhsType, pat.Var.Type, dRhs, builder);
      } else if (pat.Arguments != null) {
        Contract.Assert(pat.Ctor != null);  // follows from successful resolution
        Contract.Assert(pat.Arguments.Count == pat.Ctor.Destructors.Count);  // follows from successful resolution
        rhsType = rhsType.Normalize();
        Contract.Assert(rhsType is UserDefinedType && ((UserDefinedType)rhsType).ResolvedClass != null);
        var rhsTypeUdt = (UserDefinedType)rhsType;
        var typeSubstMap = TypeParameter.SubstitutionMap(rhsTypeUdt.ResolvedClass.TypeArgs, rhsTypeUdt.TypeArgs);

        var ctor = pat.Ctor;
        var correctConstructor = FunctionCall(pat.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, rhs);
        if (ctor.EnclosingDatatype.Ctors.Count == 1) {
          // There is only one constructor, so the value must have been constructed by it; might as well assume that here.
          builder.Add(TrAssumeCmd(pat.Origin, correctConstructor));
        } else {
          builder.Add(Assert(pat.Origin, correctConstructor, new PatternShapeIsValid(dRhs, ctor.Name), builder.Context));
        }
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var dtor = ctor.Destructors[i];

          var r = new Bpl.NAryExpr(arg.Origin, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          Type argType = dtor.Type.Subst(typeSubstMap);
          var de = CondApplyUnbox(arg.Origin, r, dtor.Type, argType);
          CheckCasePatternShape(arg, arg.Expr, de, arg.Origin, argType, builder);
        }
      }
    }

    void CheckNonNull(IOrigin tok, Expression e, BoogieStmtListBuilder builder, ExpressionTranslator etran, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);

      if (!e.Type.IsRefType) {
        // nothing to do
      } else if (e is ThisExpr) {
        // already known to be non-null
      } else if (e is StaticReceiverExpr) {
        // also ok
      } else {
        builder.Add(Assert(tok, Bpl.Expr.Neq(etran.TrExpr(e), Predef.Null),
          new NonNull("target object", e), builder.Context, kv));
      }
    }

    void CloneVariableAsBoundVar(IOrigin tok, IVariable iv, string prefix, out BoundVar bv, out IdentifierExpr ie) {
      Contract.Requires(tok != null);
      Contract.Requires(iv != null);
      Contract.Requires(prefix != null);
      Contract.Ensures(Contract.ValueAtReturn(out bv) != null);
      Contract.Ensures(Contract.ValueAtReturn(out ie) != null);

      // use this temporary variable counter CurrentIdGenerator.FreshId(prefix), but for a Dafny name (the idea being that
      // the number and the initial "_" in the name might avoid name conflicts)
      bv = new BoundVar(tok, CurrentIdGenerator.FreshId(prefix), iv.Type, iv.IsGhost);
      ie = new IdentifierExpr(tok, bv.Name) {
        Var = bv, // resolve here
        Type = bv.Type // resolve here
      };
    }

    // Use trType to translate types in the args list
    Bpl.Expr ClassTyCon(UserDefinedType cl, List<Bpl.Expr> args) {
      Contract.Requires(cl != null);
      Contract.Requires(Cce.NonNullElements(args));
      return ClassTyCon(cl.ResolvedClass, args);
    }

    Bpl.Expr ClassTyCon(TopLevelDecl cl, List<Bpl.Expr> args) {
      Contract.Requires(cl != null);
      Contract.Requires(Cce.NonNullElements(args));
      return FunctionCall(cl.Origin, GetClassTyCon(cl), Predef.Ty, args);
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

    private Expr NewOneHeapExpr(IOrigin tok) {
      return new Bpl.IdentifierExpr(tok, "$OneHeap", Predef.HeapType);
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
    void EachReferenceInFrameExpression(Expression e, Variables locals, BoogieStmtListBuilder builder, ExpressionTranslator etran,
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

      var eType = e.Type.NormalizeToAncestorType();
      var isSetType = eType.AsSetType != null;
      var isMultisetType = eType.AsMultiSetType != null;
      Contract.Assert(isSetType || isMultisetType || eType.AsSeqType != null);
      var sType = eType.AsCollectionType;
      Contract.Assert(sType != null);
      type = sType.Arg;
      // var $x
      var name = CurrentIdGenerator.FreshId("$unchanged#x");
      var xVar = locals.GetOrAdd(new Bpl.LocalVariable(e.Origin, new Bpl.TypedIdent(e.Origin, name, isSetType || isMultisetType ? TrType(type) : Bpl.Type.Int)));
      var x = new Bpl.IdentifierExpr(e.Origin, xVar);
      // havoc $x
      builder.Add(new Bpl.HavocCmd(e.Origin, [x]));

      var s = etran.TrExpr(e);
      if (isSetType) {
        description = "set element";
        obj = x;
        antecedent = IsSetMember(e.Origin, s, BoxIfNecessary(e.Origin, x, type), eType.NormalizeToAncestorType().AsSetType.Finite);
      } else if (isMultisetType) {
        description = "multiset element";
        obj = x;
        antecedent = Boogie.Expr.Gt(MultisetMultiplicity(e.Origin, s, BoxIfNecessary(e.Origin, x, type)), Boogie.Expr.Literal(0));
      } else {
        description = "sequence element";
        obj = UnboxUnlessInherentlyBoxed(FunctionCall(e.Origin, BuiltinFunction.SeqIndex, Predef.BoxType, s, x), type);
        antecedent = InSeqRange(e.Origin, x, Type.Int, s, true, null, false);
      }
    }

    private Bpl.Expr IsSetMember(IToken tok, Bpl.Expr set, Bpl.Expr boxedElement, bool isFiniteSet) {
      if (isFiniteSet) {
        return FunctionCall(tok, BuiltinFunction.SetIsMember, null, set, boxedElement);
      } else {
        return Bpl.Expr.SelectTok(tok, set, boxedElement);
      }
    }

    private Bpl.Expr MultisetMultiplicity(IToken tok, Bpl.Expr multiset, Bpl.Expr boxedElement) {
      return FunctionCall(tok, BuiltinFunction.MultiSetMultiplicity, null, multiset, boxedElement);
    }

    private Bpl.Expr UpdateMultisetMultiplicity(IToken tok, Bpl.Expr multiset, Bpl.Expr boxedElement, Bpl.Expr newMultiplicity) {
      return FunctionCall(tok, BuiltinFunction.MultiSetUpdateMultiplicity, null, multiset, boxedElement, newMultiplicity);
    }

    private Bpl.Function GetOrCreateTypeConstructor(TopLevelDecl td) {
      if (declarationMapping.TryGetValue(td, out var result)) {
        return result;
      }

      Bpl.Function func;
      if (td is TraitDecl { IsObjectTrait: true }) {
        // the type constructor for "object" is in DafnyPrelude.bpl
        func = Predef.ObjectTypeConstructor;
      } else if (td is TupleTypeDecl ttd && ttd.Dims == 2 && ttd.NonGhostDims == 2) {
        // the type constructor for "Tuple2" is in DafnyPrelude.bpl
        func = this.Predef.Tuple2TypeConstructor;
      } else {
        var inner_name = GetClass(td).TypedIdent.Name;
        string name = "T" + inner_name;

        Bpl.Variable tyVarOut = BplFormalVar(null, Predef.Ty, false);
        var args = td.TypeArgs.ConvertAll(_ => (Bpl.Variable)BplFormalVar(null, Predef.Ty, true));
        func = new Bpl.Function(td.Origin, name, args, tyVarOut);
        sink.AddTopLevelDeclaration(func);

        if (td is AbstractTypeDecl or InternalTypeSynonymDecl) {
          // axiom (forall T0, T1, ... { T(T0, T1, T2) } :: WhereClause( T(T0, T1, T2) ));
          var argBoundVars = new List<Bpl.Variable>();
          var argExprs = td.TypeArgs.ConvertAll(ta => BplBoundVar(ta.Name, Predef.Ty, argBoundVars));
          var funcAppl = FunctionCall(td.Origin, name, Predef.Ty, argExprs);
          var characteristics = td is AbstractTypeDecl ? ((AbstractTypeDecl)td).Characteristics : ((InternalTypeSynonymDecl)td).Characteristics;
          var whereClause = GetTyWhereClause(funcAppl, characteristics);
          if (whereClause != null) {
            Bpl.Expr axiom;
            if (td.TypeArgs.Count == 0) {
              axiom = whereClause;
            } else {
              var tr = new Bpl.Trigger(td.Origin, true, new List<Bpl.Expr> { funcAppl });
              axiom = new Bpl.ForallExpr(td.Origin, [], argBoundVars, null, tr, whereClause);
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
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      if (classes.TryGetValue(cl, out var cc)) {
        Contract.Assert(cc != null);
      } else {
        var name = cl.FullSanitizedName;
        if (cl is ClassLikeDecl { NonNullTypeDecl: { } }) {
          name = name + "?";  // TODO: this doesn't seem like the best place to do this name transformation
        }
        cc = new Bpl.Constant(cl.Origin, new Bpl.TypedIdent(cl.Origin, "class." + name, Predef.ClassNameType), !cl.EnclosingModuleDefinition.IsFacade);
        classes.Add(cl, cc);
      }
      return cc;
    }

    Bpl.Constant GetFieldNameFamily(string n) {
      Contract.Requires(n != null);
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      if (fieldConstants.TryGetValue(n, out var cc)) {
        Contract.Assert(cc != null);
      } else {
        cc = new Bpl.Constant(Token.NoToken, new Bpl.TypedIdent(Token.NoToken, "field$" + n, Predef.NameFamilyType), true);
        fieldConstants.Add(n, cc);
      }
      return cc;
    }

    /// <summary>
    /// This method is expected to be called just once for each function in the program.
    /// </summary>
    Bpl.Function GetOrCreateFunction(Function f) {
      if (declarationMapping.TryGetValue(f, out var result)) {
        return result;
      }

      Contract.Requires(f != null);
      Contract.Requires(Predef != null && sink != null);

      var func = GetFunctionBoogieDefinition(f);
      sink.AddTopLevelDeclaration(func);

      sink.AddTopLevelDeclaration(GetCanCallFunction(f));

      declarationMapping[f] = func;
      return func;
    }

    private Bpl.Function GetFunctionBoogieDefinition(Function f) {
      Bpl.Function func;
      {
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f), false));
        if (f.IsFuelAware()) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$ly", Predef.LayerType), true));
        }

        if (f.IsOpaque || f.IsMadeImplicitlyOpaque(options)) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$reveal", Boogie.Type.Bool), true));
        }
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType), true));
        }
        if (f.ReadsHeap) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$heap", Predef.HeapType), true));
        }
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)), true));
        }
        foreach (var p in f.Ins) {
          formals.Add(new Bpl.Formal(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
        func = new Bpl.Function(new FromDafnyNode(f), f.FullSanitizedName, [], formals, res, "function declaration for " + f.FullName);
        if (InsertChecksums) {
          InsertChecksum(f, func);
        }
      }
      return func;
    }

    private Bpl.Function GetCanCallFunction(Function f) {
      Bpl.Function canCallF;
      {
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f), false));
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$prevHeap", Predef.HeapType), true));
        }
        if (f.ReadsHeap) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "$heap", Predef.HeapType), true));
        }
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, "this", TrReceiverType(f)), true));
        }
        foreach (var p in f.Ins) {
          formals.Add(new Bpl.Formal(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.Origin, new Bpl.TypedIdent(f.Origin, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
        canCallF = new Bpl.Function(f.Origin, f.FullSanitizedName + "#canCall", [], formals, res);
      }
      return canCallF;
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
      new() {
        { MethodTranslationKind.SpecWellformedness, "CheckWellFormed" },
        { MethodTranslationKind.Call, CallPrefix },
        { MethodTranslationKind.CoCall, "CoCall" },
        { MethodTranslationKind.Implementation, "Impl" },
        { MethodTranslationKind.OverrideCheck, "OverrideCheck" },
      };

    static string MethodName(ICodeContext m, MethodTranslationKind kind) {
      Contract.Requires(m != null);
      return $"{kindSanitizedPrefix[kind]}{NameSeparator}{m.FullSanitizedName}";
    }

    private static readonly Dictionary<MethodTranslationKind, string> kindDescription =
      new() {
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

    private static void AddVerboseNameAttribute(Bpl.NamedDeclaration boogieDecl, string dafnyName, MethodTranslationKind kind) {
      var verboseName = MethodVerboseName(dafnyName, kind);
      AddVerboseNameAttribute(boogieDecl, verboseName);
    }

    private static void AddVerboseNameAttribute(Bpl.NamedDeclaration targetDecl, string verboseName) {
      targetDecl.AddAttribute("verboseName", [verboseName]);
    }

    private static void AddSmtOptionAttribute(Bpl.NamedDeclaration targetDecl, string name, string value) {
      targetDecl.Attributes = new QKeyValue(targetDecl.tok, "smt_option", new List<object>() { name, value }, targetDecl.Attributes);
    }

    private static CallCmd Call(BodyTranslationContext context, IOrigin tok, string methodName,
      List<Expr> ins, List<Bpl.IdentifierExpr> outs) {
      Contract.Requires(tok != null);
      Contract.Requires(methodName != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);

      var call = new CallCmd(tok, methodName, ins, outs) {
        IsFree = context.AssertMode == AssertMode.Assume
      };
      // CLEMENT enable this: call.ErrorData = "possible violation of function precondition";
      return call;
    }

    private void GenerateMethodParameters(IOrigin tok, MethodOrConstructor m, MethodTranslationKind kind, ExpressionTranslator etran,
      List<Variable> inParams, out Variables outParams) {
      GenerateMethodParametersChoose(tok, m, kind, !m.IsStatic, true, true, etran, inParams, out outParams);
    }

    private void GenerateMethodParametersChoose(IOrigin tok, IMethodCodeContext m, MethodTranslationKind kind, bool includeReceiver, bool includeInParams, bool includeOutParams,
      ExpressionTranslator etran, List<Variable> inParams, out Variables outParams) {
      outParams = new Variables();
      // Add type parameters first, always!
      inParams.AddRange(MkTyParamFormals(GetTypeParams(m), true));
      if (includeReceiver) {
        var receiverType = m is MemberDecl ? ModuleResolver.GetReceiverType(tok, (MemberDecl)m) : ModuleResolver.GetThisType(tok, (IteratorDecl)m);
        Contract.Assert(VisibleInScope(receiverType));

        Bpl.Expr wh;
        var receiver = new Bpl.IdentifierExpr(tok, "this", TrType(receiverType));
        if (m is Constructor && kind is MethodTranslationKind.Implementation or MethodTranslationKind.SpecWellformedness) {
          // For constructors, the typical "where" condition is added in an assumption in the body, rather than in the parameter declaration itself
          wh = null;
        } else {
          wh = BplAnd(
            ReceiverNotNull(receiver),
            (m is TwoStateLemma ? etran.Old : etran).GoodRef(tok, receiver, receiverType));
        }
        // for class constructors, the receiver is encoded as an output parameter
        Bpl.Formal thVar = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "this", TrType(receiverType), wh),
          m is not Constructor);
        if (thVar.InComing) {
          inParams.Add(thVar);
        } else {
          outParams.GetOrAdd(thVar);
        }
      }
      if (includeInParams) {
        foreach (Formal p in m.Ins) {
          Contract.Assert(VisibleInScope(p.Type));
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetExtendedWhereClause(p.Origin,
            new Bpl.IdentifierExpr(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), varType),
            p.Type, p.IsOld ? etran.Old : etran, IsAllocContext.Var(p));
          inParams.Add(new Bpl.Formal(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), varType, wh), true));
        }
      }
      if (includeOutParams) {
        var beforeTrackers = DefiniteAssignmentTrackers;
        Contract.Assume(DefiniteAssignmentTrackers.Count == 0);
        foreach (Formal p in m.Outs) {
          Contract.Assert(VisibleInScope(p.Type));
          Contract.Assert(!p.IsOld);  // out-parameters are never old (perhaps we want to relax this condition in the future)
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetWhereClause(p.Origin,
            new Bpl.IdentifierExpr(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), varType),
            p.Type, etran, IsAllocContext.Var(p));
          if (kind == MethodTranslationKind.Implementation) {
            var tracker = AddDefiniteAssignmentTracker(p, outParams, true, m.IsGhost);
            if (wh != null && tracker != null) {
              wh = BplImp(tracker, wh);
            }
          }
          outParams.GetOrAdd(new Bpl.Formal(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(CurrentDeclaration.IdGenerator), varType, wh), false));
          DefiniteAssignmentTrackers = beforeTrackers;
        }

        if (kind == MethodTranslationKind.Implementation) {
          outParams.GetOrAdd(new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "$_reverifyPost", Bpl.Type.Bool), false));
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

      public readonly IOrigin tok;
      public readonly bool IsFree;
      public readonly Bpl.Expr Expr;
      public readonly string ErrorMessage;
      public readonly string SuccessMessage;
      public readonly string Comment;


      public BoilerplateTriple(IOrigin tok, bool isFree, Bpl.Expr expr, string errorMessage, string successMessage, string comment) {
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
    List<BoilerplateTriple/*!*/>/*!*/ GetTwoStateBoilerplate(IOrigin/*!*/ tok,
      List<FrameExpression/*!*/>/*!*/ modifiesClause, bool isGhostContext, bool canAllocate,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod) {
      Contract.Requires(tok != null);
      Contract.Requires(modifiesClause != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Cce.NonNullElements(Contract.Result<List<BoilerplateTriple>>()));

      var boilerplate = new List<BoilerplateTriple>();
      if (!canAllocate && modifiesClause.Count == 0) {
        // plain and simple:  S1 == S2
        boilerplate.Add(new BoilerplateTriple(tok, true, Bpl.Expr.Eq(etranPre.HeapExpr, etran.HeapExpr), null, null, "frame condition"));
      } else {
        bool fieldGranularity = true;
        bool objectGranularity = !fieldGranularity;
        // the frame condition, which is free since it is checked with every heap update and call
        boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, canAllocate, FrameExpressionUse.Modifies, etranPre, etran, etranMod, objectGranularity), null, null, "frame condition: object granularity"));
        if (modifiesClause.Exists(fe => fe.FieldName != null || ContainsFieldLocation(fe.E.Type))) {
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
    Bpl.Expr/*!*/ FrameCondition(IOrigin/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frame, bool canAllocate, FrameExpressionUse use,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod, bool fieldGranularity) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(Cce.NonNullElements(frame));
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // read is handled in AddFrameAxiom
      //
      // if field granularity:
      // generate:
      //  (forall o: ref, f: Field :: { $Heap[o][f] }
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
      var oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      var o = new Bpl.IdentifierExpr(tok, oVar);

      Bpl.Expr f;
      List<Variable> quantifiedVars;
      List<TypeVariable> typeVars;
      Bpl.Expr heapOF;
      Bpl.Expr preHeapOF;
      if (fieldGranularity) {
        typeVars = [];
        var fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
        f = new Bpl.IdentifierExpr(tok, fVar);
        quantifiedVars = [oVar, fVar];
        heapOF = ReadHeap(tok, etran.HeapExpr, o, f);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f);
      } else {
        // object granularity
        typeVars = [];
        f = null;
        quantifiedVars = [oVar];
        heapOF = ReadHeap(tok, etran.HeapExpr, o);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o);  // Box type is Bpl.Type.Bool, but no need to unbox for equality check
      }

      Bpl.Expr ante = Bpl.Expr.Neq(o, Predef.Null);
      if (canAllocate && use == FrameExpressionUse.Modifies) {
        ante = BplAnd(ante, etranMod.IsAlloced(tok, o));
      }
      var eq = Bpl.Expr.Eq(heapOF, preHeapOF);
      var ofInFrame = InRWClause(tok, o, f, frame, use == FrameExpressionUse.Unchanged, etranMod, null, null);
      Bpl.Expr consequent = use == FrameExpressionUse.Modifies ? BplOr(eq, ofInFrame) : BplImp(ofInFrame, eq);

      var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, typeVars, quantifiedVars, null, tr, BplImp(ante, consequent));
    }

    Bpl.Expr/*!*/ FrameConditionUsingDefinedFrame(IOrigin/*!*/ tok, ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod, Boogie.IdentifierExpr frameExpr) {
      Contract.Requires(tok != null);
      Contract.Requires(etran != null);
      Contract.Requires(etranPre != null);
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      // generate:
      //  (forall o: ref, f: Field :: { $Heap[o,f] }
      //      o != null && old($Heap)[o,alloc] ==>
      //        $Heap[o,f] == PreHeap[o,f] ||
      //        $_Frame[o,f])
      Bpl.BoundVariable oVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$o", Predef.RefType));
      Bpl.IdentifierExpr o = new Bpl.IdentifierExpr(tok, oVar);
      Bpl.BoundVariable fVar = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$f", Predef.FieldName(tok)));
      Bpl.IdentifierExpr f = new Bpl.IdentifierExpr(tok, fVar);

      Bpl.Expr heapOF = ReadHeap(tok, etran.HeapExpr, o, f);
      Bpl.Expr preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f);
      Bpl.Expr ante = BplAnd(Bpl.Expr.Neq(o, Predef.Null), etranPre.IsAlloced(tok, o));
      Bpl.Expr consequent = Bpl.Expr.Eq(heapOF, preHeapOF);

      consequent = BplOr(consequent, Bpl.Expr.SelectTok(tok, frameExpr, o, f));

      Bpl.Trigger tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, [], [oVar, fVar], null, tr, BplImp(ante, consequent));
    }
    // ----- Type ---------------------------------------------------------------------------------

    static Type NormalizeToVerificationTypeRepresentation(Type type) {
      while (true) {
        type = type.NormalizeExpand();
        if (type is TypeProxy) {
          Contract.Assume(false);  // we assume that all proxies have been dealt with in the resolver
        }
        if (type.AsNewtype is not { } newtypeDecl) {
          break;
        }
        type = newtypeDecl.RhsWithArgument(type.TypeArgs);  // the Boogie type to be used for the newtype is the same as for the base type
      }
      return type;
    }

    // Translates a type into the representation Boogie type,
    // c.f. TypeToTy which translates a type to its Boogie expression
    // to be used in $Is and $IsAlloc.
    public Bpl.Type TrType(Type type) {
      Contract.Requires(type != null);
      Contract.Requires(Predef != null);
      Contract.Ensures(Contract.Result<Bpl.Type>() != null);

      type = NormalizeToVerificationTypeRepresentation(type);

      if (type is BoolType) {
        return Bpl.Type.Bool;
      } else if (type is CharType) {
        return Predef.CharType;
      } else if (type is IntType) {
        return Bpl.Type.Int;
      } else if (type is RealType) {
        return Bpl.Type.Real;
      } else if (type is BigOrdinalType) {
        return Predef.BigOrdinalType;
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        return BplBvType(t.Width);
      } else if (type is IteratorDecl.EverIncreasingType) {
        return Bpl.Type.Int;
      } else if (type is ArrowType) {
        return Predef.HandleType;
      } else if (type.IsTypeParameter || type.IsAbstractType) {
        return Predef.BoxType;
      } else if (type.IsInternalTypeSynonym) {
        return Predef.BoxType;
      } else if (type.IsRefType) {
        // object and class types translate to ref
        return Predef.RefType;
      } else if (type is UserDefinedType { ResolvedClass: TraitDecl }) {
        // non-reference trait type
        return Predef.BoxType;
      } else if (type.IsDatatype) {
        return Predef.DatatypeType;
      } else if (type is SetType) {
        return ((SetType)type).Finite ? Predef.SetType : Predef.ISetType;
      } else if (type is MultiSetType) {
        return Predef.MultiSetType;
      } else if (type is MapType) {
        return ((MapType)type).Finite ? Predef.MapType : Predef.IMapType;
      } else if (type is SeqType) {
        return Predef.SeqType;
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected type
      }
    }

    public Bpl.Expr AdaptBoxing(Bpl.IToken tok, Bpl.Expr e, Type fromType, Type toType) {
      if (fromType.IsTypeParameter) {
        return CondApplyUnbox(tok, e, fromType, toType);
      } else {
        return CondApplyBox(tok, e, fromType, toType);
      }
    }

    public Bpl.Expr CondApplyBox(Bpl.IToken tok, Bpl.Expr e, Type fromType, Type toType) {
      Contract.Requires(tok != null);
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

      if (!ModeledAsBoxType(fromType) && (toType == null || ModeledAsBoxType(toType))) {
        // if "e" denotes "Unbox(E): T", then just return "E"
        if (e is Bpl.NAryExpr { Fun: Bpl.TypeCoercion } coerce) {
          Contract.Assert(coerce.Args.Count == 1);
          Contract.Assert(Bpl.Type.Equals(((Bpl.TypeCoercion)coerce.Fun).Type, TrType(fromType)));
          if (coerce.Args[0] is Bpl.NAryExpr { Fun: Bpl.FunctionCall { FunctionName: UnboxFunctionName } } call) {
            Contract.Assert(call.Args.Count == 1);
            return call.Args[0];
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
    public Bpl.Expr BoxIfNotNormallyBoxed(Bpl.IToken tok, Bpl.Expr e, Type t) {
      if (!ModeledAsBoxType(t)) {
        return ApplyBox(tok, e);
      } else {
        return e;
      }
    }

    /// <summary>
    ///   If the passed expression is not already boxed, box it.
    /// </summary>
    public Bpl.Expr ApplyBox(Bpl.IToken tok, Bpl.Expr e) {
      Contract.Assert(tok != null);
      Contract.Assert(e != null);
      if (e.Type == Predef.BoxType || e is NAryExpr { Fun.FunctionName: BoxFunctionName }) {
        return e;
      }
      return FunctionCall(tok, BuiltinFunction.Box, null, e);
    }

    /// <summary>
    ///   If the expression is boxed, but the type is not boxed, this unboxes it.
    ///   For lambda functions.
    /// </summary>
    public Bpl.Expr UnboxUnlessInherentlyBoxed(Bpl.Expr e, Type t) {
      if (!ModeledAsBoxType(t)) {
        return FunctionCall(e.tok, BuiltinFunction.Unbox, TrType(t), e);
      } else {
        return e;
      }
    }

    public Expr UnboxUnlessBoxType(IOrigin tok, Expr e, Type type) {
      return TrType(type) == Predef.BoxType ? e : ApplyUnbox(tok, e, TrType(type));
    }

    /// <summary>
    ///   Unboxes an expression with the Box type.
    /// </summary>
    public Bpl.Expr ApplyUnbox(Bpl.IToken tok, Bpl.Expr e, Bpl.Type ty) {
      Contract.Assert(e != null);
      Contract.Assert(ty != null);
      Contract.Assert(tok != null);
      Contract.Assert((e.Type != null && e.Type.Equals(Predef.BoxType) ||
                      (e.ShallowType != null && e.ShallowType.Equals(Predef.BoxType))));
      return FunctionCall(tok, BuiltinFunction.Unbox, ty, e);
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
      t = NormalizeToVerificationTypeRepresentation(t);
      if (t is TypeProxy) {
        // unresolved proxy
        return false;
      }
      var res = t.IsTypeParameter || (t.IsTraitType && !t.IsRefType) || t.IsAbstractType || t.IsInternalTypeSynonym;
      Contract.Assert(t.IsArrowType ? !res : true);
      return res;
    }

    /// <summary>
    /// This method returns "expr" after stripping off any type coercions and box/unbox functions.
    /// </summary>
    public static Boogie.Expr StripBoxAdjustments(Boogie.Expr expr) {
      while (expr is Boogie.NAryExpr { Fun: Boogie.FunctionCall { FunctionName: BoxFunctionName or UnboxFunctionName } or Boogie.TypeCoercion } nAryExpr) {
        Contract.Assert(nAryExpr.Args.Count == 1);
        expr = nAryExpr.Args[0];
      }
      return expr;
    }

    // ----- Statement ----------------------------------------------------------------------------

    /// <summary>
    /// A ForceCheckToken is a token wrapper whose purpose is to hide inheritance.
    /// </summary>
    public class ForceCheckOrigin : OriginWrapper {
      public ForceCheckOrigin(IOrigin tok)
        : base(tok) {
        Contract.Requires(tok != null);
      }
      public static IOrigin Unwrap(IOrigin tok) {
        Contract.Requires(tok != null);
        Contract.Ensures(Contract.Result<IOrigin>() != null);
        var ftok = tok as ForceCheckOrigin;
        return ftok != null ? ftok.WrappedOrigin : tok;
      }

      public override bool IsInherited(ModuleDefinition m) {
        return false;
      }
    }

    public Bpl.PredicateCmd Assert(IOrigin tok, Bpl.Expr condition, ProofObligationDescription description,
      BodyTranslationContext context, Bpl.QKeyValue kv = null) {
      return Assert(tok, condition, description, tok, context, kv);
    }

    private PredicateCmd Assert(IOrigin tok, Expr condition, ProofObligationDescription description,
      IOrigin refinesToken, BodyTranslationContext context, QKeyValue kv = null) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      Bpl.PredicateCmd cmd;
      if (context.AssertMode == AssertMode.Assume
          || (assertionOnlyFilter != null && !assertionOnlyFilter(tok.ReportingRange.StartToken))
          || (refinesToken.IsInherited(currentModule) && codeContext is not { MustReverify: true })) {
        // produce an assume instead
        cmd = TrAssumeCmd(tok, condition, kv);
        proofDependencies?.AddProofDependencyId(cmd, tok, new AssumedProofObligationDependency(tok, description));
      } else {
        cmd = TrAssertCmdDesc(ForceCheckOrigin.Unwrap(tok), condition, description, kv);
        proofDependencies?.AddProofDependencyId(cmd, tok, new ProofObligationDependency(tok, description));
      }
      return cmd;
    }

    PredicateCmd AssertAndForget(BodyTranslationContext context, IOrigin tok, Bpl.Expr condition, ProofObligationDescription desc) {
      return AssertAndForget(context, tok, condition, desc, tok, null);
    }

    PredicateCmd AssertAndForget(BodyTranslationContext context, IOrigin tok, Bpl.Expr condition, ProofObligationDescription desc, IOrigin refinesTok, Bpl.QKeyValue kv) {
      Contract.Requires(tok != null);
      Contract.Requires(desc != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.PredicateCmd>() != null);

      PredicateCmd cmd;
      if (context.AssertMode == AssertMode.Assume ||
          (assertionOnlyFilter != null && !assertionOnlyFilter(tok.ReportingRange.StartToken)) ||
          (refinesTok.IsInherited(currentModule) && (codeContext == null || !codeContext.MustReverify))) {
        // produce a "skip" instead
        cmd = TrAssumeCmd(tok, Bpl.Expr.True, kv);
      } else {
        tok = ForceCheckOrigin.Unwrap(tok);
        var args = new List<object>();
        args.Add(Bpl.Expr.Literal(0));
        cmd = TrAssertCmdDesc(tok, condition, desc, new Bpl.QKeyValue(tok, "subsumption", args, kv));
        proofDependencies?.AddProofDependencyId(cmd, tok, new ProofObligationDependency(tok, desc));
      }

      return cmd;
    }

    Bpl.Ensures EnsuresWithDependencies(IOrigin tok, bool free, Expression dafnyCondition, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(dafnyCondition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var ens = Ensures(tok, free, dafnyCondition, condition, errorMessage, successMessage, comment);
      proofDependencies?.AddProofDependencyId(ens, tok, new EnsuresDependency(tok, dafnyCondition));
      return ens;
    }
    Bpl.Ensures FreeEnsures(IOrigin tok, Bpl.Expr condition, string comment, bool alwaysAssume = false) {
      var kv = alwaysAssume ? AlwaysAssumeAttribute(tok) : null;
      return Ensures(tok, true, null, condition, null, null, comment, kv);
    }


    Bpl.Ensures Ensures(IOrigin tok, bool free, Expression dafnyCondition, Bpl.Expr condition, string errorMessage, string successMessage, string comment, QKeyValue kv = null) {
      Contract.Requires(tok != null);
      Contract.Requires(condition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var unwrappedToken = ForceCheckOrigin.Unwrap(tok);
      Bpl.Ensures ens = new Bpl.Ensures(unwrappedToken, free, condition, comment, kv);
      var description = new EnsuresDescription(dafnyCondition, errorMessage, successMessage);
      ens.Description = description;
      if (!free) {
        ReportAssertion(unwrappedToken, description);
      }
      return ens;
    }

    Bpl.Requires RequiresWithDependencies(IOrigin tok, bool free, Expression dafnyCondition, Bpl.Expr condition, string errorMessage, string successMessage, string comment) {
      Contract.Requires(tok != null);
      Contract.Requires(dafnyCondition != null);
      Contract.Ensures(Contract.Result<Bpl.Ensures>() != null);

      var req = Requires(tok, free, dafnyCondition, condition, errorMessage, successMessage, comment);
      proofDependencies?.AddProofDependencyId(req, tok, new RequiresDependency(tok, dafnyCondition));
      return req;
    }
    Bpl.Requires FreeRequires(IOrigin tok, Bpl.Expr bCondition, string comment, bool alwaysAssume = false) {
      var kv = alwaysAssume ? AlwaysAssumeAttribute(tok) : null;
      return Requires(tok, true, null, bCondition, null, null, comment, kv);
    }

    Bpl.Requires Requires(IOrigin tok, bool free, Expression dafnyCondition, Bpl.Expr bCondition, string errorMessage, string successMessage, string comment, QKeyValue kv = null) {
      Contract.Requires(tok != null);
      Contract.Requires(bCondition != null);
      Contract.Ensures(Contract.Result<Bpl.Requires>() != null);
      Bpl.Requires req = new Bpl.Requires(ForceCheckOrigin.Unwrap(tok), free, bCondition, comment, kv);
      req.Description = new RequiresDescription(dafnyCondition, errorMessage, successMessage);
      return req;
    }

    public Bpl.StmtList TrStmt2StmtList(BoogieStmtListBuilder builder,
      Statement block, Variables locals, ExpressionTranslator etran, bool introduceScope = false) {
      Contract.Requires(builder != null);
      Contract.Requires(block != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && Predef != null);
      Contract.Ensures(Contract.Result<Bpl.StmtList>() != null);

      TrStmtList([block], builder, locals, etran, introduceScope ? block.EntireRange : null, processLabels: false);
      return builder.Collect(block.StartToken);  // TODO: would be nice to have an end-curly location for "block"
    }

    /// <summary>
    /// Add to "builder" the following:
    ///     if (*) { S ; assume false; }
    /// where "S" is the given "builderToCollect".  This method consumes what has been built up in "builderToCollect".
    /// </summary>
    public void PathAsideBlock(IOrigin tok, BoogieStmtListBuilder builderToCollect, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(builderToCollect != null);
      Contract.Requires(builderToCollect != null);

      if (!builderToCollect.Commands.Any()) {
        return;
      }
      builderToCollect.Add(new AssumeCmd(tok, Bpl.Expr.False));
      var ifCmd = new IfCmd(tok, null, builderToCollect.Collect(tok), null, null);
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
    Bpl.AssertCmd TrAssertCmd(IOrigin tok, Bpl.Expr expr, Bpl.QKeyValue attributes = null) {
      // TODO: move the following comment once this method disappears

      // It may be that "expr" is a Lit expression. It might seem we don't need a Lit expression
      // around the boolean expression that is being asserted. However, we keep it. For one,
      // it doesn't change the semantics of the assert command. More importantly, leaving
      // a Lit around the expression is useful to avoid sending an "assert false;" to Boogie--since
      // Boogie looks especially for "assert false;" commands and processes them in such a way
      // that loops no longer are loops (which is confusing for Dafny users).
      return attributes == null ? new Bpl.AssertCmd(tok, expr) : new Bpl.AssertCmd(tok, expr, attributes);
    }

    Bpl.AssertCmd TrAssertCmdDesc(IOrigin tok, Bpl.Expr expr,
      ProofObligationDescription description, Bpl.QKeyValue attributes = null) {
      ReportAssertion(tok, description);
      return new Bpl.AssertCmd(tok, expr, description, attributes);
    }

    private ISet<(Uri, int)> reportedAssertions = new HashSet<(Uri, int)>();
    private void ReportAssertion(IOrigin tok, ProofObligationDescription description) {
      if (!reportedAssertions.Add((tok.Uri, tok.pos))) {
        return;
      }

      if (options.Get(CommonOptionBag.ShowAssertions) > CommonOptionBag.AssertionShowMode.None && description.IsImplicit) {
        reporter.Info(MessageSource.Translator, ToDafnyToken(tok), "Implicit assertion: " + description.ShortDescription, "isAssertion");
      } else if (options.Get(CommonOptionBag.ShowAssertions) == CommonOptionBag.AssertionShowMode.All) {
        reporter.Info(MessageSource.Translator, ToDafnyToken(tok), "Explicit assertion: " + description.ShortDescription, "isAssertion");
      }
    }

    delegate void BodyTranslator(BoogieStmtListBuilder builder, ExpressionTranslator etr);

    List<Bpl.Expr> TrTypeArgs(Dictionary<TypeParameter, Type> tySubst, List<TypeParameter> tyArgs) {
      var res = new List<Bpl.Expr>();
      foreach (var p in tyArgs) {
        res.Add(TypeToTy(tySubst[p]));
      }
      return res;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, out Bpl.Expr typeAntecedent,
      BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran,
      string nameSuffix = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.ValueAtReturn(out typeAntecedent) != null);

      typeAntecedent = Bpl.Expr.True;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (BoundVar bv in boundVars) {
        LocalVariable local = new LocalVariable(bv.Origin, nameSuffix == null ? bv.Name : bv.Name + nameSuffix, bv.Type, bv.IsGhost);
        local.type = local.SafeSyntacticType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(bv, ie);
        Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Origin, new Bpl.TypedIdent(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(local.Type)));
        locals.GetOrAdd(bvar);
        var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
        builder.Add(new Bpl.HavocCmd(bv.Origin, [bIe]));
        Bpl.Expr wh = GetWhereClause(bv.Origin, bIe, local.Type, etran, IsAllocType.ISALLOC);
        if (wh != null) {
          typeAntecedent = BplAnd(typeAntecedent, wh);
        }
      }
      return substMap;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, BoogieStmtListBuilder builder,
      Variables locals, ExpressionTranslator etran,
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
      BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran) {
      Contract.Requires(v != null);
      Contract.Requires(substMap != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var local = new LocalVariable(v.Origin, v.Name, v.Type, v.IsGhost);
      local.type = local.SafeSyntacticType;  // resolve local here
      var ie = new IdentifierExpr(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator));
      ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
      substMap.Add(v, ie);

      var bvar = new Bpl.LocalVariable(local.Origin, new Bpl.TypedIdent(local.Origin, local.AssignUniqueName(CurrentDeclaration.IdGenerator), TrType(local.Type)));
      locals.GetOrAdd(bvar);
      var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
      builder.Add(new Bpl.HavocCmd(v.Origin, [bIe]));
      var wh = GetWhereClause(v.Origin, bIe, local.Type, etran, ISALLOC);
      return wh ?? Bpl.Expr.True;
    }

    List<Bpl.Expr> RecordDecreasesValue(List<Expression> decreases, BoogieStmtListBuilder builder, Variables locals, ExpressionTranslator etran, string varPrefix) {
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(varPrefix != null);
      Contract.Requires(builder != null);
      Contract.Requires(decreases != null);
      List<Bpl.Expr> oldBfs = [];
      var idGen = new VerificationIdGenerator();
      foreach (Expression e in decreases) {
        Contract.Assert(e != null);
        Bpl.LocalVariable bfVar = new Bpl.LocalVariable(e.Origin, new Bpl.TypedIdent(e.Origin, idGen.FreshId(varPrefix), TrType(Cce.NonNull(e.Type))));
        locals.GetOrAdd(bfVar);
        Bpl.IdentifierExpr bf = new Bpl.IdentifierExpr(e.Origin, bfVar);
        oldBfs.Add(bf);
        // record value of each decreases expression at beginning of the loop iteration
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(e.Origin, bf, etran.TrExpr(e));
        builder.Add(cmd);
      }
      return oldBfs;
    }


    public static void AddComment(BoogieStmtListBuilder builder, Statement stmt, string comment) {
      Contract.Requires(builder != null);
      Contract.Requires(stmt != null);
      Contract.Requires(comment != null);
      builder.Add(new Bpl.CommentCmd(string.Format("----- {0} ----- {1}({2},{3})", comment, stmt.Origin.Filepath, stmt.Origin.line, stmt.Origin.col)));
    }

    /// <summary>
    /// Therefore, these properties are applied to method in-parameters.
    /// For now, this only allows you to case split on incoming data type values.
    /// This used to add IsGood[Multi]Set_Extendend, but that is always
    /// added for sets & multisets now in the prelude.
    /// </summary>
    Bpl.Expr GetExtendedWhereClause(IOrigin tok, Bpl.Expr x, Type type, ExpressionTranslator etran, IsAllocType alloc) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);
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
        return FunctionCall(Token.NoToken, finite ? "TSet" : "TISet", Predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MultiSetType) {
        return FunctionCall(Token.NoToken, "TMultiSet", Predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is SeqType) {
        return FunctionCall(Token.NoToken, "TSeq", Predef.Ty, TypeToTy(((CollectionType)type).Arg));
      } else if (type is MapType) {
        bool finite = ((MapType)type).Finite;
        return FunctionCall(Token.NoToken, finite ? "TMap" : "TIMap", Predef.Ty,
          TypeToTy(((MapType)type).Domain),
          TypeToTy(((MapType)type).Range));
      } else if (type is BoolType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TBool", Predef.Ty);
      } else if (type is CharType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TChar", Predef.Ty);
      } else if (type is RealType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TReal", Predef.Ty);
      } else if (type is BitvectorType) {
        var t = (BitvectorType)type;
        return FunctionCall(Token.NoToken, "TBitvector", Predef.Ty, Bpl.Expr.Literal(t.Width));
      } else if (type is IntType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TInt", Predef.Ty);
      } else if (type is BigOrdinalType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TORDINAL", Predef.Ty);
      } else if (type is ParamTypeProxy) {
        return TrTypeParameter(((ParamTypeProxy)type).orig);
      } else if (type is FieldType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TField", Predef.Ty);
      } else {
        Contract.Assert(false); throw new Cce.UnreachableException();  // unexpected type
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
      return new Bpl.IdentifierExpr(tp.Origin, nm, Predef.Ty);
    }

    Bpl.Expr TrAbstractType(AbstractTypeDecl abstractType, List<Type> tyArguments) {
      Contract.Requires(tyArguments != null);

      var fn = GetOrCreateTypeConstructor(abstractType);
      var args = tyArguments.ConvertAll(TypeToTy);
      return FunctionCall(abstractType.Origin, fn.Name, Predef.Ty, args);
    }

    public List<TypeParameter> GetTypeParams(IMethodCodeContext cc) {
      if (cc is MethodOrConstructor methodOrConstructor) {
        return Concat(GetTypeParams(methodOrConstructor.EnclosingClass), methodOrConstructor.TypeArgs);
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
    Bpl.Expr MkIs(Bpl.Expr x, Type t, Bpl.IToken tok = null) {
      return MkIs(x, TypeToTy(t), ModeledAsBoxType(t), tok);
    }

    Bpl.Expr MkIs(Bpl.Expr x, Bpl.Expr t, bool box = false, Bpl.IToken tok = null) {
      if (box) {
        return FunctionCall(tok ?? x.tok, BuiltinFunction.IsBox, null, x, t);
      } else {
        return FunctionCall(tok ?? x.tok, BuiltinFunction.Is, null, x, t);
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
    public Bpl.Expr GetWhereClause(IOrigin tok, Bpl.Expr x, Type type, ExpressionTranslator etran, IsAllocType alloc,
      bool allocatednessOnly = false, bool alwaysUseSymbolicName = false) {
      Contract.Requires(tok != null);
      Contract.Requires(x != null);
      Contract.Requires(type != null);
      Contract.Requires(etran != null);
      Contract.Requires(Predef != null);

      if (type.NormalizeExpand() is TypeProxy) {
        // Unresolved proxy
        // Omit where clause (in other places, unresolved proxies are treated as a reference type; we could do that here too, but
        // we might as well leave out the where clause altogether).
        return null;
      }

      var normType = type.NormalizeExpandKeepConstraints();
      var verificationType = NormalizeToVerificationTypeRepresentation(type);
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
      } else if (normType is BoolType or IntType or RealType or BigOrdinalType) {
        // nothing to do
      } else if (normType is BitvectorType) {
        var t = (BitvectorType)normType;
        if (t.Width == 0) {
          // type bv0 has only one value
          return Bpl.Expr.Eq(BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, t), x);
        }
      } else if ((normType.AsTypeSynonym != null || normType.AsNewtype != null) &&
        (verificationType.IsNumericBased() || verificationType.IsBitVectorType || verificationType.IsBoolType)) {
        var constraint = ModuleResolver.GetImpliedTypeConstraint(new BoogieWrapper(x, normType), normType);
        isPred = etran.TrExpr(constraint);
      } else {
        // go for the symbolic name
        isPred = MkIs(x, normType);
      }
      return isAlloc == null ? isPred : isPred == null ? isAlloc : BplAnd(isPred, isAlloc);
    }

    // Returns expressions, which, if false, means that the two LHS expressions are
    // not distinct; if null then the LHSs are trivially distinct
    void CheckDistinctness(Expression lhsa, Expression lhsb, ExpressionTranslator etran, out Expression dExpr, out Bpl.Expr bExpr) {
      // Helper functions to make the following more concise
      Expression DfyBin(BinaryExpr.Opcode op, Expression e0, Expression e1) =>
        new BinaryExpr(Token.NoToken, op, e0, e1);
      Expression DfyOr(Expression e0, Expression e1) => DfyBin(BinaryExpr.Opcode.Or, e0, e1);
      Expression DfyNeq(Expression e0, Expression e1) => DfyBin(BinaryExpr.Opcode.Neq, e0, e1);
      Expression DfyLe(Expression e0, Expression e1) => DfyBin(BinaryExpr.Opcode.Le, e0, e1);
      Expression DfyLt(Expression e0, Expression e1) => DfyBin(BinaryExpr.Opcode.Lt, e0, e1);

      {
        dExpr = null;
        bExpr = null;
        if (lhsa is IdentifierExpr iea && lhsb is IdentifierExpr ieb) {
          if (iea.Name != ieb.Name) {
            return;
          }

          dExpr = new LiteralExpr(Token.NoToken, false);
          bExpr = Bpl.Expr.False;
          return;
        }
      }
      {
        if (lhsa is MemberSelectExpr iea && lhsb is MemberSelectExpr ieb) {
          if (iea.Member is Field fa && ieb.Member is Field fb) {
            if (fa != fb) {
              return;
            }

            dExpr = DfyNeq(iea.Obj, ieb.Obj);
            bExpr = Bpl.Expr.Neq(etran.TrExpr(iea.Obj), etran.TrExpr(ieb.Obj));
            return;
          }
        }
      }
      {
        if (lhsa is SeqSelectExpr iea && lhsb is SeqSelectExpr ieb) {
          dExpr = DfyNeq(iea.Seq, ieb.Seq);
          bExpr = Bpl.Expr.Neq(etran.TrExpr(iea.Seq), etran.TrExpr(ieb.Seq));

          if (iea.E1 == null && ieb.E1 == null) {
            dExpr = DfyOr(dExpr, DfyNeq(iea.E0, ieb.E0));
            bExpr = BplOr(bExpr, Bpl.Expr.Neq(etran.TrExpr(iea.E0), etran.TrExpr(ieb.E0)));
          } else if (iea.E1 == null && ieb.E1 != null) {
            dExpr = DfyOr(dExpr, DfyLe(ieb.E1, iea.E0));
            dExpr = DfyOr(dExpr, DfyLt(iea.E0, ieb.E0));
            bExpr = BplOr(bExpr, Bpl.Expr.Le(etran.TrExpr(ieb.E1), etran.TrExpr(iea.E0)));
            bExpr = BplOr(bExpr, Bpl.Expr.Lt(etran.TrExpr(iea.E0), etran.TrExpr(ieb.E0)));
          } else if (iea.E1 != null && ieb.E1 == null) {
            dExpr = DfyOr(dExpr, DfyLe(iea.E1, ieb.E0));
            dExpr = DfyOr(dExpr, DfyLt(ieb.E0, iea.E0));
            bExpr = BplOr(bExpr, Bpl.Expr.Le(etran.TrExpr(iea.E1), etran.TrExpr(ieb.E0)));
            bExpr = BplOr(bExpr, Bpl.Expr.Lt(etran.TrExpr(ieb.E0), etran.TrExpr(iea.E0)));
          } else {
            dExpr = DfyOr(dExpr, DfyLe(iea.E1, ieb.E0));
            dExpr = DfyOr(dExpr, DfyLe(ieb.E1, iea.E0));
            bExpr = BplOr(bExpr, Bpl.Expr.Le(etran.TrExpr(iea.E1), etran.TrExpr(ieb.E0)));
            bExpr = BplOr(bExpr, Bpl.Expr.Le(etran.TrExpr(ieb.E1), etran.TrExpr(iea.E0)));
          }

          return;
        }
      }
      {
        if (lhsa is MultiSelectExpr iea && lhsb is MultiSelectExpr ieb && iea.Indices.Count == ieb.Indices.Count) {
          dExpr = DfyNeq(iea.Array, ieb.Array);
          bExpr = Bpl.Expr.Neq(etran.TrExpr(iea.Array), etran.TrExpr(ieb.Array));
          for (int i = 0; i < iea.Indices.Count; i++) {
            dExpr = DfyOr(dExpr, DfyNeq(iea.Indices[i], ieb.Indices[i]));
            bExpr = BplOr(bExpr, Bpl.Expr.Neq(etran.TrExpr(iea.Indices[i]), etran.TrExpr(ieb.Indices[i])));
          }
        }
      }
    }

    /// <summary>
    /// Returns the name of the local variable used as a stand-in for a field in the BodyInit part of a divided
    /// constructor body.
    /// </summary>
    string SurrogateName(Field field) {
      Contract.Requires(field != null);
      return "this." + field.Name;
    }

    // Surrounds the given subrange-check expression with necessary context (e.g. quantifier bounds)
    public delegate Expression SubrangeCheckContext(Expression check);

    Bpl.Expr GetSubrangeCheck(
      Bpl.IToken tok,
      Bpl.Expr bSource, Type sourceType, Type targetType,
      // allow null for checked expressions that cannot necessarily be named without side effects, such as method out-params
      [CanBeNull] Expression source,
      [CanBeNull] SubrangeCheckContext context,
      out ProofObligationDescription desc, string errorMessagePrefix = "") {
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
        cre = MkIs(BoxIfNecessary(bSource.tok, bSource, sourceType), TypeToTy(targetType), true, tok);
      } else if (ModeledAsBoxType(sourceType)) {
        cre = MkIs(bSource, TypeToTy(targetType), true, tok);
      } else if (targetType is UserDefinedType targetUdt) {
        cre = MkIs(BoxifyForTraitParent(bSource.tok, bSource, udt.ResolvedClass, sourceType), targetType, tok);
      } else {
        cre = MkIs(bSource, targetType, tok);
      }

      Expression dafnyCheck = null;
      context ??= (e => e);
      if (source != null) {
        dafnyCheck = context(new TypeTestExpr(source.Origin, source, targetType));
      }
      // type checks of the form `f is T -> U` are only available in the refreshed type system
      var canTestFunctionTypes = options.Get(CommonOptionBag.TypeSystemRefresh);

      if (udt != null && udt.IsRefType) {
        var s = sourceType.NormalizeExpandKeepConstraints();
        var certain = false;
        string cause = null;
        if (s is UserDefinedType sudt && udt.ResolvedClass is NonNullTypeDecl nntd && nntd.Class == sudt.ResolvedClass) {
          certain = udt.ResolvedClass.TypeArgs.Count == 0;
          cause = "it may be null";
        }
        desc = new SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), false, certain, cause, dafnyCheck);
      } else if (udt != null && ArrowType.IsTotalArrowTypeName(udt.Name)) {
        desc = new SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), true, false,
          "it may be partial or have read effects",
          canTestFunctionTypes ? dafnyCheck : null
        );
      } else if (udt != null && ArrowType.IsPartialArrowTypeName(udt.Name)) {
        desc = new SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(), true, false,
          "it may have read effects",
          canTestFunctionTypes ? dafnyCheck : null
        );
      } else {
        var isSubset = targetType.NormalizeExpandKeepConstraints() is UserDefinedType {
          ResolvedClass: SubsetTypeDecl or NewtypeDecl { Var: { } }
        };
        desc = new SubrangeCheck(errorMessagePrefix, sourceType.ToString(), targetType.ToString(),
          isSubset, false, null, dafnyCheck);
      }
      return cre;
    }

    public void CheckSubrange(IOrigin tok, Bpl.Expr bSource, Type sourceType, Type targetType,
      Expression source, BoogieStmtListBuilder builder, string errorMsgPrefix = "") {
      Contract.Requires(tok != null);
      Contract.Requires(bSource != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(targetType != null);
      Contract.Requires(builder != null);

      var cre = GetSubrangeCheck(tok, bSource, sourceType, targetType, source, null, out var desc, errorMsgPrefix);
      if (cre != null) {
        builder.Add(Assert(tok, cre, desc, builder.Context));
      }
    }

    void Check_NewRestrictions(IOrigin tok, Expression dObj, Bpl.Expr obj, Field f, Bpl.Expr rhs, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
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
        var subset = FunctionCall(tok, BuiltinFunction.SetSubset, null, rhs,
          ApplyUnbox(tok, ReadHeap(tok, etran.HeapExpr, obj, fId), Predef.SetType));
        builder.Add(Assert(tok, subset, new AssignmentShrinks(dObj, f.Name), builder.Context));
      }
    }

    Bpl.AssumeCmd AssumeGoodHeap(IOrigin tok, ExpressionTranslator etran) {
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
        mc.ProjectionFunctions = [];
        foreach (var bv in mc.BoundVars) {
          var arg = BplFormalVar(null, TrType(mc.TermLeft.Type), false);
          var res = BplFormalVar(null, TrType(bv.Type), true);
          var projectFn = new Bpl.Function(mc.Origin, varNameGen.FreshId(string.Format("#{0}#", bv.Name)), [arg], res);
          mc.ProjectionFunctions.Add(projectFn);
          sink.AddTopLevelDeclaration(projectFn);
        }
      }
    }

    int projectionFunctionCount = 0;
    public Declaration CurrentDeclaration { get; set; }

    // ----- Expression ---------------------------------------------------------------------------

    /// <summary>
    /// This class gives a way to represent a Boogie translation target as if it were still a Dafny expression.
    /// </summary>
    internal class BoogieWrapper : Expression {
      public readonly Bpl.Expr Expr;

      public BoogieWrapper(Bpl.Expr expr, Type type)
        : base(ToDafnyToken(expr.tok)) {
        Contract.Requires(expr != null);
        Contract.Requires(type != null);
        Expr = expr;
        Type = type;  // resolve immediately
      }
    }

    internal class BoogieFunctionCall : Expression {
      public readonly string FunctionName;
      public readonly bool UsesHeap;
      public readonly bool UsesOldHeap;
      public readonly List<Label> HeapAtLabels;
      public readonly List<Type> TyArgs; // Note: also has a bunch of type arguments
      public readonly List<Expression> Args;
      public BoogieFunctionCall(IOrigin origin, string functionName, bool usesHeap, bool usesOldHeap, List<Label> heapAtLabels, List<Expression> args, List<Type> tyArgs)
        : base(origin) {
        Contract.Requires(origin != null);
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

      public SubstLetExpr(IOrigin origin, List<CasePattern<BoundVar>> lhss, List<Expression> rhss, Expression body, bool exact,
         LetExpr orgExpr, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap, List<BoundedPool>/*?*/ constraintBounds)
        : base(origin, lhss, rhss, body, exact) {
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
        Bpl.Constant moreFuel = new Bpl.Constant(f.Origin, new Bpl.TypedIdent(f.Origin, uniqueId, predef.LayerType), false);
        sink.AddTopLevelDeclaration(moreFuel);
        Bpl.Expr moreFuel_expr = new Bpl.IdentifierExpr(f.Origin, moreFuel);
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
        return new Bpl.IdentifierExpr(Token.NoToken, "$LZ", boogieGenerator.Predef.LayerType);
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
      public static FuelContext ExpandFuelContext(Attributes attribs, IOrigin tok, FuelContext oldFuelContext, ErrorReporter reporter) {
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

    private bool DisableNonLinearArithmetic => DetermineDisableNonLinearArithmetic(forModule, options);
    private int ArithmeticSolver {
      get {
        var arithmeticSolver = Attributes.Find(forModule.Attributes, "z3ArithmeticSolver");

        // The value 2 tends to lead to the best all-around arithmetic
        // performance, though some programs can be verified more quickly
        // (or verified at all) using a different solver.
        // https://microsoft.github.io/z3guide/programming/Parameters/
        var defaultSolver = 2;
        if (arithmeticSolver == null) {
          return defaultSolver;
        }

        var arg = arithmeticSolver.Args.Count > 0 ? arithmeticSolver.Args[0] : null;
        if (arg == null) {
          return defaultSolver;
        }

        if (!Expression.IsIntLiteral(arg, out var value)) {
          return 0;
        }
        try {
          return (int)value;
        } catch (OverflowException) {
          return defaultSolver;
        }
      }
    }

    public static bool DetermineDisableNonLinearArithmetic(ModuleDefinition module, DafnyOptions dafnyOptions) {
      var nlaAttribute = Attributes.Find(module.Attributes, "disableNonlinearArithmetic");
      if (nlaAttribute != null) {
        var value = true;
        var arg = nlaAttribute.Args.Count > 0 ? nlaAttribute.Args[0] : null;
        if (arg != null) {
          Expression.IsBoolLiteral(arg, out value);
        }

        return value;
      }

      return dafnyOptions.DisableNLarith;
    }

    /// <summary>
    /// Return the conjuncts of "attributedExpressions".
    /// </summary>
    public static IEnumerable<AttributedExpression> ConjunctsOf(List<AttributedExpression> attributedExpressions) {
      foreach (var attrExpr in attributedExpressions) {
        if (attrExpr.Label != null) {
          // don't mess with labeled expressions
          yield return attrExpr;
        } else {
          foreach (var conjunct in Expression.ConjunctsWithLetsOnOutside(attrExpr.E)) {
            yield return new AttributedExpression(conjunct, attrExpr.Attributes);
          }
        }
      }
    }

    List<SplitExprInfo> /*!*/ TrSplitExpr(BodyTranslationContext context, Expression expr, ExpressionTranslator etran, bool applyInduction,
      out bool splitHappened) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      splitHappened = TrSplitExpr(context, expr, splits, true, int.MaxValue, applyInduction, etran);
      return splits;
    }

    List<SplitExprInfo> TrSplitExprForMethodSpec(BodyTranslationContext context, Expression expr, ExpressionTranslator etran, MethodTranslationKind kind) {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      var applyInduction = kind == MethodTranslationKind.Implementation;
      TrSplitExpr(context, expr, splits, true, int.MaxValue, applyInduction, etran);
      return splits;
    }

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IOrigin tok, Dictionary<IVariable, Expression> substMap = null,
      List<BoundVar> keepOnlyThoseTermsThatMentionTheseVariables = null) {
      Contract.Requires(etran != null);
      Contract.Requires(tok != null);
      var argsEtran = etran.WithNoLits();
      Bpl.Trigger tr = null;
      foreach (var trigger in attribs.AsEnumerable().Where(aa => aa.Name == "trigger").Select(aa => aa.Args)) {
        List<Bpl.Expr> tt = [];
        foreach (var arg in trigger) {
          var term = substMap == null ? arg : Substitute(arg, null, substMap);
          if (keepOnlyThoseTermsThatMentionTheseVariables == null ||
              keepOnlyThoseTermsThatMentionTheseVariables.Exists(boundVariable =>
                FreeVariablesUtil.ContainsFreeVariable(term, false, boundVariable))) {
            tt.Add(StripBoxAdjustments(argsEtran.TrExpr(term)));
          }
        }

        if (tt.Count != 0) {
          tr = new Bpl.Trigger(tok, true, tt, tr);
        }
      }
      return tr;
    }

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IOrigin tok, List<Variable> bvars, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap) {
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
        var heapExpr = BplBoundVar(CurrentIdGenerator.FreshId("tr$heap#"), Predef.HeapType, bvars);
        argsEtran = new ExpressionTranslator(argsEtran, heapExpr);
      }

      // now translate it with the correct layer and heapExpr
      foreach (var trigger in attribs.AsEnumerable().Where(aa => aa.Name == "trigger")) {
        List<Bpl.Expr> tt = [];
        foreach (var arg in trigger.Args) {
          Bpl.Expr term;
          if (substMap == null) {
            term = argsEtran.TrExpr(arg);
          } else {
            term = argsEtran.TrExpr(Substitute(arg, null, substMap, typeMap));
          }
          tt.Add(StripBoxAdjustments(term));
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
      return expr.Origin.IsInherited(currentModule) && (codeContext == null || !codeContext.MustReverify) && RefinementTransformer.ContainsChange(expr, currentModule);
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
        return [];  // don't apply induction
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
      Contract.Requires(Cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new Substituter(receiverReplacement, substMap, typeMap ?? new Dictionary<TypeParameter, Type>(), oldLabel);
      return s.Substitute(expr);
    }

    public static Attributes SubstituteAttributes(Attributes attributes, Dictionary<IVariable, Expression> substMap) {
      var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
      return s.SubstAttributes(attributes);
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
      return BplOr(
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
      public readonly HashSet<string> Names = [];
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
      exprs = [];
      foreach (TypeParameter v in args) {
        vars.Add(BplBoundVar(NameTypeParam(v), Predef.Ty, out var e));
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
      exprs = [];
      foreach (TypeParameter v in args) {
        var whereClause = includeWhereClause ? GetTyWhereClause(new Bpl.IdentifierExpr(v.Origin, NameTypeParam(v), Predef.Ty), v.Characteristics) : null;
        vars.Add(BplFormalVar(named ? NameTypeParam(v) : null, Predef.Ty, true, out var e, whereClause));
        exprs.Add(e);
      }
      return vars;
    }

    public Bpl.Expr/*?*/ GetTyWhereClause(Bpl.Expr expr, TypeParameterCharacteristics characteristics) {
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

    static readonly List<Boolean> Bools = [false, true];

    public Expr GetRevealConstant(Function f) {
      this.CreateRevealableConstant(f);
      return this.functionReveals[f];
    }

    public static IsAllocType ISALLOC { get { return IsAllocType.ISALLOC; } }
    public static IsAllocType NOALLOC { get { return IsAllocType.NOALLOC; } }
  }

  public enum AssertMode { Keep, Assume, Check }
}

public enum IsAllocType { ISALLOC, NOALLOC, NEVERALLOC };  // NEVERALLOC is like NOALLOC, but overrides AlwaysAlloc

class FromDafnyNode : VCGeneration.TokenWrapper {
  public INode Node { get; }

  public FromDafnyNode(INode node) : base(node.Origin) {
    this.Node = node;
  }
}