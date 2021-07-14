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
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class FreshIdGenerator
  {
    Dictionary<string, int> PrefixToCount = new Dictionary<string, int>();

    public /*spec public*/ readonly Stack<int> Tip = new Stack<int>();
    string tipString;  // a string representation of Tip
    int tipChildrenCount = 0;
    readonly Stack<Dictionary<string, int>> PrefixToCount_Stack = new Stack<Dictionary<string, int>>();  // invariant PrefixToCount_Stack.Count == Tip.Count
    public void Push() {
      Tip.Push(tipChildrenCount);
      tipChildrenCount = 0;
      tipString = ComputeTipString();
      PrefixToCount_Stack.Push(PrefixToCount);
      PrefixToCount = new Dictionary<string, int>();
    }
    public void Pop() {
      Contract.Requires(Tip.Count > 0);
      int k = Tip.Pop();
      tipChildrenCount = k + 1;
      tipString = ComputeTipString();
      PrefixToCount = PrefixToCount_Stack.Pop();
    }
    string ComputeTipString() {
      string s = null;
      foreach (var k in Tip) {
        if (s == null) {
          s = k.ToString();
        } else {
          s = k.ToString() + "_" + s;
        }
      }
      return s;
    }

    readonly string CommonPrefix = "";

    public FreshIdGenerator()
    {
    }

    private FreshIdGenerator(string commonPrefix)
    {
      CommonPrefix = commonPrefix;
    }

    public void Reset()
    {
      lock (PrefixToCount)
      {
        PrefixToCount.Clear();
      }
    }

    public string FreshId(string prefix)
    {
      return CommonPrefix + prefix + FreshNumericId(prefix);
    }

    public FreshIdGenerator NestedFreshIdGenerator(string prefix)
    {
      return new FreshIdGenerator(FreshId(prefix));
    }

    public string FreshNumericId(string prefix = "")
    {
      lock (PrefixToCount)
      {
        int old;
        if (!PrefixToCount.TryGetValue(prefix, out old)) {
          old = 0;
        }
        PrefixToCount[prefix] = old + 1;
        return tipString == null ? old.ToString() : tipString + "_" + old.ToString();
      }
    }
  }

  public class Translator {
    ErrorReporter reporter;
    // TODO(wuestholz): Enable this once Dafny's recommended Z3 version includes changeset 0592e765744497a089c42021990740f303901e67.
    public bool UseOptimizationInZ3 { get; set; }

    public class TranslatorFlags {
      public bool InsertChecksums = 0 < CommandLineOptions.Clo.VerifySnapshots;
      public string UniqueIdPrefix = null;
    }

    [NotDelayed]
    public Translator(ErrorReporter reporter, TranslatorFlags flags = null) {
      this.reporter = reporter;
      if (flags == null) {
        flags = new TranslatorFlags();
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

    private void EstablishModuleScope(ModuleDefinition systemModule, ModuleDefinition m){
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
    readonly Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>/*!*/ classes = new Dictionary<TopLevelDecl/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<TopLevelDecl, string>/*!*/ classConstants = new Dictionary<TopLevelDecl, string>();
    readonly Dictionary<int, string> functionConstants = new Dictionary<int, string>();
    readonly Dictionary<Function, string> functionHandles = new Dictionary<Function, string>();
    readonly List<FuelConstant> functionFuel = new List<FuelConstant>();
    readonly Dictionary<Field/*!*/,Bpl.Constant/*!*/>/*!*/ fields = new Dictionary<Field/*!*/,Bpl.Constant/*!*/>();
    readonly Dictionary<Field/*!*/, Bpl.Function/*!*/>/*!*/ fieldFunctions = new Dictionary<Field/*!*/, Bpl.Function/*!*/>();
    readonly Dictionary<string, Bpl.Constant> fieldConstants = new Dictionary<string,Constant>();
    readonly Dictionary<string, Bpl.Constant> tytagConstants = new Dictionary<string,Constant>();
    readonly ISet<string> abstractTypes = new HashSet<string>();
    readonly ISet<string> opaqueTypes = new HashSet<string>();

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
    void ObjectInvariant()
    {
      Contract.Invariant(cce.NonNullDictionaryAndValues(classes));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fields));
      Contract.Invariant(cce.NonNullDictionaryAndValues(fieldFunctions));
      Contract.Invariant(codeContext == null || codeContext.EnclosingModule == currentModule);
    }

    [Pure]
    bool VisibleInScope(Declaration d) {
      Contract.Requires(d != null);
      if (d is ClassDecl cl && cl.NonNullTypeDecl != null) {
        // "provides" is recorded in the non-null type declaration, not the class
        return cl.NonNullTypeDecl.IsVisibleInScope(currentScope);
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
      if (d.tok is IncludeToken && !DafnyOptions.O.VerifyAllModules) {
        return false;
      }

      if (d.IsVisibleInScope(verificationScope)) {
        Contract.Assert(d.IsRevealedInScope(verificationScope));
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


    readonly PredefinedDecls predef;

    private TranslatorFlags flags = new TranslatorFlags();
    private bool InsertChecksums { get { return flags.InsertChecksums; } }
    private string UniqueIdPrefix { get { return flags.UniqueIdPrefix; } }

    internal class PredefinedDecls {
      public readonly Bpl.Type CharType;
      public readonly Bpl.Type RefType;
      public readonly Bpl.Type BoxType;
      public Bpl.Type BigOrdinalType {
        get { return BoxType; }
      }
      public readonly Bpl.Type TickType;
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
        Contract.Invariant(TickType != null);
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

      public Bpl.Type SetType(IToken tok, bool finite, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, finite ? setTypeCtor : isetTypeCtor, new List<Bpl.Type> { ty });
      }

      public Bpl.Type MultiSetType(IToken tok, Bpl.Type ty) {
        Contract.Requires(tok != null);
        Contract.Requires(ty != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.TypeSynonymAnnotation(Token.NoToken, multiSetTypeCtor, new List<Bpl.Type>{ ty });
      }
      public Bpl.Type MapType(IToken tok, bool finite, Bpl.Type tya, Bpl.Type tyb) {
        Contract.Requires(tok != null);
        Contract.Requires(tya != null && tyb != null);
        Contract.Ensures(Contract.Result<Bpl.Type>() != null);

        return new Bpl.CtorType(Token.NoToken, finite ? mapTypeCtor : imapTypeCtor, new List<Bpl.Type> { tya, tyb });
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

        return new Bpl.IdentifierExpr(tok, AllocField);
      }

      public PredefinedDecls(Bpl.TypeCtorDecl charType, Bpl.TypeCtorDecl refType, Bpl.TypeCtorDecl boxType, Bpl.TypeCtorDecl tickType,
                             Bpl.TypeSynonymDecl setTypeCtor, Bpl.TypeSynonymDecl isetTypeCtor, Bpl.TypeSynonymDecl multiSetTypeCtor,
                             Bpl.TypeCtorDecl mapTypeCtor, Bpl.TypeCtorDecl imapTypeCtor,
                             Bpl.Function arrayLength, Bpl.Function realFloor,
                             Bpl.Function ORD_isLimit, Bpl.Function ORD_isSucc, Bpl.Function ORD_offset, Bpl.Function ORD_isNat,
                             Bpl.Function mapDomain, Bpl.Function imapDomain,
                             Bpl.Function mapValues, Bpl.Function imapValues, Bpl.Function mapItems, Bpl.Function imapItems,
                             Bpl.Function tuple2Destructors0, Bpl.Function tuple2Destructors1, Bpl.Function tuple2Constructor,
                             Bpl.TypeCtorDecl seqTypeCtor, Bpl.TypeSynonymDecl bv0TypeDecl,
                             Bpl.TypeCtorDecl fieldNameType, Bpl.TypeCtorDecl tyType, Bpl.TypeCtorDecl tyTagType, Bpl.TypeCtorDecl tyTagFamilyType,
                             Bpl.GlobalVariable heap, Bpl.TypeCtorDecl classNameType, Bpl.TypeCtorDecl nameFamilyType,
                             Bpl.TypeCtorDecl datatypeType, Bpl.TypeCtorDecl handleType, Bpl.TypeCtorDecl layerType, Bpl.TypeCtorDecl dtCtorId,
                             Bpl.Constant allocField) {
        #region Non-null preconditions on parameters
        Contract.Requires(charType != null);
        Contract.Requires(refType != null);
        Contract.Requires(boxType != null);
        Contract.Requires(tickType != null);
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
        this.TickType = new Bpl.CtorType(Token.NoToken, tickType, new List<Bpl.Type>());
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
        this.ORDINAL_IsNat= ORD_isNat;
        this.MapDomain = mapDomain;
        this.IMapDomain = imapDomain;
        this.MapValues = mapValues;
        this.IMapValues = imapValues;
        this.MapItems = mapItems;
        this.IMapItems = imapItems;
        this.Tuple2Destructors0 = tuple2Destructors0;
        this.Tuple2Destructors1 = tuple2Destructors1;
        this.Tuple2Constructor = tuple2Constructor;
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

    static PredefinedDecls FindPredefinedDecls(Bpl.Program prog) {
      Contract.Requires(prog != null);
      if (prog.Resolve() != 0) {
        Console.WriteLine("Error: resolution errors encountered in Dafny prelude");
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
      Bpl.TypeCtorDecl tickType = null;
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
          } else if (dt.Name == "TickType") {
            tickType = dt;
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
          }
        }
      }
      if (seqTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Seq");
      } else if (setTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Set");
      } else if (isetTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ISet");
      } else if (multiSetTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type MultiSet");
      } else if (mapTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Map");
      } else if (imapTypeCtor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type IMap");
      } else if (arrayLength == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.array.Length");
      } else if (realFloor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.real.Floor");
      } else if (ORDINAL_isLimit == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsLimit");
      } else if (ORDINAL_isSucc == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsSucc");
      } else if (ORDINAL_offset == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function ORD#Offset");
      } else if (ORDINAL_isNat == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function ORD#IsNat");
      } else if (mapDomain == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function Map#Domain");
      } else if (imapDomain == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Domain");
      } else if (mapValues == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function Map#Values");
      } else if (imapValues == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Values");
      } else if (mapItems == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function Map#Items");
      } else if (imapItems == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function IMap#Items");
      } else if (tuple2Destructors0 == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.Tuple2._0");
      } else if (tuple2Destructors1 == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function _System.Tuple2._1");
      } else if (tuple2Constructor == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of function #_System._tuple#2._#Make2");
      } else if (bv0TypeDecl == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Bv0");
      } else if (fieldNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Field");
      } else if (classNameType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type ClassName");
      } else if (tyType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type Ty");
      } else if (tyTagType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type TyTag");
      } else if (tyTagFamilyType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type TyTagFamily");
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
      } else if (charType == null) {
        Console.WriteLine("Error: Dafny prelude is missing declaration of type char");
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
        return new PredefinedDecls(charType, refType, boxType, tickType,
                                   setTypeCtor, isetTypeCtor, multiSetTypeCtor,
                                   mapTypeCtor, imapTypeCtor,
                                   arrayLength, realFloor,
                                   ORDINAL_isLimit, ORDINAL_isSucc, ORDINAL_offset, ORDINAL_isNat,
                                   mapDomain, imapDomain,
                                   mapValues, imapValues, mapItems, imapItems,
                                   tuple2Destructors0, tuple2Destructors1, tuple2Constructor,
                                   seqTypeCtor, bv0TypeDecl,
                                   fieldNameType, tyType, tyTagType, tyTagFamilyType,
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
      var defines = new List<string>();
      if (6 <= DafnyOptions.O.ArithMode) {
        defines.Add("ARITH_DISTR");
      }
      if (8 <= DafnyOptions.O.ArithMode) {
        defines.Add("ARITH_MUL_DIV_MOD");
      }
      if (9 <= DafnyOptions.O.ArithMode) {
        defines.Add("ARITH_MUL_SIGN");
      }
      if (10 <= DafnyOptions.O.ArithMode) {
        defines.Add("ARITH_MUL_COMM");
        defines.Add("ARITH_MUL_ASSOC");
      }
      int errorCount = BplParser.Parse(preludePath, defines, out prelude);
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

    private Bpl.Program DoTranslation(Program p, ModuleDefinition forModule) {
      program = p;
      Type.EnableScopes();

      EstablishModuleScope(p.BuiltIns.SystemModule, forModule);
      Type.PushScope(this.currentScope);

      foreach (var w in program.BuiltIns.Bitwidths) {
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

      foreach (TopLevelDecl d in program.BuiltIns.SystemModule.TopLevelDecls) {
        currentDeclaration = d;
        if (d is OpaqueTypeDecl) {
          var dd = (OpaqueTypeDecl)d;
          AddTypeDecl(dd);
          AddClassMembers(dd, true);
        } else if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          AddTypeDecl(dd);
          AddClassMembers(dd, true);
        } else if (d is SubsetTypeDecl) {
          AddTypeDecl((SubsetTypeDecl)d);
        } else if (d is TypeSynonymDecl) {
          // do nothing, just bypass type synonyms in the translation
        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          AddDatatype(dd);
          AddClassMembers(dd, true);
        } else if (d is ArrowTypeDecl) {
          var ad = (ArrowTypeDecl)d;
          GetClassTyCon(ad);
          AddArrowTypeAxioms(ad);
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          AddClassMembers(cl, true);
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

      foreach (ModuleDefinition m in mods) {
        foreach (TopLevelDecl d in m.TopLevelDecls.FindAll(VisibleInScope)) {
          currentDeclaration = d;
          if (d is OpaqueTypeDecl) {
            var dd = (OpaqueTypeDecl)d;
            AddTypeDecl(dd);
            AddClassMembers(dd, true);
          } else if (d is ModuleDecl) {
            // submodules have already been added as a top level module, ignore this.
          } else if (d is RevealableTypeDecl) {
            AddTypeDecl((RevealableTypeDecl)d);
          } else {
            Contract.Assert(false);
          }
        }
      }

      foreach (var c in tytagConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }
      foreach (var c in fieldConstants.Values) {
        sink.AddTopLevelDeclaration(c);
      }

      AddTraitParentAxioms();

      if (InsertChecksums) {
        foreach (var impl in sink.Implementations) {
          if (impl.FindStringAttribute("checksum") == null) {
            impl.AddAttribute("checksum", "stable");
          }
        }
        foreach (var func in sink.Functions) {
          if (func.FindStringAttribute("checksum") == null) {
            func.AddAttribute("checksum", "stable");
          }
        }
      }

      Type.PopScope(this.currentScope);
      Type.DisableScopes();
      return sink;

    }

    // Don't verify modules which only contain other modules
    private static bool ShouldVerifyModule(ModuleDefinition m) {
      if (!m.IsToBeVerified && !DafnyOptions.O.VerifyAllModules)
        return false;

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
        return p.RawModules().Where(ShouldVerifyModule);
    }

    public static IEnumerable<Tuple<string, Bpl.Program>> Translate(Program p, ErrorReporter reporter, TranslatorFlags flags = null) {
      Contract.Requires(p != null);
      Contract.Requires(p.ModuleSigs.Count > 0);

      Type.ResetScopes();

      foreach (ModuleDefinition outerModule in VerifiableModules(p)) {

        var translator = new Translator(reporter, flags);

        if (translator.sink == null || translator.sink == null) {
          // something went wrong during construction, which reads the prelude; an error has
          // already been printed, so just return an empty program here (which is non-null)
          yield return new Tuple<string,Bpl.Program>(outerModule.CompileName, new Bpl.Program());
        }
        yield return new Tuple<string, Bpl.Program>(outerModule.CompileName, translator.DoTranslation(p, outerModule));
      }

    }

    public Bpl.Type BplBvType(int width) {
      Contract.Requires(0 <= width);
      if (width == 0) {
        // Boogie claims to support bv0, but it translates it straight down to the SMT solver's 0-width bitvector type.
        // However, the SMT-LIB 2 standard does not define such a bitvector width, so this is a bug in Boogie.  The
        // best would be to fix this in Boogie, but for now, we simply work around it here.
        return predef.Bv0Type;
      } else {
        return Bpl.Type.GetBvType(width);
      }
    }

    internal Expr BplBvLiteralExpr(IToken tok, BaseTypes.BigNum n, BitvectorType bitvectorType) {
      Contract.Requires(tok != null);
      Contract.Requires(bitvectorType != null);
      return BplBvLiteralExpr(tok, n, bitvectorType.Width);
    }
    internal Expr BplBvLiteralExpr(IToken tok, BaseTypes.BigNum n, int width) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= width);
      if (width == 0) {
        // see comment in BplBvType
        Contract.Assert(n.IsZero);
        return Bpl.Expr.Literal(0);
      } else if (n.IsNegative) {
        // This can only happen if some error is reported elsewhere. Nevertheless, we do need to
        // generate a Boogie expression and Boogie would crash if we pass a negative number to
        // Bpl.LiteralExpr for a bitvector.
        var zero = new Bpl.LiteralExpr(tok, BaseTypes.BigNum.ZERO, width);
        var absN = new Bpl.LiteralExpr(tok, -n, width);
        var etran = new ExpressionTranslator(this, predef, tok);
        return etran.TrToFunctionCall(tok, "sub_bv" + width, BplBvType(width), zero, absN, false);
      } else {
        return new Bpl.LiteralExpr(tok, n, width);
      }
    }

    private void AddBitvectorTypeAxioms(int w) {
      Contract.Requires(0 <= w);

      if (w == 0) {
        // the axioms for bv0 are already in DafnyPrelude.bpl
        return;
      }

      // box/unbox axiom
      var tok = Token.NoToken;
      var printableName = "bv" + w;
      var dafnyType = new BitvectorType(w);
      var boogieType = BplBvType(w);
      var typeTerm = TypeToTy(dafnyType);
      AddBoxUnboxAxiom(tok, printableName, typeTerm, boogieType, new List<Variable>());

      // axiom (forall v: bv3 :: { $Is(v, TBitvector(3)) } $Is(v, TBitvector(3)));
      var vVar = BplBoundVar("v", boogieType, out var v);
      var bvs = new List<Variable>() { vVar };
      var isBv = MkIs(v, typeTerm);
      var tr = BplTrigger(isBv);
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isBv)));

      // axiom (forall v: bv3, heap: Heap :: { $IsAlloc(v, TBitvector(3), h) } $IsAlloc(v, TBitvector(3), heap));
      vVar = BplBoundVar("v", boogieType, out v);
      var heapVar = BplBoundVar("heap", predef.HeapType, out var heap);
      bvs = new List<Variable>() { vVar, heapVar };
      var isAllocBv = MkIsAlloc(v, typeTerm, heap);
      tr = BplTrigger(isAllocBv);
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, new Bpl.ForallExpr(tok, bvs, tr, isAllocBv)));
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
              }
            }
          }
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
        foreach (TopLevelDecl d in m.TopLevelDecls) {
          var c = d as TopLevelDeclWithMembers;
          if (c == null || !RevealedInScope(d)) {
            continue;
          }
          foreach (var parentType in c.ParentTraits) {
            Bpl.Expr heap; var heapVar = BplBoundVar("$heap", predef.HeapType, out heap);
            Bpl.Expr o; var oVar = BplBoundVar("$o", predef.RefType, out o);
            Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);

            List<Bpl.Expr> tyexprs;
            var bvarsTypeParameters = MkTyParamBinders(GetTypeParams(c), out tyexprs);

            // axiom (forall T: Ty, $o: ref ::
            //     { $Is($o, C(T)) }
            //     $o != null && $Is($o, C(T)) ==> $Is($o, J(G(T)));
            var isC = MkIs(o, UserDefinedType.FromTopLevelDecl(c.tok, c));
            var isJ = MkIs(o, parentType);
            var bvs = new List<Bpl.Variable>();
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            var tr = BplTrigger(isC);
            var body = BplImp(BplAnd(oNotNull, isC), isJ);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body)));

            // axiom (forall T: Ty, $Heap: Heap, $o: ref ::
            //     { $IsAlloc($o, C(T), $Heap) }
            //     $o != null && $IsAlloc($o, C(T), $Heap) ==> $IsAlloc($o, J(G(T)), $Heap);
            var isAllocC = MkIsAlloc(o, UserDefinedType.FromTopLevelDecl(c.tok, c), heap);
            var isAllocJ = MkIsAlloc(o, parentType, heap);
            bvs = new List<Bpl.Variable>();
            bvs.AddRange(bvarsTypeParameters);
            bvs.Add(oVar);
            bvs.Add(heapVar);
            tr = BplTrigger(isAllocC);
            body = BplImp(BplAnd(oNotNull, isAllocC), isAllocJ);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, new Bpl.ForallExpr(c.tok, bvs, tr, body)));
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

    void AddTypeDecl_Aux(IToken tok, string nm, List<TypeParameter> typeArgs) {
      Contract.Requires(tok != null);
      Contract.Requires(nm != null);
      Contract.Requires(typeArgs != null);

      if (abstractTypes.Contains(nm)) {
        // nothing to do; has already been added
        return;
      }
      if (typeArgs.Count == 0) {
        sink.AddTopLevelDeclaration(
          new Bpl.Constant(tok,
            new TypedIdent(tok, nm, predef.Ty), false /* not unique */));
      } else {
        // Note, the function produced is NOT necessarily injective, because the type may be replaced
        // in a refinement module in such a way that the type arguments do not matter.
        var args = new List<Bpl.Variable>(typeArgs.ConvertAll(a => (Bpl.Variable)BplFormalVar(null, predef.Ty, true)));
        var func = new Bpl.Function(tok, nm, args, BplFormalVar(null, predef.Ty, false));
        sink.AddTopLevelDeclaration(func);
      }
      abstractTypes.Add(nm);
    }

    void AddTypeDecl(OpaqueTypeDecl td) {
      Contract.Requires(td != null);
      AddTypeDecl_Aux(td.tok, nameTypeParam(td), td.TypeArgs);
    }


    void AddTypeDecl(InternalTypeSynonymDecl td) {
      Contract.Requires(td != null);
      Contract.Requires(!RevealedInScope(td));
      AddTypeDecl_Aux(td.tok, "#$" + td.Name, td.TypeArgs);
    }

    void AddTypeDecl(RevealableTypeDecl d) {
      Contract.Requires(d != null);
      if (RevealedInScope(d)) {
        if (d is NewtypeDecl) {
          var dd = (NewtypeDecl)d;
          AddTypeDecl(dd);
          AddClassMembers(dd, true);
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          AddClassMembers(cl, DafnyOptions.O.OptimizeResolution < 1);
          if (cl.NonNullTypeDecl != null) {
            AddTypeDecl(cl.NonNullTypeDecl);
          }
          if (d is IteratorDecl) {
            AddIteratorSpecAndBody((IteratorDecl)d);
          }
        } else if (d is DatatypeDecl) {
          var dd = (DatatypeDecl)d;
          AddDatatype(dd);
          AddClassMembers(dd, true);
        } else if (d is SubsetTypeDecl) {
          AddTypeDecl((SubsetTypeDecl)d);
        } else if (d is TypeSynonymDecl) {
          //do nothing, this type will be transparent to translation
        } else {
          Contract.Assert(false);
        }
      } else {
        AddTypeDecl(d.SelfSynonymDecl());
        var dd = d as TopLevelDeclWithMembers;
        if (dd != null) {
          AddClassMembers(dd, true);
        }
      }
    }

    void AddTypeDecl(NewtypeDecl dd) {
      Contract.Requires(dd != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(dd);

      if (dd.Var != null) {
        AddWellformednessCheck(dd);
        currentModule = dd.EnclosingModuleDefinition;
        // Add $Is and $IsAlloc axioms for the newtype
        AddRedirectingTypeDeclAxioms(false, dd, dd.FullName);
        AddRedirectingTypeDeclAxioms(true, dd, dd.FullName);
        currentModule = null;
      }
      this.fuelContext = oldFuelContext;
    }

    void AddTypeDecl(SubsetTypeDecl dd) {
      Contract.Requires(dd != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(dd);

      if (!Attributes.Contains(dd.Attributes, "axiom")) {
        AddWellformednessCheck(dd);
      }
      currentModule = dd.EnclosingModuleDefinition;
      // Add $Is and $IsAlloc axioms for the subset type
      AddRedirectingTypeDeclAxioms(false, dd, dd.FullName);
      AddRedirectingTypeDeclAxioms(true, dd, dd.FullName);
      currentModule = null;
      this.fuelContext = oldFuelContext;
    }
    void AddRedirectingTypeDeclAxioms<T>(bool is_alloc, T dd, string fullName) where T : TopLevelDecl, RedirectingTypeDecl {
      Contract.Requires(dd != null);
      Contract.Requires(dd.Var != null && dd.Constraint != null);
      Contract.Requires(fullName != null);

      List<Bpl.Expr> typeArgs;
      var vars = MkTyParamBinders(dd.TypeArgs, out typeArgs);
      var o_ty = ClassTyCon(dd, typeArgs);

      var oBplType = TrType(dd.Var.Type);
      var o = BplBoundVar(dd.Var.AssignUniqueName(dd.IdGenerator), oBplType, vars);

      Bpl.Expr body, is_o;
      string name = string.Format("{0}: {1} ", fullName, dd.WhatKind);

      if (is_alloc) {
        name += "$IsAlloc";
        var h = BplBoundVar("$h", predef.HeapType, vars);
        // $IsAlloc(o, ..)
        is_o = MkIsAlloc(o, o_ty, h, ModeledAsBoxType(dd.Var.Type));
        if (dd.Var.Type.IsNumericBased() || dd.Var.Type.IsBitVectorType || dd.Var.Type.IsBoolType || dd.Var.Type.IsCharType) {
          body = is_o;
        } else {
          Bpl.Expr rhs = MkIsAlloc(o, dd.Var.Type, h);
          body = BplIff(is_o, rhs);
        }
      } else {
        name += "$Is";
        // $Is(o, ..)
        is_o = MkIs(o, o_ty, ModeledAsBoxType(dd.Var.Type));
        var etran = new ExpressionTranslator(this, predef, NewOneHeapExpr(dd.tok));
        Bpl.Expr parentConstraint, constraint;
        if (dd.Var.Type.IsNumericBased() || dd.Var.Type.IsBitVectorType || dd.Var.Type.IsBoolType) {
          // optimize this to only use the numeric/bitvector constraint, not the whole $Is thing on the base type
          parentConstraint = Bpl.Expr.True;
          var udt = UserDefinedType.FromTopLevelDecl(dd.tok, dd);
          var c = Resolver.GetImpliedTypeConstraint(dd.Var, udt);
          constraint = etran.TrExpr(c);
        } else {
          parentConstraint = MkIs(o, dd.Var.Type);
          // conjoin the constraint
          constraint = etran.TrExpr(dd.Constraint);
        }
        body = BplIff(is_o, BplAnd(parentConstraint, constraint));
      }

      sink.AddTopLevelDeclaration(new Bpl.Axiom(dd.tok, BplForall(vars, BplTrigger(is_o), body), name));
    }

    void AddDatatype(DatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(sink != null && predef != null);

      foreach (DatatypeCtor ctor in dt.Ctors) {
        // Add:  function #dt.ctor(tyVars, paramTypes) returns (DatatypeType);

        List<Bpl.Variable> argTypes = new List<Bpl.Variable>();
        foreach (Formal arg in ctor.Formals) {
          Bpl.Variable a = new Bpl.Formal(arg.tok, new Bpl.TypedIdent(arg.tok, Bpl.TypedIdent.NoName, TrType(arg.Type)), true);
          argTypes.Add(a);
        }
        Bpl.Variable resType = new Bpl.Formal(ctor.tok, new Bpl.TypedIdent(ctor.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), false);
        Bpl.Function fn;
        if (dt is TupleTypeDecl ttd && ttd.Dims == 2) {
          fn = predef.Tuple2Constructor;
        } else {
          fn = new Bpl.Function(ctor.tok, ctor.FullName, argTypes, resType, "Constructor function declaration");
          sink.AddTopLevelDeclaration(fn);
        }
        if (InsertChecksums) {
          InsertChecksum(dt, fn);
        }

        List<Bpl.Variable> bvs;
        List<Bpl.Expr> args;


        {
          // Add:  const unique ##dt.ctor: DtCtorId;
          Bpl.Constant cid = new Bpl.Constant(ctor.tok, new Bpl.TypedIdent(ctor.tok, "#" + ctor.FullName, predef.DtCtorId), true);
          Bpl.Expr c = new Bpl.IdentifierExpr(ctor.tok, cid);
          sink.AddTopLevelDeclaration(cid);

          {
            // Add:  axiom (forall params :: DatatypeCtorId(#dt.ctor(params)) == ##dt.ctor);
            CreateBoundVariables(ctor.Formals, out bvs, out args);
            var constructor_call = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
            var lhs = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, constructor_call);
            Bpl.Expr q = Bpl.Expr.Eq(lhs, c);
            var trigger = BplTrigger(constructor_call);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, BplForall(bvs, trigger, q), "Constructor identifier"));
          }

          {
            // Add:  function dt.ctor?(this: DatatypeType): bool { DatatypeCtorId(this) == ##dt.ctor }
            fn = GetReadonlyField(ctor.QueryField);
            sink.AddTopLevelDeclaration(fn);

            // and here comes the associated axiom:

            Bpl.Expr th; var thVar = BplBoundVar("d", predef.DatatypeType, out th);
            var queryPredicate = FunctionCall(ctor.tok, fn.Name, Bpl.Type.Bool, th);
            var ctorId = FunctionCall(ctor.tok, BuiltinFunction.DatatypeCtorId, null, th);
            var rhs = Bpl.Expr.Eq(ctorId, c);
            var body = Bpl.Expr.Iff(queryPredicate, rhs);
            var tr = BplTrigger(queryPredicate);
            var ax = BplForall(thVar, tr, body);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, ax, "Questionmark and identifier"));
          }

          // check well-formedness of any default-value expressions
          AddWellformednessCheck(ctor);
        }


        {
          // Add:  axiom (forall d: DatatypeType :: dt.ctor?(d) ==> (exists params :: d == #dt.ctor(params));
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr rhs = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          Bpl.Expr dId; var dBv = BplBoundVar("d", predef.DatatypeType, out dId);
          Bpl.Expr q = Bpl.Expr.Eq(dId, rhs);
          if (bvs.Count != 0) {
            q = new Bpl.ExistsExpr(ctor.tok, bvs, null/*always in a Skolemization context*/, q);
          }
          Bpl.Expr dtq = FunctionCall(ctor.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, dId);
          var trigger = BplTrigger(dtq);
          q = BplForall(dBv, trigger, BplImp(dtq, q));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Constructor questionmark has arguments"));
        }

        MapM(Bools, is_alloc => {
          /*
            (forall x0 : C0, ..., xn : Cn, G : Ty •
              { $Is(C(x0,...,xn), T(G)) }
              $Is(C(x0,...,xn), T(G)) <==>
              $Is[Box](x0, C0(G)) && ... && $Is[Box](xn, Cn(G)));
            (forall x0 : C0, ..., xn : Cn, G : Ty, H : Heap •
                { $IsAlloc(C(G, x0,...,xn), T(G), H) }
                IsGoodHeap(H) ==>
                   ($IsAlloc(C(G, x0,...,xn), T(G), H) <==>
                    $IsAlloc[Box](x0, C0(G), H) && ... && $IsAlloc[Box](xn, Cn(G), H)));
          */
          List<Bpl.Expr> tyexprs;
          var tyvars = MkTyParamBinders(dt.TypeArgs, out tyexprs);
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          Bpl.Expr h;
          var hVar = BplBoundVar("$h", predef.HeapType, out h);
          Bpl.Expr conj = Bpl.Expr.True;
          for (var i = 0; i < ctor.Formals.Count; i++) {
            var arg = ctor.Formals[i];
            if (is_alloc) {
              if (CommonHeapUse || (NonGhostsUseHeap && !arg.IsGhost)) {
                conj = BplAnd(conj, MkIsAlloc(args[i], arg.Type, h));
              }
            } else {
              conj = BplAnd(conj, MkIs(args[i], arg.Type));
            }
          }
          var c_params = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          var c_ty = ClassTyCon((TopLevelDecl)dt, tyexprs);
          bvs.InsertRange(0, tyvars);
          if (!is_alloc) {
            var c_is = MkIs(c_params, c_ty);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok,
                BplForall(bvs, BplTrigger(c_is), BplIff(c_is, conj)),
                "Constructor $Is"));
          } else if (is_alloc && (CommonHeapUse || NonGhostsUseHeap)) {
            var isGoodHeap = FunctionCall(ctor.tok, BuiltinFunction.IsGoodHeap, null, h);
            var c_alloc = MkIsAlloc(c_params, c_ty, h);
            bvs.Add(hVar);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok,
                BplForall(bvs, BplTrigger(c_alloc),
                               BplImp(isGoodHeap, BplIff(c_alloc, conj))),
                "Constructor $IsAlloc"));
          }
          if (is_alloc && CommonHeapUse && !AlwaysUseHeap) {
            for (int i = 0; i < ctor.Formals.Count; i++) {
              var arg = ctor.Formals[i];
              var dtor = GetReadonlyField(ctor.Destructors[i]);
              /* (forall d : DatatypeType, G : Ty, H : Heap •
                     { $IsAlloc[Box](Dtor(d), D(G), H) }
                     IsGoodHeap(H) &&
                     C?(d) &&
                     (exists G' : Ty :: $IsAlloc(d, T(G,G'), H))
                     ==>
                         $IsAlloc[Box](Dtor(d), D(G), H))
               */
              Bpl.Expr dId; var dBv = BplBoundVar("d", predef.DatatypeType, out dId);
              var isGoodHeap = FunctionCall(ctor.tok, BuiltinFunction.IsGoodHeap, null, h);
              Bpl.Expr dtq = FunctionCall(ctor.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, dId);
              var c_alloc = MkIsAlloc(dId, c_ty, h);
              var dtorD = FunctionCall(ctor.tok, dtor.Name, TrType(arg.Type), dId);
              var d_alloc = MkIsAlloc(dtorD, arg.Type, h);

              // split tyvars into G,G' where G are the type variables that are used in the type of the destructor
              var freeTypeVars = new HashSet<TypeParameter>();
              ComputeFreeTypeVariables_All(arg.Type, freeTypeVars);
              var tyvarsG = new List<Bpl.Variable>();
              var tyvarsGprime = new List<Bpl.Variable>();
              Contract.Assert(dt.TypeArgs.Count == tyvars.Count);
              for (int j = 0; j < dt.TypeArgs.Count; j++) {
                var tv = tyvars[j];
                if (freeTypeVars.Contains(dt.TypeArgs[j])) {
                  tyvarsG.Add(tv);
                } else {
                  tyvarsGprime.Add(tv);
                }
              }

              bvs = new List<Bpl.Variable>();
              bvs.Add(dBv);
              bvs.AddRange(tyvarsG);
              bvs.Add(hVar);
              if (tyvarsGprime.Count != 0) {
                c_alloc = new Bpl.ExistsExpr(ctor.tok, tyvarsGprime, BplTrigger(c_alloc), c_alloc);
              }
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok,
                  BplForall(bvs, BplTrigger(d_alloc),
                                 BplImp(BplAnd(isGoodHeap, BplAnd(dtq, c_alloc)), d_alloc)),
                  "Destructor $IsAlloc"));
            }
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
          sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Constructor literal"));
        }

        // Injectivity axioms for normal arguments
        for (int i = 0; i < ctor.Formals.Count; i++) {
          var arg = ctor.Formals[i];
          // function ##dt.ctor#i(DatatypeType) returns (Ti);
          var sf = ctor.Destructors[i];
          Contract.Assert(sf != null);
          fn = GetReadonlyField(sf);
          if (fn == predef.Tuple2Destructors0 || fn == predef.Tuple2Destructors1) {
            // the two destructors for 2-tuples are predefined in Prelude for use
            // by the Map#Items axiom
          } else if (sf.EnclosingCtors[0] != ctor) {
            // this special field, which comes from a shared destructor, is being declared in a different iteration of this loop
          } else {
            sink.AddTopLevelDeclaration(fn);
          }
          // axiom (forall params :: ##dt.ctor#i(#dt.ctor(params)) == params_i);
          CreateBoundVariables(ctor.Formals, out bvs, out args);
          var inner = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
          var outer = FunctionCall(ctor.tok, fn.Name, TrType(arg.Type), inner);
          var q = BplForall(bvs, BplTrigger(inner), Bpl.Expr.Eq(outer, args[i]));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Constructor injectivity"));

          if (dt is IndDatatypeDecl) {
            var argType = arg.Type.NormalizeExpandKeepConstraints();  // TODO: keep constraints -- really?  Write a test case
            if (argType.IsDatatype || argType.IsTypeParameter) {
              // for datatype:             axiom (forall params :: {#dt.ctor(params)} DtRank(params_i) < DtRank(#dt.ctor(params)));
              // for type-parameter type:  axiom (forall params :: {#dt.ctor(params)} BoxRank(params_i) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Expr lhs = FunctionCall(ctor.tok, arg.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank, null, args[i]);
              /* CHECK
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                argType.IsDatatype ? args[i] : FunctionCall(ctor.tok, BuiltinFunction.Unbox, predef.DatatypeType, args[i]));
              */
              Bpl.Expr ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
              var trigger = BplTrigger(ct);
              q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Lt(lhs, rhs));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive rank"));
            } else if (argType is SeqType) {
              // axiom (forall params, i: int {#dt.ctor(params)} :: 0 <= i && i < |arg| ==> DtRank(arg[i]) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, i: int {#dt.ctor(params)} :: 0 <= i && i < |arg| ==> DtRank(Unbox(Seq#Index(arg,i))) < DtRank(#dt.ctor(params)));
              {
                CreateBoundVariables(ctor.Formals, out bvs, out args);
                Bpl.Variable iVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "i", Bpl.Type.Int));
                bvs.Add(iVar);
                Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, iVar);
                Bpl.Expr ante = Bpl.Expr.And(
                  Bpl.Expr.Le(Bpl.Expr.Literal(0), ie),
                  Bpl.Expr.Lt(ie, FunctionCall(arg.tok, BuiltinFunction.SeqLength, null, args[i])));
                var seqIndex = FunctionCall(arg.tok, BuiltinFunction.SeqIndex, predef.DatatypeType, args[i], ie);
                Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null,
                  FunctionCall(arg.tok, BuiltinFunction.Unbox, predef.DatatypeType, seqIndex));
                var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
                var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
                q = new Bpl.ForallExpr(ctor.tok, bvs, new Trigger(lhs.tok, true, new List<Bpl.Expr> { seqIndex, ct }), Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
                sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive seq element rank"));
              }

              // axiom (forall params {#dt.ctor(params)} :: SeqRank(arg) < DtRank(#dt.ctor(params)));
              {
                CreateBoundVariables(ctor.Formals, out bvs, out args);
                var lhs = FunctionCall(ctor.tok, BuiltinFunction.SeqRank, null, args[i]);
                var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
                var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
                var trigger = BplTrigger(ct);
                q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Lt(lhs, rhs));
                sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive seq rank"));
              }
            } else if (argType is SetType) {
              // axiom (forall params, d: Datatype {arg[d], #dt.ctor(params)}  :: arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype {arg[Box(d)], #dt.ctor(params)} :: arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              Bpl.Expr inSet = Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie));
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
              var trigger = new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { inSet, ct });
              q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Imp(inSet, Bpl.Expr.Lt(lhs, rhs)));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive set element rank"));
            } else if (argType is MultiSetType) {
              // axiom (forall params, d: Datatype {arg[d], #dt.ctor(params)} :: 0 < arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              // that is:
              // axiom (forall params, d: Datatype {arg[Box(d)], #dt.ctor(params)} :: 0 < arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
              bvs.Add(dVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.tok, dVar);
              var inMultiset = Bpl.Expr.SelectTok(arg.tok, args[i], FunctionCall(arg.tok, BuiltinFunction.Box, null, ie));
              Bpl.Expr ante = Bpl.Expr.Gt(inMultiset, Bpl.Expr.Literal(0));
              Bpl.Expr lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
              var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
              var trigger = new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { inMultiset, ct });
              q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Imp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive multiset element rank"));
            } else if (argType is MapType) {
              var finite = ((MapType)argType).Finite;
              {
                // axiom (forall params, d: DatatypeType
                //   { Map#Domain(arg)[$Box(d)], #dt.ctor(params) }
                //   Map#Domain(arg)[$Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
                CreateBoundVariables(ctor.Formals, out bvs, out args);
                var dVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "d", predef.DatatypeType));
                bvs.Add(dVar);
                var ie = new Bpl.IdentifierExpr(arg.tok, dVar);
                var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                var domain = FunctionCall(arg.tok, f, predef.MapType(arg.tok, finite, predef.BoxType, predef.BoxType), args[i]);
                var inDomain = Bpl.Expr.SelectTok(arg.tok, domain, FunctionCall(arg.tok, BuiltinFunction.Box, null, ie));
                var lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ie);
                var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
                var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
                var trigger = new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { inDomain, ct });
                q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Imp(inDomain, Bpl.Expr.Lt(lhs, rhs)));
                sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive map key rank"));
              }
              {
                // axiom(forall params, bx: Box ::
                //   { Map#Elements(arg)[bx], #dt.ctor(params) }
                //   Map#Domain(arg)[bx] ==> DtRank($Unbox(Map#Elements(arg)[bx]): DatatypeType) < DtRank(#dt.ctor(params)));
                CreateBoundVariables(ctor.Formals, out bvs, out args);
                var bxVar = new Bpl.BoundVariable(arg.tok, new Bpl.TypedIdent(arg.tok, "bx", predef.BoxType));
                bvs.Add(bxVar);
                var ie = new Bpl.IdentifierExpr(arg.tok, bxVar);
                var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
                var domain = FunctionCall(arg.tok, f, predef.MapType(arg.tok, finite, predef.BoxType, predef.BoxType), args[i]);
                var inDomain = Bpl.Expr.SelectTok(arg.tok, domain, ie);
                var ef = finite ? BuiltinFunction.MapElements : BuiltinFunction.IMapElements;
                var element = FunctionCall(arg.tok, ef, predef.MapType(arg.tok, finite, predef.BoxType, predef.BoxType), args[i]);
                var elmt = Bpl.Expr.SelectTok(arg.tok, element, ie);
                var unboxElmt = FunctionCall(arg.tok, BuiltinFunction.Unbox, predef.DatatypeType, elmt);
                var lhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, unboxElmt);
                var ct = FunctionCall(ctor.tok, ctor.FullName, predef.DatatypeType, args);
                var rhs = FunctionCall(ctor.tok, BuiltinFunction.DtRank, null, ct);
                var trigger = new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { inDomain, ct });
                q = new Bpl.ForallExpr(ctor.tok, bvs, trigger, Bpl.Expr.Imp(inDomain, Bpl.Expr.Lt(lhs, rhs)));
                sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.tok, q, "Inductive map value rank"));
              }
            }
          }
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
                                        "Depth-one case-split function");

        if (InsertChecksums) {
          InsertChecksum(dt, cases_fn);
        }

        sink.AddTopLevelDeclaration(cases_fn);
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
          sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, "Depth-one case-split axiom"));
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
        sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, "Questionmark data type disjunctivity"));
      }

      if (dt is IndDatatypeDecl) {
        var dtEqualName = dt.FullSanitizedName + "#Equal";

        // Add function Dt#Equal(DatatypeType, DatatypeType): bool;
        // For each constructor Ctor(x: X, y: Y), add an axiom of the form
        //     forall a, b ::
        //       { Dt#Equal(a, b), Ctor?(a) }
        //       { Dt#Equal(a, b), Ctor?(b) }
        //       Ctor?(a) && Ctor?(b)
        //       ==>
        //       (Dt#Equal(a, b) <==>
        //           X#Equal(a.x, b.x) &&
        //           Y#Equal(a.y, b.y)
        //       )
        // where X#Equal is the equality predicate for type X and a.x denotes Dtor#x(a), and similarly
        // for Y and b.
        // Except, in the event that the datatype has exactly one constructor, then instead generate:
        //     forall a, b ::
        //       { Dt#Equal(a, b) }
        //       true
        //       ==>
        //       ...as before
        {
          var args = new List<Variable>();
          args.Add(new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), false));
          args.Add(new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, predef.DatatypeType), false));
          var ctorEqualResult = new Bpl.Formal(dt.tok, new Bpl.TypedIdent(dt.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
          sink.AddTopLevelDeclaration(new Bpl.Function(dt.tok, dtEqualName, args, ctorEqualResult, "Datatype extensional equality declaration"));

          Bpl.Expr a; var aVar = BplBoundVar("a", predef.DatatypeType, out a);
          Bpl.Expr b; var bVar = BplBoundVar("b", predef.DatatypeType, out b);

          var dtEqual = FunctionCall(dt.tok, dtEqualName, Bpl.Type.Bool, a, b);

          foreach (var ctor in dt.Ctors) {
            Bpl.Trigger trigger;
            Bpl.Expr ante;
            if (dt.Ctors.Count == 1) {
              ante = Bpl.Expr.True;
              trigger = BplTrigger(dtEqual);
            } else {
              var ctorQ = GetReadonlyField(ctor.QueryField);
              var ctorQa = FunctionCall(ctor.tok, ctorQ.Name, Bpl.Type.Bool, a);
              var ctorQb = FunctionCall(ctor.tok, ctorQ.Name, Bpl.Type.Bool, b);
              ante = BplAnd(ctorQa, ctorQb);
              trigger = dt.Ctors.Count == 1 ? BplTrigger(dtEqual) :
                new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { dtEqual, ctorQa },
                new Bpl.Trigger(ctor.tok, true, new List<Bpl.Expr> { dtEqual, ctorQb }));
            }

            Bpl.Expr eqs = Bpl.Expr.True;
            for (var i = 0; i < ctor.Formals.Count; i++) {
              var arg = ctor.Formals[i];
              var dtor = GetReadonlyField(ctor.Destructors[i]);
              var dtorA = FunctionCall(ctor.tok, dtor.Name, TrType(arg.Type), a);
              var dtorB = FunctionCall(ctor.tok, dtor.Name, TrType(arg.Type), b);
              var eq = TypeSpecificEqual(ctor.tok, arg.Type, dtorA, dtorB);
              eqs = BplAnd(eqs, eq);
            }

            var ax = BplForall(new List<Variable> { aVar, bVar }, trigger, Bpl.Expr.Imp(ante, Bpl.Expr.Iff(dtEqual, eqs)));
            sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, string.Format("Datatype extensional equality definition: {0}", ctor.FullName)));
          }
        }

        // Add extensionality axiom: forall a, b :: { Dt#Equal(a, b) } Dt#Equal(a, b) <==> a == b
        {
          Bpl.Expr a; var aVar = BplBoundVar("a", predef.DatatypeType, out a);
          Bpl.Expr b; var bVar = BplBoundVar("b", predef.DatatypeType, out b);

          var lhs = FunctionCall(dt.tok, dtEqualName, Bpl.Type.Bool, a, b);
          var rhs = Bpl.Expr.Eq(a, b);

          var ax = BplForall(new List<Variable> { aVar, bVar }, BplTrigger(lhs), Bpl.Expr.Iff(lhs, rhs));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, string.Format("Datatype extensionality axiom: {0}", dt.FullName)));
        }
      }

      if (dt is CoDatatypeDecl) {
        var codecl = (CoDatatypeDecl)dt;

        Func<Bpl.Expr, Bpl.Expr> MinusOne = k => {
          if (k == null) {
            return null;
          } else if (k.Type.IsInt) {
            return Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
          } else {
            return FunctionCall(k.tok, "ORD#Minus", k.Type, k, FunctionCall(k.tok, "ORD#FromNat", k.Type, Bpl.Expr.Literal(1)));
          };
        };

        Action<Bpl.Type, Action<Tuple<List<Type>, List<Type>>, List<Bpl.Variable>, List<Bpl.Expr>, List<Bpl.Expr>, Bpl.Variable, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr>> CoAxHelper = (typeOfK, K) => {
          Func<string, List<TypeParameter>> renew = s =>
            Map(codecl.TypeArgs, tp =>
              new TypeParameter(tp.tok, tp.Name + "#" + s, tp.PositionalIndex, tp.Parent));
          List<TypeParameter> typaramsL = renew("l"), typaramsR = renew("r");
          List<Bpl.Expr> lexprs; var lvars = MkTyParamBinders(typaramsL, out lexprs);
          List<Bpl.Expr> rexprs; var rvars = MkTyParamBinders(typaramsR, out rexprs);
          Func<List<TypeParameter>, List<Type>> Types = l => Map(l, tp => (Type)new UserDefinedType(tp));
          var tyargs = Tuple.Create(Types(typaramsL), Types(typaramsR));

          var vars = Concat(lvars, rvars);

          Bpl.Expr k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit;
          Bpl.Variable kVar;
          if (typeOfK != null) {
            kVar = BplBoundVar("k", typeOfK, out k); vars.Add(kVar);
            if (typeOfK.IsInt) {
              kIsValid = Bpl.Expr.Le(Bpl.Expr.Literal(0), k);
              kIsNonZero = Bpl.Expr.Neq(Bpl.Expr.Literal(0), k);
              kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), k);
              kIsLimit = Bpl.Expr.False;
            } else {
              kIsValid = Bpl.Expr.True;
              kIsNonZero = Bpl.Expr.Neq(k, FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, Bpl.Expr.Literal(0)));
              kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), FunctionCall(k.tok, "ORD#Offset", Bpl.Type.Int, k));
              kIsLimit = FunctionCall(k.tok, "ORD#IsLimit", Bpl.Type.Bool, k);
            }
          } else {
            kVar = null; k = null;
            kIsValid = Bpl.Expr.True;
            kIsNonZero = Bpl.Expr.True;
            kHasSuccessor = Bpl.Expr.True;
            kIsLimit = Bpl.Expr.True;
          }
          var ly = BplBoundVar("ly", predef.LayerType, vars);
          var d0 = BplBoundVar("d0", predef.DatatypeType, vars);
          var d1 = BplBoundVar("d1", predef.DatatypeType, vars);

          K(tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1);
        };

        Action<Bpl.Type> AddAxioms = typeOfK => {
          {
            // Add two copies of the type parameter lists!
            var args = MkTyParamFormals(Concat(GetTypeParams(dt), GetTypeParams(dt)), false);
            if (typeOfK != null) {
              args.Add(BplFormalVar(null, typeOfK, true));
            }
            args.Add(BplFormalVar(null, predef.LayerType, true));
            args.Add(BplFormalVar(null, predef.DatatypeType, true));
            args.Add(BplFormalVar(null, predef.DatatypeType, true));
            var r = BplFormalVar(null, Bpl.Type.Bool, false);
            var fn_nm = typeOfK != null ? CoPrefixName(codecl) : CoEqualName(codecl);
            var fn = new Bpl.Function(dt.tok, fn_nm, args, r);
            if (InsertChecksums) {
              InsertChecksum(dt, fn);
            }
            sink.AddTopLevelDeclaration(fn);
          }

          // axiom (forall G0,...,Gn : Ty, k: int, ly : Layer, d0, d1: DatatypeType ::
          //  { Eq(G0, .., Gn, S(ly), k, d0, d1) }
          //  Is(d0, T(G0, .., Gn)) && Is(d1, T(G0, ... Gn)) ==>
          //  (Eq(G0, .., Gn, S(ly), k, d0, d1)
          //    <==>
          //      (0 < k.Offset ==>
          //        (d0.Nil? && d1.Nil?) ||
          //        (d0.Cons? && d1.Cons? && d0.head == d1.head && Eq(G0, .., Gn, ly, k-1, d0.tail, d1.tail))) &&
          //      (k != 0 && k.IsLimit ==>                        // for prefix equality only
          //        FullEq(G0, .., Gn, ly, d0.tail, d1.tail)))    // for prefix equality only
          CoAxHelper(typeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var eqDt = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var iss = BplAnd(MkIs(d0, ClassTyCon(dt, lexprs)), MkIs(d1, ClassTyCon(dt, rexprs)));
            var body = BplImp(
              iss,
              BplIff(eqDt,
                BplAnd(
                  BplImp(kHasSuccessor, BplOr(CoPrefixEquality(dt.tok, codecl, tyargs.Item1, tyargs.Item2, MinusOne(k), ly, d0, d1))),
                  k == null ? Bpl.Expr.True : BplImp(BplAnd(kIsNonZero, kIsLimit), CoEqualCall(codecl, tyargs.Item1, tyargs.Item2, null, ly, d0, d1)))));
            var ax = BplForall(vars, BplTrigger(eqDt), body);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, "Layered co-equality axiom"));
          });

          // axiom (forall G0,...,Gn : Ty, k: int, ly : Layer, d0, d1: DatatypeType ::
          //  { Eq(G0, .., Gn, S(ly), k, d0, d1) }
          //    0 < k ==>
          //      (Eq(G0, .., Gn, S(ly), k, d0, d1) <==>
          //       Eq(G0, .., Gn, ly, k, d0, d))
          CoAxHelper(typeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var eqDtSL = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var eqDtL  = CoEqualCall(codecl, lexprs, rexprs, k, ly, d0, d1);
            var body = BplImp(kIsNonZero, BplIff(eqDtSL, eqDtL));
            var ax = BplForall(vars, BplTrigger(eqDtSL), body);
            sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.tok, ax, "Unbump layer co-equality axiom"));
          });
        };

        AddAxioms(null); // Add the above axioms for $Equal

        // axiom (forall d0, d1: DatatypeType, k: int :: { $Equal(d0, d1) } :: Equal(d0, d1) <==> d0 == d1);
        CoAxHelper(null, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var Eq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var equal = Bpl.Expr.Eq(d0, d1);
          sink.AddTopLevelDeclaration(new Axiom(dt.tok,
            BplForall(vars, BplTrigger(Eq), BplIff(Eq, equal)),
            "Equality for codatatypes"));
        });

        Bpl.Type theTypeOfK = predef.BigOrdinalType;
        AddAxioms(predef.BigOrdinalType); // Add the above axioms for $PrefixEqual

        // The connection between the full codatatype equality and its prefix version
        // axiom (forall d0, d1: DatatypeType :: $Eq#Dt(d0, d1) <==>
        //                                       (forall k: int :: 0 <= k ==> $PrefixEqual#Dt(k, d0, d1)));
        CoAxHelper(theTypeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var Eq = CoEqualCall(codecl, lexprs, rexprs, null, LayerSucc(ly), d0, d1);
          var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          vars.Remove(kVar);
          sink.AddTopLevelDeclaration(new Axiom(dt.tok,
            BplForall(vars, BplTrigger(Eq), BplIff(Eq, BplForall(kVar, BplTrigger(PEq), BplImp(kIsValid, PEq)))),
            "Coequality and prefix equality connection"));
        });
        // In addition, the following special case holds for $Eq#Dt:
        // axiom (forall d0, d1: DatatypeType :: $Eq#Dt(d0, d1) <==
        //                                       (forall k: int :: 0 <= k ==> $PrefixEqual#Dt(ORD#FromNat(k), d0, d1)));
        if (!theTypeOfK.IsInt) {
          CoAxHelper(Bpl.Type.Int, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var Eq = CoEqualCall(codecl, lexprs, rexprs, null, LayerSucc(ly), d0, d1);
            var PEq = CoEqualCall(codecl, lexprs, rexprs, FunctionCall(k.tok, "ORD#FromNat", predef.BigOrdinalType, k), LayerSucc(ly), d0, d1);
            vars.Remove(kVar);
            sink.AddTopLevelDeclaration(new Axiom(dt.tok,
              BplForall(vars, BplTrigger(Eq), BplImp(BplForall(kVar, BplTrigger(PEq), BplImp(kIsValid, PEq)), Eq)),
              "Coequality and prefix equality connection"));
          });
        }

        // A consequence of the definition of prefix equalities is the following:
        // axiom (forall k, m: int, d0, d1: DatatypeType :: 0 <= k <= m && $PrefixEq#Dt(m, d0, d1) ==> $PrefixEq#0#Dt(k, d0, d1));
        CoAxHelper(theTypeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var m = BplBoundVar("m", k.Type, vars);
          var PEqK = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var PEqM = CoEqualCall(codecl, lexprs, rexprs, m, LayerSucc(ly), d0, d1);
          Bpl.Expr kLtM;
          if (k.Type.IsInt) {
            kLtM = Bpl.Expr.Lt(k, m);
          } else {
            kLtM = FunctionCall(dt.tok, "ORD#Less", Bpl.Type.Bool, k, m);
          }
          sink.AddTopLevelDeclaration(new Axiom(dt.tok,
            BplForall(vars,
            new Bpl.Trigger(dt.tok, true, new List<Bpl.Expr> { PEqK, PEqM }),
            BplImp(BplAnd(BplAnd(kIsValid, kLtM), PEqM), PEqK)),
            "Prefix equality consequence"));
        });

        // With the axioms above, going from d0==d1 to a prefix equality requires going via the full codatatype
        // equality, which in turn requires the full codatatype equality to be present.  The following axiom
        // provides a shortcut:
        // axiom (forall d0, d1: DatatypeType, k: int :: d0 == d1 && 0 <= k ==> $PrefixEqual#_module.Stream(k, d0, d1));
        CoAxHelper(theTypeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var equal = Bpl.Expr.Eq(d0, d1);
          var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var trigger = BplTrigger(PEq);
          sink.AddTopLevelDeclaration(new Axiom(dt.tok,
            BplForall(vars, trigger, BplImp(BplAnd(equal, kIsValid), PEq)), "Prefix equality shortcut"));
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
            var tyA = Resolver.SubstType(ty, lsu);
            var tyB = Resolver.SubstType(ty, rsu);
            var aa = CondApplyUnbox(tok, a, ty, tyA);
            var bb = CondApplyUnbox(tok, b, ty, tyB);
            var equal = new BinaryExpr(tok, BinaryExpr.Opcode.Eq, new BoogieWrapper(aa, tyA), new BoogieWrapper(bb, tyB));
            equal.ResolvedOp = Resolver.ResolveOp(equal.Op, tyA, tyB);  // resolve here
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

    public static Bpl.NAryExpr ReadHeap(IToken tok, Expr heap, Expr r)
    {
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

    void AddClassMembers(TopLevelDeclWithMembers c, bool includeMethods)
    {
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(c != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));
      Contract.Assert(VisibleInScope(c));

      sink.AddTopLevelDeclaration(GetClass(c));
      if (c is ArrayClassDecl) {
        // classes.Add(c, predef.ClassDotArray);
        AddAllocationAxiom(null, (ArrayClassDecl)c, true);
      }

      // Add $Is and $IsAlloc for this class :
      //    axiom (forall p: ref, G: Ty ::
      //       { $Is(p, TClassA(G), h) }
      //       $Is(p, TClassA(G), h) <=> (p == null || dtype(p) == TClassA(G));
      //    axiom (forall p: ref, h: Heap, G: Ty ::
      //       { $IsAlloc(p, TClassA(G), h) }
      //       $IsAlloc(p, TClassA(G), h) => (p == null || h[p, alloc]);
      MapM(c is ClassDecl ? Bools : new List<bool>(), is_alloc => {
        List<Bpl.Expr> tyexprs;
        var vars = MkTyParamBinders(GetTypeParams(c), out tyexprs);

        var o = BplBoundVar("$o", predef.RefType, vars);

        Bpl.Expr body, is_o;
        Bpl.Expr o_null = Bpl.Expr.Eq(o, predef.Null);
        Bpl.Expr o_ty = ClassTyCon(c, tyexprs);
        string name;

        if (is_alloc) {
          name = c + ": Class $IsAlloc";
          var h = BplBoundVar("$h", predef.HeapType, vars);
          // $IsAlloc(o, ..)
          is_o = MkIsAlloc(o, o_ty, h);
          body = BplIff(is_o, BplOr(o_null, IsAlloced(c.tok, h, o)));
        } else {
          name = c + ": Class $Is";
          // $Is(o, ..)
          is_o = MkIs(o, o_ty);
          Bpl.Expr rhs;
          if (c == program.BuiltIns.ObjectDecl) {
            rhs = Bpl.Expr.True;
          } else if (c is TraitDecl) {
            //generating $o == null || implements$J(dtype(x), typeArgs)
            var t = (TraitDecl)c;
            var dtypeFunc = FunctionCall(o.tok, BuiltinFunction.DynamicType, null, o);
            var implementsJ_Arguments = new List<Expr> { dtypeFunc }; // TODO: also needs type parameters
            implementsJ_Arguments.AddRange(tyexprs);
            Bpl.Expr implementsFunc = FunctionCall(t.tok, "implements$" + t.FullSanitizedName, Bpl.Type.Bool, implementsJ_Arguments);
            rhs = BplOr(o_null, implementsFunc);
          } else {
            rhs = BplOr(o_null, DType(o, o_ty));
          }
          body = BplIff(is_o, rhs);
        }

        sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, BplForall(vars, BplTrigger(is_o), body), name));
      });

      if (c is TraitDecl) {
        //this adds: function implements$J(Ty, typeArgs): bool;
        var vars = MkTyParamFormals(GetTypeParams(c));
        var arg_ref = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, predef.Ty), true);
        vars.Add(arg_ref);
        var res = new Bpl.Formal(c.tok, new Bpl.TypedIdent(c.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
        var implement_intr = new Bpl.Function(c.tok, "implements$" + c.FullSanitizedName, vars, res);
        sink.AddTopLevelDeclaration(implement_intr);
      } else if (c is ClassDecl) {
        //this adds: axiom implements$J(class.C, typeInstantiations);
        var vars = MkTyParamBinders(GetTypeParams(c), out var tyexprs);

        foreach (var parent in ((ClassDecl)c).ParentTraits) {
          var trait = (TraitDecl)((NonNullTypeDecl)((UserDefinedType)parent).ResolvedClass).ViewAsClass;
          var arg = ClassTyCon(c, tyexprs);
          var args = new List<Bpl.Expr> { arg };
          foreach (var targ in parent.TypeArgs) {
            args.Add(TypeToTy(targ));
          }
          var expr = FunctionCall(c.tok, "implements$" + trait.FullSanitizedName, Bpl.Type.Bool, args);
          var implements_axiom = new Bpl.Axiom(c.tok, BplForall(vars, null, expr));
          sink.AddTopLevelDeclaration(implements_axiom);
        }
      }

      foreach (MemberDecl member in c.Members.FindAll(VisibleInScope)) {
        Contract.Assert(isAllocContext == null);
        currentDeclaration = member;
        if (member is Field) {
          Field f = (Field)member;
          if (f is ConstantField) {
            // The following call has the side effect of idempotently creating and adding the function to the sink's top-level declarations
            Contract.Assert(currentModule == null);
            currentModule = f.EnclosingClass.EnclosingModuleDefinition;
            var oldFuelContext = fuelContext;
            fuelContext = FuelSetting.NewFuelContext(f);
            var boogieFunction = GetReadonlyField(f);
            fuelContext = oldFuelContext;
            currentModule = null;
            AddAllocationAxiom(f, c);
          } else {
            if (f.IsMutable) {
              Bpl.Constant fc = GetField(f);
              sink.AddTopLevelDeclaration(fc);
            } else {
              Bpl.Function ff = GetReadonlyField(f);
              if (ff != predef.ArrayLength)
                sink.AddTopLevelDeclaration(ff);
            }
            AddAllocationAxiom(f, c);
          }

        } else if (member is Function) {
          AddFunction_Top((Function)member);
        } else if (member is Method) {
          if (includeMethods || InVerificationScope(member) || referencedMembers.Contains(member)) {
            AddMethod_Top((Method)member);
          }
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member
        }
      }
    }

    void AddFunction_Top(Function f) {
      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(f);
      isAllocContext = new IsAllocContext(true);

      AddClassMember_Function(f);

      if (!f.IsBuiltin && InVerificationScope(f)) {
        AddWellformednessCheck(f);
        if (f.OverriddenFunction != null) { //it means that f is overriding its associated parent function
          AddFunctionOverrideCheckImpl(f);
        }
      }
      var cop = f as ExtremePredicate;
      if (cop != null) {
        AddClassMember_Function(cop.PrefixPredicate);
        // skip the well-formedness check, because it has already been done for the extreme predicate
      }
      this.fuelContext = oldFuelContext;
      isAllocContext = null;
    }

    void AddMethod_Top(Method m) {
      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(m);

      // wellformedness check for method specification
      if (m.EnclosingClass is IteratorDecl && m == ((IteratorDecl)m.EnclosingClass).Member_MoveNext) {
        // skip the well-formedness check, because it has already been done for the iterator
      } else {
        var proc = AddMethod(m, MethodTranslationKind.SpecWellformedness);
        sink.AddTopLevelDeclaration(proc);
        if (InVerificationScope(m)) {
          AddMethodImpl(m, proc, true);
        }
        if (m.OverriddenMethod != null && InVerificationScope(m)) //method has overrided a parent method
        {
          var procOverrideChk = AddMethod(m, MethodTranslationKind.OverrideCheck);
          sink.AddTopLevelDeclaration(procOverrideChk);
          AddMethodOverrideCheckImpl(m, procOverrideChk);
        }
      }
      // the method spec itself
      sink.AddTopLevelDeclaration(AddMethod(m, MethodTranslationKind.Call));
      if (m is ExtremeLemma) {
        // Let the CoCall and Impl forms to use m.PrefixLemma signature and specification (and
        // note that m.PrefixLemma.Body == m.Body.
        m = ((ExtremeLemma)m).PrefixLemma;
        sink.AddTopLevelDeclaration(AddMethod(m, MethodTranslationKind.CoCall));
      }
      if (m.Body != null && InVerificationScope(m)) {
        // ...and its implementation
        assertionCount = 0;
        var proc = AddMethod(m, MethodTranslationKind.Implementation);
        sink.AddTopLevelDeclaration(proc);
        AddMethodImpl(m, proc, false);
      }
      Reset();
      this.fuelContext = oldFuelContext;

    }

    /// <summary>
    /// Returns true if the body of function "f" is available in module "context".
    /// This happens when the following conditions all hold:
    ///   - "f" has a body
    ///   - "f" is not opaque
    /// </summary>
    static bool FunctionBodyIsAvailable(Function f, ModuleDefinition context, VisibilityScope scope, bool revealProtectedBody) {
      Contract.Requires(f != null);
      Contract.Requires(context != null);
      return f.Body != null && !IsOpaqueFunction(f) && f.IsRevealedInScope(scope);
    }
    static bool IsOpaqueFunction(Function f) {
      Contract.Requires(f != null);
      return Attributes.Contains(f.Attributes, "opaque");
    }
    static bool IsOpaqueRevealLemma(Method m) {
      Contract.Requires(m != null);
      return Attributes.Contains(m.Attributes, "opaque_reveal");
    }

    private void AddClassMember_Function(Function f) {
      Contract.Ensures(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);

      currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      codeContext = f;

      // declare function
      AddFunction(f);
      // add synonym axiom
      if (f.IsFuelAware()) {
        AddLayerSynonymAxiom(f);
        AddFuelSynonymAxiom(f);
      }
      // add frame axiom
      if (AlwaysUseHeap || f.ReadsHeap) {
        AddFrameAxiom(f);
      }
      // add consequence axiom
      AddFunctionConsequenceAxiom(f, f.Ens);
      // add definition axioms, suitably specialized for literals
      if (f.Body != null && RevealedInScope(f)) {
        AddFunctionAxiom(f, f.Body.Resolved);
      } else {
        // for body-less functions, at least generate its #requires function
        var b = FunctionAxiom(f, null, null);
        Contract.Assert(b == null);
      }
      // for a function in a class C that overrides a function in a trait J, add an axiom that connects J.F and C.F
      if (f.OverriddenFunction != null) {
        sink.AddTopLevelDeclaration(FunctionOverrideAxiom(f.OverriddenFunction, f));
      }

      // supply the connection between least/greatest predicates and prefix predicates
      if (f is ExtremePredicate) {
        AddPrefixPredicateAxioms(((ExtremePredicate)f).PrefixPredicate);
      }

      Reset();
    }

    void AddIteratorSpecAndBody(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      FuelContext oldFuelContext = this.fuelContext;
      this.fuelContext = FuelSetting.NewFuelContext(iter);
      isAllocContext = new IsAllocContext(false);

      // wellformedness check for method specification
      Bpl.Procedure proc = AddIteratorProc(iter, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);
      if (InVerificationScope(iter)){
        AddIteratorWellformed(iter, proc);
      }
      // the method itself
      if (iter.Body != null && InVerificationScope(iter)) {
        proc = AddIteratorProc(iter, MethodTranslationKind.Implementation);
        sink.AddTopLevelDeclaration(proc);
        // ...and its implementation
        AddIteratorImpl(iter, proc);
      }
      this.fuelContext = oldFuelContext;
      isAllocContext = null;
    }

    Bpl.Procedure AddIteratorProc(IteratorDecl iter, MethodTranslationKind kind) {
      Contract.Requires(iter != null);
      Contract.Requires(kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation);
      Contract.Requires(predef != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);

      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      var etran = new ExpressionTranslator(this, predef, iter.tok);

      var inParams = new List<Bpl.Variable>();
      List<Variable> outParams;
      GenerateMethodParametersChoose(iter.tok, iter, kind, true, true, false, etran, inParams, out outParams);

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
          string errorMessage = CustomErrorMessage(p.Attributes);
          if (p.Label != null && kind == MethodTranslationKind.Implementation) {
            // don't include this precondition here, but record it for later use
            p.Label.E = etran.Old.TrExpr(p.E);
          } else {
            foreach (var s in TrSplitExprForMethodSpec(p.E, etran, kind)) {
              if (kind == MethodTranslationKind.Call && RefinementToken.IsInherited(s.E.tok, currentModule)) {
                // this precondition was inherited into this module, so just ignore it
              } else {
                req.Add(Requires(s.E.tok, s.IsOnlyFree, s.E, errorMessage, comment));
                comment = null;
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }
        comment = "user-defined postconditions";
        foreach (var p in iter.Ensures) {
          foreach (var s in TrSplitExprForMethodSpec(p.E, etran, kind)) {
            if (kind == MethodTranslationKind.Implementation && RefinementToken.IsInherited(s.E.tok, currentModule)) {
              // this postcondition was inherited into this module, so just ignore it
            } else {
              ens.Add(Ensures(s.E.tok, s.IsOnlyFree, s.E, null, comment));
              comment = null;
            }
          }
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(iter.tok, iter.Modifies.Expressions, false, etran.Old, etran, etran.Old)) {
          ens.Add(Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
        }
      }

      var name = MethodName(iter, kind);
      var proc = new Bpl.Procedure(iter.tok, name, new List<Bpl.TypeVariable>(), inParams, outParams, req, mod, ens, etran.TrAttributes(iter.Attributes, null));

      currentModule = null;
      codeContext = null;

      return proc;
    }

    void AddEnsures(List<Bpl.Ensures> list, Bpl.Ensures ens) {
      list.Add(ens);
      if (!ens.Free) { this.assertionCount++; }
    }

    void AddIteratorWellformed(IteratorDecl iter, Procedure proc) {
      Contract.Requires(iter != null);
      Contract.Requires(proc != null);
      Contract.Requires(currentModule == null && codeContext == null);
      Contract.Ensures(currentModule == null && codeContext == null);

      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      var builder = new BoogieStmtListBuilder(this);
      var etran = new ExpressionTranslator(this, predef, iter.tok);
      var localVariables = new List<Variable>();
      GenerateIteratorImplPrelude(iter, inParams, new List<Variable>(), builder, localVariables);

      // check well-formedness of any default-value expressions (before assuming preconditions)
      foreach (var formal in iter.Ins.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformed(e, new WFOptions(null, false, false, true), localVariables, builder, etran);
        builder.Add(new Bpl.AssumeCmd(e.tok, CanCallAssumption(e, etran)));
        CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, builder);
      }
      // check well-formedness of the preconditions, and then assume each one of them
      foreach (var p in iter.Requires) {
        CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, builder, etran);
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
        builder.Add(TrAssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }

      // play havoc with the heap, except at the locations prescribed by (this._reads - this._modifies - {this})
      var th = new ThisExpr(iter);  // resolve here
      var rds = new MemberSelectExpr(iter.tok, th, iter.Member_Reads);
      var mod = new MemberSelectExpr(iter.tok, th, iter.Member_Modifies);
      builder.Add(new Bpl.CallCmd(iter.tok, "$IterHavoc0",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(mod) },
        new List<Bpl.IdentifierExpr>()));

      // assume the automatic yield-requires precondition (which is always well-formed):  this.Valid()
      var validCall = new FunctionCallExpr(iter.tok, "Valid", th, iter.tok, new List<Expression>());
      validCall.Function = iter.Member_Valid;  // resolve here
      validCall.Type = Type.Bool;  // resolve here
      validCall.TypeApplication_AtEnclosingClass = iter.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));  // resolve here
      validCall.TypeApplication_JustFunction = new List<Type>(); // resolved here

      builder.Add(TrAssumeCmd(iter.tok, etran.TrExpr(validCall)));

      // check well-formedness of the user-defined part of the yield-requires
      foreach (var p in iter.YieldRequires) {
        CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, builder, etran);
      }

      // save the heap (representing the state where yield-requires holds):  $_OldIterHeap := Heap;
      var oldIterHeap = new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, "$_OldIterHeap", predef.HeapType));
      localVariables.Add(oldIterHeap);
      builder.Add(Bpl.Cmd.SimpleAssign(iter.tok, new Bpl.IdentifierExpr(iter.tok, oldIterHeap), etran.HeapExpr));
      // simulate a modifies this, this._modifies, this._new;
      var nw = new MemberSelectExpr(iter.tok, th, iter.Member_New);
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
      builder.Add(TrAssumeCmd(iter.tok, yeEtran.TrExpr(cond)));

      // check wellformedness of postconditions
      var yeBuilder = new BoogieStmtListBuilder(this);
      var endBuilder = new BoogieStmtListBuilder(this);
      // In the yield-ensures case:  assume this.Valid();
      yeBuilder.Add(TrAssumeCmd(iter.tok, yeEtran.TrExpr(validCall)));
      Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
      for (int i = 0; i < iter.OutsFields.Count; i++) {
        var y = iter.OutsFields[i];
        var ys = iter.OutsHistoryFields[i];
        var thisY = new MemberSelectExpr(iter.tok, th, y);
        var thisYs = new MemberSelectExpr(iter.tok, th, ys);
        var oldThisYs = new OldExpr(iter.tok, thisYs);
        oldThisYs.Type = thisYs.Type;  // resolve here
        var singleton = new SeqDisplayExpr(iter.tok, new List<Expression>() { thisY });
        singleton.Type = thisYs.Type;  // resolve here
        var concat = new BinaryExpr(iter.tok, BinaryExpr.Opcode.Add, oldThisYs, singleton);
        concat.ResolvedOp = BinaryExpr.ResolvedOpcode.Concat; concat.Type = oldThisYs.Type;  // resolve here

        // In the yield-ensures case:  assume this.ys == old(this.ys) + [this.y];
        yeBuilder.Add(TrAssumeCmd(iter.tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(concat))));
        // In the ensures case:  assume this.ys == old(this.ys);
        endBuilder.Add(TrAssumeCmd(iter.tok, Bpl.Expr.Eq(yeEtran.TrExpr(thisYs), yeEtran.TrExpr(oldThisYs))));
      }

      foreach (var p in iter.YieldEnsures) {
        CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, yeBuilder, yeEtran);
      }
      foreach (var p in iter.Ensures) {
        CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, endBuilder, yeEtran);
      }
      builder.Add(new Bpl.IfCmd(iter.tok, null, yeBuilder.Collect(iter.tok), null, endBuilder.Collect(iter.tok)));

      Bpl.StmtList stmts = builder.Collect(iter.tok);

      if (EmitImplementation(iter.Attributes)) {
        QKeyValue kv = etran.TrAttributes(iter.Attributes, null);
        Bpl.Implementation impl = new Bpl.Implementation(iter.tok, proc.Name,
          new List<Bpl.TypeVariable>(), inParams, new List<Variable>(),
          localVariables, stmts, kv);
        sink.AddTopLevelDeclaration(impl);
      }

      Reset();
    }

    bool EmitImplementation(Attributes attributes) {
      // emit the impl only when there are proof obligations
      if (assertionCount > 0) {
        return true;
      } else {
        return false;
      }
    }
    void AddIteratorImpl(IteratorDecl iter, Bpl.Procedure proc) {
      Contract.Requires(iter != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(iter.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && yieldCountVariable == null && _tmpIEs.Count == 0);
      Contract.Ensures(currentModule == null && codeContext == null && yieldCountVariable == null && _tmpIEs.Count == 0);

      currentModule = iter.EnclosingModuleDefinition;
      codeContext = iter;

      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      Contract.Assert(1 <= inParams.Count);  // there should at least be a receiver parameter
      Contract.Assert(proc.OutParams.Count == 0);

      var builder = new BoogieStmtListBuilder(this);
      var etran = new ExpressionTranslator(this, predef, iter.tok);
      var localVariables = new List<Variable>();
      GenerateIteratorImplPrelude(iter, inParams, new List<Variable>(), builder, localVariables);

      // add locals for the yield-history variables and the extra variables
      // Assume the precondition and postconditions of the iterator constructor method
      foreach (var p in iter.Member_Init.Req) {
        if (p.Label != null) {
          // don't include this precondition here
          Contract.Assert(p.Label.E != null);  // it should already have been recorded
        } else {
          builder.Add(TrAssumeCmd(p.E.tok, etran.TrExpr(p.E)));
        }
      }
      foreach (var p in iter.Member_Init.Ens) {
        // these postconditions are two-state predicates, but that's okay, because we haven't changed anything yet
        builder.Add(TrAssumeCmd(p.E.tok, etran.TrExpr(p.E)));
      }
      // add the _yieldCount variable, and assume its initial value to be 0
      yieldCountVariable = new Bpl.LocalVariable(iter.tok,
        new Bpl.TypedIdent(iter.tok, iter.YieldCountVariable.AssignUniqueName(currentDeclaration.IdGenerator), TrType(iter.YieldCountVariable.Type)));
      yieldCountVariable.TypedIdent.WhereExpr = YieldCountAssumption(iter, etran);  // by doing this after setting "yieldCountVariable", the variable can be used by YieldCountAssumption
      localVariables.Add(yieldCountVariable);
      builder.Add(TrAssumeCmd(iter.tok, Bpl.Expr.Eq(new Bpl.IdentifierExpr(iter.tok, yieldCountVariable), Bpl.Expr.Literal(0))));
      // add a variable $_OldIterHeap
      var oih = new Bpl.IdentifierExpr(iter.tok, "$_OldIterHeap", predef.HeapType);
      Bpl.Expr wh = BplAnd(
        FunctionCall(iter.tok, BuiltinFunction.IsGoodHeap, null, oih),
        HeapSucc(oih, etran.HeapExpr));
      localVariables.Add(new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, "$_OldIterHeap", predef.HeapType, wh)));

      // do an initial YieldHavoc
      YieldHavoc(iter.tok, iter, builder, etran);

      // translate the body of the iterator
      var stmts = TrStmt2StmtList(builder, iter.Body, localVariables, etran);

      if (EmitImplementation(iter.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(iter.Attributes, null);

        Bpl.Implementation impl = new Bpl.Implementation(iter.tok, proc.Name,
          new List<Bpl.TypeVariable>(), inParams, new List<Variable>(),
          localVariables, stmts, kv);
        sink.AddTopLevelDeclaration(impl);
      }

      yieldCountVariable = null;
      Reset();
    }

    private void Reset()
    {
      currentModule = null;
      codeContext = null;
      CurrentIdGenerator.Reset();
      _tmpIEs.Clear();
      assertionCount = 0;
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

    public static Bpl.QKeyValue InlineAttribute(Bpl.IToken tok, Bpl.QKeyValue/*?*/ next = null) {
      Contract.Requires(tok != null);
      return new QKeyValue(tok, "inline", new List<object>(), next);
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
          IdentifierExpr ie = new IdentifierExpr(p.tok, p.AssignUniqueName(translator.currentDeclaration.IdGenerator));
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
            ReplacementExprs.Add(Translator.Substitute(e, null, substMap));
          }
          foreach (var rf in prev.ReplacementFormals) {
            if (rf != formal) {
              ReplacementFormals.Add(rf);
            }
          }
          foreach (var entry in prev.SubstMap) {
            SubstMap.Add(entry.Key, Translator.Substitute(entry.Value, null, substMap));
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

    void AddFunctionAxiom(Function f, Expression body) {
      Contract.Requires(f != null);
      Contract.Requires(body != null);

      var ax = FunctionAxiom(f, body, null);
      sink.AddTopLevelDeclaration(ax);
      // TODO(namin) Is checking f.Reads.Count==0 excluding Valid() of BinaryTree in the right way?
      //             I don't see how this in the decreasing clause would help there.
      if (!(f is ExtremePredicate) && f.CoClusterTarget == Function.CoCallClusterInvolvement.None && f.Reads.Count == 0) {
        var FVs = new HashSet<IVariable>();
        Type usesThis = null;
        bool dontCare0 = false, dontCare1 = false;
        var dontCareHeapAt = new HashSet<Label>();
        foreach (var e in f.Decreases.Expressions) {
          ComputeFreeVariables(e, FVs, ref dontCare0, ref dontCare1, dontCareHeapAt, ref usesThis);
        }

        var allFormals = new List<Formal>();
        var decs = new List<Formal>();
        if (f.IsStatic) {
          Contract.Assert(usesThis == null);
        } else {
          var surrogate = new ThisSurrogate(f.tok, Resolver.GetReceiverType(f.tok, f));
          allFormals.Add(surrogate);
          if (usesThis != null) {
            decs.Add(surrogate);
          }
        }
        foreach (var formal in f.Formals) {
          allFormals.Add(formal);
          if (FVs.Contains(formal)) {
            decs.Add(formal);
          }
        }

        Contract.Assert(decs.Count <= allFormals.Count);
        if (0 < decs.Count && decs.Count < allFormals.Count) {
          ax = FunctionAxiom(f, body, decs);
          sink.AddTopLevelDeclaration(ax);
        }

        ax = FunctionAxiom(f, body, allFormals);
        sink.AddTopLevelDeclaration(ax);
      }
    }

    void AddFunctionConsequenceAxiom(Function f, List<AttributedExpression> ens) {
      Contract.Requires(f != null);
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);

      bool readsHeap = AlwaysUseHeap || f.ReadsHeap;
      foreach (AttributedExpression e in f.Req.Concat(ens)) {
        readsHeap = readsHeap || UsesHeap(e.E);
      }

      ExpressionTranslator etranHeap;
      ExpressionTranslator etran;
      Bpl.BoundVariable bvPrevHeap = null;
      if (f is TwoStateFunction) {
        bvPrevHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        etran = new ExpressionTranslator(this, predef,
          f.ReadsHeap ? new Bpl.IdentifierExpr(f.tok, predef.HeapVarName, predef.HeapType) : null,
          new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
        etranHeap = etran;
      } else {
        etranHeap = new ExpressionTranslator(this, predef, f.tok);
        etran = readsHeap ? etranHeap : new ExpressionTranslator(this, predef, (Bpl.Expr)null);
      }

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
      if (f.IsFuelAware()) {
        layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
        formals.Add(layer);
        etran = etran.WithCustomFuelSetting(new CustomFuelSettings{ {f, new FuelSetting(this, 0, new Bpl.IdentifierExpr(f.tok, layer))} });
        //etran = etran.WithLayer(new Bpl.IdentifierExpr(f.tok, layer));
        // Note, "layer" is not added to "args" here; rather, that's done below, as needed
      } else {
        layer = null;
      }

      Bpl.Expr ante = Bpl.Expr.True;
      Bpl.Expr anteIsAlloc = Bpl.Expr.True;
      if (f is TwoStateFunction) {
        Contract.Assert(bvPrevHeap != null);
        formals.Add(bvPrevHeap);
        args.Add(etran.Old.HeapExpr);
        // ante:  $IsGoodHeap($prevHeap) &&
        ante = BplAnd(ante, FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr));
      }
      var bvHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      if (AlwaysUseHeap || f.ReadsHeap) {
        args.Add(new Bpl.IdentifierExpr(f.tok, bvHeap));
      }
      // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
      if (readsHeap) {
        Bpl.Expr goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
        formals.Add(bvHeap);
        ante = BplAnd(ante, goodHeap);
      }
      if (f is TwoStateFunction && f.ReadsHeap) {
        ante = BplAnd(ante, HeapSucc(etran.Old.HeapExpr, etran.HeapExpr));
      }

      if (!f.IsStatic) {
        var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, TrReceiverType(f)));
        formals.Add(bvThis);
        var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        args.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(
          ReceiverNotNull(bvThisIdExpr),
          (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, bvThisIdExpr, thisType));
        ante = BplAnd(ante, wh);
      }
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (Formal p in f.Formals) {
        var bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), TrType(p.Type)));
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        formals.Add(bv);
        args.Add(formal);
        // add well-typedness conjunct to antecedent
        Bpl.Expr wh = GetWhereClause(p.tok, formal, p.Type, p.IsOld ? etran.Old : etran, NOALLOC);
        if (wh != null) { ante = BplAnd(ante, wh); }
        wh = GetWhereClause(p.tok, formal, p.Type, etranHeap, ISALLOC);
        if (wh != null) { anteIsAlloc = BplAnd(anteIsAlloc, wh); }
      }

      Bpl.Expr funcAppl;
      {
        var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        var funcArgs = new List<Bpl.Expr>();
        funcArgs.AddRange(tyargs);
        /*
        if (f.IsFueled) {
            funcArgs.Add(etran.layerInterCluster.GetFunctionFuel(f));
        } else if (layer != null) {
           var ly = new Bpl.IdentifierExpr(f.tok, layer);
           funcArgs.Add(FunctionCall(f.tok, BuiltinFunction.LayerSucc, null, ly));
        }
         */
        if (layer != null) {
          funcArgs.Add(new Bpl.IdentifierExpr(f.tok, layer));
        }

        funcArgs.AddRange(args);
        funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
      }

      Bpl.Expr pre = Bpl.Expr.True;
      foreach (AttributedExpression req in f.Req) {
        pre = BplAnd(pre, etran.TrExpr(Substitute(req.E, null, substMap)));
      }
      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight)
      var mod = f.EnclosingClass.EnclosingModuleDefinition;
      Bpl.Expr useViaContext = !InVerificationScope(f) ? Bpl.Expr.True :
        (Bpl.Expr)Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight());
      // useViaCanCall: f#canCall(args)
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

      // ante := useViaCanCall || (useViaContext && typeAnte && pre)
      ante = Bpl.Expr.Or(useViaCanCall, BplAnd(useViaContext, BplAnd(ante, pre)));

      Bpl.Trigger tr = BplTriggerHeap(this, f.tok, funcAppl,
        (AlwaysUseHeap || f.ReadsHeap || !readsHeap) ? null : etran.HeapExpr);
      Bpl.Expr post = Bpl.Expr.True;
      // substitute function return value with the function call.
      if (f.Result != null) {
        substMap.Add(f.Result, new BoogieWrapper(funcAppl, f.ResultType));
      }
      foreach (AttributedExpression p in ens) {
        Bpl.Expr q = etran.TrExpr(Substitute(p.E, null, substMap));
        post = BplAnd(post, q);
      }
      Bpl.Expr whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etran, NOALLOC);
      if (whr != null) { post = Bpl.Expr.And(post, whr); }

      Bpl.Expr ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), formals, null, tr, Bpl.Expr.Imp(ante, post));
      var activate = AxiomActivation(f, etran);
      string comment = "consequence axiom for " + f.FullSanitizedName;
      sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment));

      if (CommonHeapUse && !readsHeap) {
        whr = GetWhereClause(f.tok, funcAppl, f.ResultType, etranHeap, NOALLOC, true);
        if (whr != null) {
          Bpl.Expr goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etranHeap.HeapExpr);
          formals = Util.Cons(bvHeap, formals);
          ante = BplAnd(ante, goodHeap);
          ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), formals, null, BplTrigger(whr), Bpl.Expr.Imp(ante, whr));
          activate = AxiomActivation(f, etran);
          sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax)));
        }
      }
    }

    Bpl.Expr AxiomActivation(Function f, ExpressionTranslator etran) {
      Contract.Requires(f != null);
      Contract.Requires(etran != null);
      Contract.Requires(VisibleInScope(f));
      var module = f.EnclosingClass.EnclosingModuleDefinition;

      if (InVerificationScope(f)) {
        return
          Bpl.Expr.Le(Bpl.Expr.Literal(module.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight());
      } else {
        return Bpl.Expr.True;
      }
    }

    /// <summary>
    /// The list of formals "lits" is allowed to contain an object of type ThisSurrogate, which indicates that
    /// the receiver parameter of the function should be included among the lit formals.
    /// </summary>
    Bpl.Axiom FunctionAxiom(Function f, Expression/*?*/ body, List<Formal>/*?*/ lits) {
      Contract.Requires(f != null);
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Ensures((Contract.Result<Bpl.Axiom>() == null) == (body == null));  // return null iff body is null

      // This method generates the Definition Axiom, suitably modified according to the optional "lits".
      //
      // axiom  // definition axiom
      //   AXIOM_ACTIVATION
      //   ==>
      //   (forall s, $Heap, formals ::                  // let args := $Heap,formals
      //       { f(Succ(s), args) }                      // (*)
      //       (f#canCall(args) || USE_VIA_CONTEXT)
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

      bool readsHeap = AlwaysUseHeap || f.ReadsHeap;
      foreach (AttributedExpression e in f.Req) {
        readsHeap = readsHeap || UsesHeap(e.E);
      }
      if (body != null && UsesHeap(body)) {
        readsHeap = true;
      }

      ExpressionTranslator etran;
      Bpl.BoundVariable bvPrevHeap = null;
      if (f is TwoStateFunction) {
        bvPrevHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        etran = new ExpressionTranslator(this, predef,
          f.ReadsHeap ? new Bpl.IdentifierExpr(f.tok, predef.HeapVarName, predef.HeapType) : null,
          new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
      } else {
        etran = readsHeap ?
          new ExpressionTranslator(this, predef, f.tok) :
          new ExpressionTranslator(this, predef, (Bpl.Expr)null);
      }

      // quantify over the type arguments, and add them first to the arguments
      List<Bpl.Expr> args = new List<Bpl.Expr>();
      List<Bpl.Expr> tyargs = GetTypeArguments(f, null).ConvertAll(TypeToTy);

      var forallFormals = MkTyParamBinders(GetTypeParams(f), out _);
      var funcFormals = MkTyParamBinders(GetTypeParams(f), out _);
      var reqFuncArguments = new List<Bpl.Expr>(tyargs);

      Bpl.BoundVariable layer;
      if (f.IsFuelAware()) {
        layer = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType));
        forallFormals.Add(layer);
        funcFormals.Add(layer);
        reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, layer));
        // Note, "layer" is not added to "args" here; rather, that's done below, as needed
      } else {
        layer = null;
      }

      Bpl.Expr ante = Bpl.Expr.True;
      if (f is TwoStateFunction) {
        Contract.Assert(bvPrevHeap != null);
        forallFormals.Add(bvPrevHeap);
        funcFormals.Add(bvPrevHeap);
        args.Add(etran.Old.HeapExpr);
        reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
        // ante:  $IsGoodHeap($prevHeap) &&
        ante = BplAnd(ante, FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.Old.HeapExpr));
      }
      Bpl.Expr goodHeap = null;
      var bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
      if (AlwaysUseHeap || f.ReadsHeap) {
        funcFormals.Add(bv);
      }
      if (AlwaysUseHeap || f.ReadsHeap) {
        args.Add(new Bpl.IdentifierExpr(f.tok, bv));
        reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bv));
      }
      // ante:  $IsGoodHeap($Heap) && $HeapSucc($prevHeap, $Heap) && this != null && formals-have-the-expected-types &&
      if (readsHeap) {
        forallFormals.Add(bv);
        goodHeap = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr);
        ante = BplAnd(ante, goodHeap);
      }
      if (f is TwoStateFunction && f.ReadsHeap) {
        ante = BplAnd(ante, HeapSucc(etran.Old.HeapExpr, etran.HeapExpr));
      }

      Expression receiverReplacement = null;
      if (!f.IsStatic) {
        var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, TrReceiverType(f)));
        forallFormals.Add(bvThis);
        funcFormals.Add(bvThis);
        reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bvThis));
        var bvThisIdExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
        if (lits != null && lits.Exists(p => p is ThisSurrogate)) {
          args.Add(Lit(bvThisIdExpr));
          var th = new ThisExpr(f);
          var l = new UnaryOpExpr(f.tok, UnaryOpExpr.Opcode.Lit, th) {
            Type = th.Type
          };
          receiverReplacement = l;
        } else {
          args.Add(bvThisIdExpr);
        }
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(f.tok, f);
        Bpl.Expr wh = Bpl.Expr.And(
          ReceiverNotNull(bvThisIdExpr),
          (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, bvThisIdExpr, thisType));
        ante = BplAnd(ante, wh);
      }

      var typeMap = new Dictionary<TypeParameter, Type>();
      var anteReqAxiom = ante;  // note that antecedent so far is the same for #requires axioms, even the receiver parameter of a two-state function
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (Formal p in f.Formals) {
        var pType = Resolver.SubstType(p.Type, typeMap);
        bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), TrType(pType)));
        forallFormals.Add(bv);
        funcFormals.Add(bv);
        reqFuncArguments.Add(new Bpl.IdentifierExpr(f.tok, bv));
        Bpl.Expr formal = new Bpl.IdentifierExpr(p.tok, bv);
        if (lits != null && lits.Contains(p) && !substMap.ContainsKey(p)) {
          args.Add(Lit(formal));
          var ie = new IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator));
          ie.Var = p; ie.Type = ie.Var.Type;
          var l = new UnaryOpExpr(p.tok, UnaryOpExpr.Opcode.Lit, ie);
          l.Type = ie.Var.Type;
          substMap.Add(p, l);
        } else {
          args.Add(formal);
        }
        // add well-typedness conjunct to antecedent
        Bpl.Expr wh = GetWhereClause(p.tok, formal, pType, p.IsOld ? etran.Old : etran, NOALLOC);
        if (wh != null) { ante = BplAnd(ante, wh); }
        wh = GetWhereClause(p.tok, formal, pType, etran, NOALLOC);
        if (wh != null) { anteReqAxiom = BplAnd(anteReqAxiom, wh); }
      }

      Bpl.Expr pre = Bpl.Expr.True;
      foreach (AttributedExpression req in f.Req) {
        pre = BplAnd(pre, etran.TrExpr(Substitute(req.E, receiverReplacement, substMap)));
      }
      var preReqAxiom = pre;
      if (f is TwoStateFunction) {
        // Checked preconditions that old parameters really existed in previous state
        var index = 0;
        Bpl.Expr preRA = Bpl.Expr.True;
        foreach (var formal in f.Formals) {
          if (formal.IsOld) {
            var dafnyFormalIdExpr = new IdentifierExpr(formal.tok, formal);
            preRA = BplAnd(preRA, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, etran.Old.HeapExpr));
          }
          index++;
        }
        preReqAxiom = BplAnd(preRA, pre);
      }

      // Add the precondition function and its axiom (which is equivalent to the anteReqAxiom)
      if (body == null || (RevealedInScope(f) && lits == null)) {
        var precondF = new Bpl.Function(f.tok,
          RequiresName(f), new List<Bpl.TypeVariable>(),
          funcFormals.ConvertAll(v => (Bpl.Variable)BplFormalVar(null, v.TypedIdent.Type, true)),
          BplFormalVar(null, Bpl.Type.Bool, false));
        sink.AddTopLevelDeclaration(precondF);

        var appl = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, reqFuncArguments);
        Bpl.Trigger trig = BplTriggerHeap(this, f.tok, appl, readsHeap ? etran.HeapExpr : null);
        // axiom (forall params :: { f#requires(params) }  ante ==> f#requires(params) == pre);
        sink.AddTopLevelDeclaration(new Axiom(f.tok,
          BplForall(forallFormals, trig, BplImp(anteReqAxiom, Bpl.Expr.Eq(appl, preReqAxiom))),
          "#requires axiom for " + f.FullSanitizedName));
      }
      if (body == null || !RevealedInScope(f)) {
        return null;
      }

      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight)
      ModuleDefinition mod = f.EnclosingClass.EnclosingModuleDefinition;
      Bpl.Expr useViaContext = !InVerificationScope(f) ? (Bpl.Expr)Bpl.Expr.True :
        Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(f)), etran.FunctionContextHeight());
      // ante := (useViaContext && typeAnte && pre)
      ante = BplAnd(useViaContext, BplAnd(ante, pre));

      // useViaCanCall: f#canCall(args)
      Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName + "#canCall", Bpl.Type.Bool);
      Bpl.Expr useViaCanCall = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(canCallFuncID), Concat(tyargs, args));

      // ante := useViaCanCall || (useViaContext && typeAnte && pre)
      ante = Bpl.Expr.Or(useViaCanCall, ante);

      Bpl.Expr funcAppl;
      {
        var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        var funcArgs = new List<Bpl.Expr>();
        funcArgs.AddRange(tyargs);
        if (layer != null) {
          var ly = new Bpl.IdentifierExpr(f.tok, layer);
          //if (lits == null) {
            funcArgs.Add(LayerSucc(ly));
          //} else {
          //  funcArgs.Add(ly);
          //}
        }
        funcArgs.AddRange(args);
        funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), funcArgs);
      }

      Bpl.Trigger tr = BplTriggerHeap(this, f.tok, funcAppl, readsHeap ? etran.HeapExpr : null);
      Bpl.Expr tastyVegetarianOption; // a.k.a. the "meat" of the operation :)
      if (!RevealedInScope(f)) {
        tastyVegetarianOption = Bpl.Expr.True;
      } else {
        var bodyWithSubst = Substitute(body, receiverReplacement, substMap);
        if (f is PrefixPredicate) {
          var pp = (PrefixPredicate)f;
          bodyWithSubst = PrefixSubstitution(pp, bodyWithSubst);
        }
        Bpl.Expr ly = null;
        if (layer != null) {
          ly = new Bpl.IdentifierExpr(f.tok, layer);
          if (lits != null) {   // Lit axiom doesn't consume any fuel
            ly = LayerSucc(ly);
          }
        }
        var etranBody = layer == null ? etran : etran.LimitedFunctions(f, ly);
        var trbody = etranBody.TrExpr(bodyWithSubst);
        tastyVegetarianOption = BplAnd(CanCallAssumption(bodyWithSubst, etranBody),
          BplAnd(TrFunctionSideEffect(bodyWithSubst, etranBody), Bpl.Expr.Eq(funcAppl, trbody)));
      }
      QKeyValue kv = null;
      if (lits != null) {
        kv = new QKeyValue(f.tok, "weight", new List<object>() { Bpl.Expr.Literal(3) }, null);
      }
      Bpl.Expr ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), forallFormals, kv, tr, Bpl.Expr.Imp(ante, tastyVegetarianOption));
      var activate = AxiomActivation(f, etran);
      string comment;
      comment = "definition axiom for " + f.FullSanitizedName;
      if (lits != null) {
        if (lits.Count == f.Formals.Count + (f.IsStatic ? 0 : 1)) {
          comment += " for all literals";
        } else {
          comment += " for decreasing-related literals";
        }
      }
      if (RevealedInScope(f)) {
        comment += " (revealed)";
      } else {
        comment += " (opaque)";
      }
      return new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    }

    /// <summary>
    /// Essentially, the function override axiom looks like:
    ///   axiom (forall $heap: HeapType, typeArgs: Ty, this: ref, x#0: int, fuel: LayerType ::
    ///     { J.F(fuel, $heap, G(typeArgs), this, x#0), C.F(fuel, $heap, typeArgs, this, x#0) }
    ///     { J.F(fuel, $heap, G(typeArgs), this, x#0), $Is(this, C) }
    ///     this != null && $Is(this, C)
    ///     ==>
    ///     J.F(fuel, $heap, G(typeArgs), this, x#0) == C.F(fuel, $heap, typeArgs, this, x#0));
    /// (without the other usual antecedents).  Essentially, the override gives a part of the body of the
    /// trait's function, so we call FunctionAxiom to generate a conditional axiom (that is, we pass in the "overridingFunction"
    /// parameter to FunctionAxiom, which will add 'dtype(this) == class.C' as an additional antecedent) for a
    /// body of 'C.F(this, x#0)'.
    /// </summary>
    Bpl.Axiom FunctionOverrideAxiom(Function f, Function overridingFunction) {
      Contract.Requires(f != null);
      Contract.Requires(overridingFunction != null);
      Contract.Requires(predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Requires(!f.IsStatic);
      Contract.Requires(overridingFunction.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Ensures(Contract.Result<Bpl.Axiom>() != null);

      bool readsHeap = AlwaysUseHeap || f.ReadsHeap || overridingFunction.ReadsHeap;

      ExpressionTranslator etran;
      Bpl.BoundVariable bvPrevHeap = null;
      if (f is TwoStateFunction) {
        bvPrevHeap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        etran = new ExpressionTranslator(this, predef,
          f.ReadsHeap ? new Bpl.IdentifierExpr(f.tok, predef.HeapVarName, predef.HeapType) : null,
          new Bpl.IdentifierExpr(f.tok, bvPrevHeap));
      } else if (readsHeap) {
        etran = new ExpressionTranslator(this, predef, f.tok);
      } else {
        etran = new ExpressionTranslator(this, predef, (Bpl.Expr)null);
      }

      // "forallFormals" is built to hold the bound variables of the quantification
      // argsJF are the arguments to J.F (the function in the trait)
      // argsCF are the arguments to C.F (the overriding function)
      var forallFormals = new List<Bpl.Variable>();
      var argsJF = new List<Bpl.Expr>();
      var argsCF = new List<Bpl.Expr>();

      // Add type arguments
      forallFormals.AddRange(MkTyParamBinders(GetTypeParams(overridingFunction), out _));
      argsJF.AddRange(GetTypeArguments(f, overridingFunction).ConvertAll(TypeToTy));
      argsCF.AddRange(GetTypeArguments(overridingFunction, null).ConvertAll(TypeToTy));

      // Add the fuel argument
      if (f.IsFuelAware()) {
        Contract.Assert(overridingFunction.IsFuelAware());  // f.IsFuelAware() ==> overridingFunction.IsFuelAware()
        var fuel = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$fuel", predef.LayerType));
        forallFormals.Add(fuel);
        var ly = new Bpl.IdentifierExpr(f.tok, fuel);
        argsJF.Add(ly);
        argsCF.Add(ly);
      } else if (overridingFunction.IsFuelAware()) {
        // We can't use a bound variable $fuel, because then one of the triggers won't be mentioning this $fuel.
        // Instead, we do the next best thing: use the literal $LZ.
        var ly = new Bpl.IdentifierExpr(f.tok, "$LZ",predef.LayerType); // $LZ
        argsCF.Add(ly);
      }

      // Add heap arguments
      if (f is TwoStateFunction) {
        Contract.Assert(bvPrevHeap != null);
        forallFormals.Add(bvPrevHeap);
        argsJF.Add(etran.Old.HeapExpr);
        argsCF.Add(etran.Old.HeapExpr);
      }
      if (AlwaysUseHeap || f.ReadsHeap || overridingFunction.ReadsHeap) {
        var heap = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, predef.HeapVarName, predef.HeapType));
        forallFormals.Add(heap);
        if (AlwaysUseHeap || f.ReadsHeap) {
          argsJF.Add(new Bpl.IdentifierExpr(f.tok, heap));
        }
        if (AlwaysUseHeap || overridingFunction.ReadsHeap) {
          argsCF.Add(new Bpl.IdentifierExpr(overridingFunction.tok, heap));
        }
      }

      // Add receiver parameter
      Type thisType = Resolver.GetReceiverType(f.tok, overridingFunction);
      var bvThis = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, etran.This, TrType(thisType)));
      forallFormals.Add(bvThis);
      var bvThisExpr = new Bpl.IdentifierExpr(f.tok, bvThis);
      argsJF.Add(bvThisExpr);
      argsCF.Add(bvThisExpr);
      // $Is(this, C)
      var isOfSubtype = GetWhereClause(overridingFunction.tok, bvThisExpr, thisType, f is TwoStateFunction ? etran.Old : etran, IsAllocType.NEVERALLOC);

      // Add other arguments
      var typeMap = GetTypeArgumentSubstitutionMap(f, overridingFunction);
      foreach (Formal p in f.Formals) {
        var pType = Resolver.SubstType(p.Type, typeMap);
        var bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(currentDeclaration.IdGenerator), TrType(pType)));
        forallFormals.Add(bv);
        var jfArg = new Bpl.IdentifierExpr(p.tok, bv);
        argsJF.Add(ModeledAsBoxType(p.Type) ? BoxIfUnboxed(jfArg, pType) : jfArg);
        argsCF.Add(new Bpl.IdentifierExpr(p.tok, bv));
      }

      // useViaContext: (mh != ModuleContextHeight || fh != FunctionContextHeight)
      ModuleDefinition mod = f.EnclosingClass.EnclosingModuleDefinition;
      Bpl.Expr useViaContext = !InVerificationScope(overridingFunction) ? (Bpl.Expr)Bpl.Expr.True :
        Bpl.Expr.Neq(Bpl.Expr.Literal(mod.CallGraph.GetSCCRepresentativeId(overridingFunction)), etran.FunctionContextHeight());

      Bpl.Expr funcAppl;
      {
        var funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), argsJF);
      }
      Bpl.Expr overridingFuncAppl;
      {
        var funcID = new Bpl.IdentifierExpr(overridingFunction.tok, overridingFunction.FullSanitizedName, TrType(overridingFunction.ResultType));
        overridingFuncAppl = new Bpl.NAryExpr(overridingFunction.tok, new Bpl.FunctionCall(funcID), argsCF);
      }

      // Build the triggers
      // { f(Succ(s), args), f'(Succ(s), args') }
      Bpl.Trigger tr = BplTriggerHeap(this, overridingFunction.tok,
        funcAppl,
        readsHeap ? etran.HeapExpr : null,
        overridingFuncAppl);
      // { f(Succ(s), args), $Is(this, T') }
      var exprs = new List<Bpl.Expr>() {funcAppl, isOfSubtype};
      if (readsHeap) {
        exprs.Add(FunctionCall(overridingFunction.tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr));
      }
      tr = new Bpl.Trigger(overridingFunction.tok, true, exprs, tr);

      // The equality that is what it's all about
      var synonyms = Bpl.Expr.Eq(
        funcAppl,
        ModeledAsBoxType(f.ResultType) ? BoxIfUnboxed(overridingFuncAppl, overridingFunction.ResultType) : overridingFuncAppl);

      // The axiom
      Bpl.Expr ax = BplForall(f.tok, new List<Bpl.TypeVariable>(), forallFormals, null, tr,
        Bpl.Expr.Imp(Bpl.Expr.And(ReceiverNotNull(bvThisExpr), isOfSubtype), synonyms));
      var activate = AxiomActivation(f, etran);
      string comment = "override axiom for " + f.FullSanitizedName + " in class " + overridingFunction.EnclosingClass.FullSanitizedName;
      return new Bpl.Axiom(f.tok, Bpl.Expr.Imp(activate, ax), comment);
    }

    Bpl.Type TrReceiverType(MemberDecl f) {
      Contract.Requires(f != null);
      return TrType(Resolver.GetReceiverType(f.tok, f));
    }

    Bpl.Expr ReceiverNotNull(Bpl.Expr th) {
      Contract.Requires(th != null);
      if (th.Type == predef.RefType) {
        return Bpl.Expr.Neq(th, predef.Null);
      } else {
        return Bpl.Expr.True;
      }
    }

    Expr TrFunctionSideEffect(Expression expr, ExpressionTranslator etran) {
      Expr e = Bpl.Expr.True;
      if (expr is StmtExpr) {
        // if there is a call to reveal_ lemma, we need to record its side effect.
        var stmt = ((StmtExpr)expr).S;
        e = TrFunctionSideEffect(stmt, etran);
      }
      return e;
    }

    Expr TrFunctionSideEffect(Statement stmt, ExpressionTranslator etran) {
      Expr e = Bpl.Expr.True;
      e = TrStmtSideEffect(e, stmt, etran);
      foreach (var ss in stmt.SubStatements) {
        e = TrStmtSideEffect(e, ss, etran);
      }
      return e;
    }

    Expr TrStmtSideEffect(Expr e, Statement stmt, ExpressionTranslator etran) {
      if (stmt is CallStmt) {
        var call = (CallStmt)stmt;
        var m = call.Method;
        if (IsOpaqueRevealLemma(m)) {
          List<Expression> args = Attributes.FindExpressions(m.Attributes, "fuel");
          if (args != null) {
            MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
            if (selectExpr != null) {
              Function f = selectExpr.Member as Function;
              FuelConstant fuelConstant = this.functionFuel.Find(x => x.f == f);
              if (fuelConstant != null) {
                Bpl.Expr startFuel = fuelConstant.startFuel;
                Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
                Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, predef, f.IdGenerator);
                Bpl.Expr layer = etran.layerInterCluster.LayerN(1, moreFuel_expr);
                Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(2, moreFuel_expr);

                e = BplAnd(e, Bpl.Expr.Eq(startFuel, layer));
                e = BplAnd(e, Bpl.Expr.Eq(startFuelAssert, layerAssert));
                e = BplAnd(e, Bpl.Expr.Eq(this.FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, moreFuel_expr), moreFuel_expr));
              }
            }
          }
        }
      } else if (stmt is RevealStmt) {
        var reveal = (RevealStmt)stmt;
        foreach (var s in reveal.ResolvedStatements) {
          e = BplAnd(e, TrFunctionSideEffect(s, etran));
        }
      }
      return e;
    }

    /// <summary>
    /// For an extreme predicate P, "pp" is the prefix predicate for P (such that P = pp.ExtremePred) and
    /// "body" is the body of P.  Return what would be the body of the prefix predicate pp.
    /// In particular, return
    /// #if _k has type nat:
    ///   0 LESS _k  IMPLIES  body'                        // for greatest predicates
    ///   0 LESS _k  AND  body'                            // for least predicates
    /// #elsif _k has type ORDINAL:
    ///   (0 LESS ORD#Offset(_k)  IMPLIES  body') AND
    ///   (0 == ORD#Offset(_k) IMPLIES forall _k':ORDINAL :: _k' LESS _k ==> pp(_k', args))  // for greatest predicates
    ///   (0 == ORD#Offset(_k) IMPLIES exists _k':ORDINAL :: _k' LESS _k && pp(_k', args))   // for least predicates
    /// #endif
    /// where body' is body with the formals of P replaced by the corresponding
    /// formals of pp and with self-calls P(s) replaced by recursive calls to
    /// pp(_k - 1, s).
    /// </summary>
    Expression PrefixSubstitution(PrefixPredicate pp, Expression body) {
      Contract.Requires(pp != null);

      var typeMap = Util.Dict<TypeParameter,Type>(pp.ExtremePred.TypeArgs, Map(pp.TypeArgs, x => new UserDefinedType(x)));

      var paramMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < pp.ExtremePred.Formals.Count; i++) {
        var replacement = pp.Formals[i + 1];  // the +1 is to skip pp's _k parameter
        var param = new IdentifierExpr(replacement.tok, replacement.Name);
        param.Var = replacement;  // resolve here
        param.Type = replacement.Type;  // resolve here
        paramMap.Add(pp.ExtremePred.Formals[i], param);
      }

      var k = new IdentifierExpr(pp.tok, pp.K.Name);
      k.Var = pp.K;  // resolve here
      k.Type = pp.K.Type;  // resolve here
      Expression kMinusOne = Expression.CreateSubtract(k, Expression.CreateNatLiteral(pp.tok, 1, pp.K.Type));

      var s = new PrefixCallSubstituter(null, paramMap, typeMap, pp.ExtremePred, kMinusOne);
      body = s.Substitute(body);

      if (pp.K.Type.IsBigOrdinalType) {
        // 0 < k.Offset
        Contract.Assume(program.BuiltIns.ORDINAL_Offset != null);  // should have been filled in by the resolver
        var kOffset = new MemberSelectExpr(pp.tok, k, program.BuiltIns.ORDINAL_Offset);
        var kIsPositive = Expression.CreateLess(Expression.CreateIntLiteral(pp.tok, 0), kOffset);
        var kIsLimit = Expression.CreateEq(Expression.CreateIntLiteral(pp.tok, 0), kOffset, Type.Int);
        var kprimeVar = new BoundVar(pp.tok, "_k'", Type.BigOrdinal);
        var kprime = new IdentifierExpr(pp.tok, kprimeVar);

        var substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(pp.K, kprime);
        Expression recursiveCallReceiver;
        List<Expression> recursiveCallArgs;
        RecursiveCallParameters(pp.tok, pp, pp.TypeArgs, pp.Formals, substMap, out recursiveCallReceiver, out recursiveCallArgs);
        var ppCall = new FunctionCallExpr(pp.tok, pp.Name, recursiveCallReceiver, pp.tok, recursiveCallArgs);
        ppCall.Function = pp;
        ppCall.Type = Type.Bool;
        ppCall.TypeApplication_AtEnclosingClass = pp.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
        ppCall.TypeApplication_JustFunction = pp.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));

        Attributes triggerAttr = new Attributes("trigger", new List<Expression> { ppCall }, null);
        Expression limitCalls;
        if (pp.ExtremePred is GreatestPredicate) {
          // forall k':ORDINAL | _k' LESS _k :: pp(_k', args)
          var smaller = Expression.CreateLess(kprime, k);
          limitCalls = new ForallExpr(pp.tok, new List<BoundVar> { kprimeVar }, smaller, ppCall, triggerAttr);
          limitCalls.Type = Type.Bool;  // resolve here
        } else {
          // exists k':ORDINAL | _k' LESS _k :: pp(_k', args)
          // Here, instead of using the usual ORD#Less, we use the semantically equivalent ORD#LessThanLimit, because this
          // allows us to write a good trigger for a targeted monotonicity axiom.  That axiom, in turn, makes the
          // automatic verification more powerful for least lemmas that have more than one focal-predicate term.
          var smaller = new BinaryExpr(kprime.tok, BinaryExpr.Opcode.Lt, kprime, k) {
            ResolvedOp = BinaryExpr.ResolvedOpcode.LessThanLimit,
            Type = Type.Bool
          };
          limitCalls = new ExistsExpr(pp.tok, new List<BoundVar> { kprimeVar }, smaller, ppCall, triggerAttr);
          limitCalls.Type = Type.Bool;  // resolve here
        }
        var a = Expression.CreateImplies(kIsPositive, body);
        var b = Expression.CreateImplies(kIsLimit, limitCalls);
        return Expression.CreateAnd(a, b);
      } else {
        // 0 < k
        var kIsPositive = Expression.CreateLess(Expression.CreateIntLiteral(pp.tok, 0), k);
        if (pp.ExtremePred is GreatestPredicate) {
          // add antecedent "0 < _k ==>"
          return Expression.CreateImplies(kIsPositive, body);
        } else {
          // add initial conjunct "0 < _k &&"
          return Expression.CreateAnd(kIsPositive, body);
        }
      }
    }

    public static void RecursiveCallParameters(IToken tok, MemberDecl member, List<TypeParameter> typeParams, List<Formal> ins,
      Dictionary<IVariable, Expression> substMap,
      out Expression receiver, out List<Expression> arguments) {
      Contract.Requires(tok != null);
      Contract.Requires(member != null);
      Contract.Requires(member.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(typeParams != null);
      Contract.Requires(ins != null);
      Contract.Requires(substMap != null);
      Contract.Ensures(Contract.ValueAtReturn(out receiver) != null);
      Contract.Ensures(Contract.ValueAtReturn(out arguments) != null);

      if (member.IsStatic) {
        receiver = new StaticReceiverExpr(tok, (TopLevelDeclWithMembers)member.EnclosingClass, true);  // this also resolves it
      } else {
        receiver = new ImplicitThisExpr(tok);
        receiver.Type = Resolver.GetReceiverType(tok, member);  // resolve here
      }

      arguments = new List<Expression>();
      foreach (var inFormal in ins) {
        Expression inE;
        if (substMap.TryGetValue(inFormal, out inE)) {
          arguments.Add(inE);
        } else {
          var ie = new IdentifierExpr(inFormal.tok, inFormal.Name);
          ie.Var = inFormal;  // resolve here
          ie.Type = inFormal.Type;  // resolve here
          arguments.Add(ie);
        }
      }
    }

    void AddLayerSynonymAxiom(Function f, bool forHandle = false) {
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

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args1.Add(s);
        args0.Add(s);
      }
      if (!forHandle && (AlwaysUseHeap || f.ReadsHeap)) {
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
      sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, ax, "layer synonym axiom"));
    }

    void AddFuelSynonymAxiom(Function f) {
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
      args0.Add(new Bpl.IdentifierExpr(f.tok, "$LZ",predef.LayerType)); // $LZ

      if (f is TwoStateFunction) {
        bv = new Bpl.BoundVariable(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType));
        formals.Add(bv);
        s = new Bpl.IdentifierExpr(f.tok, bv);
        args2.Add(s);
        args1.Add(s);
        args0.Add(s);
      }
      if (AlwaysUseHeap || f.ReadsHeap) {
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
      sink.AddTopLevelDeclaration(new Bpl.Axiom(f.tok, ax, "fuel synonym axiom"));
    }

    /// <summary>
    /// In the following,
    /// if "pp" is a greatest predicate, then QQQ and NNN and HHH and EEE stand for "forall" and "" and "==>" and REVERSE-IMPLIES, and
    /// if "pp" is a least predicate, then QQQ and NNN and HHH and EEE stand for "exists" and "!" and "&&" and "==>".
    /// ==========  For co-predicates:
    /// Add the axioms:
    ///   forall args :: P(args) ==> QQQ k: nat :: P#[k](args)
    ///   forall args :: (QQQ k: nat :: P#[k](args)) ==> P(args)
    ///   forall args,k :: k == 0 ==> NNN P#[k](args)
    /// where "args" is "heap, formals".  In more details:
    ///   AXIOM_ACTIVATION ==> forall args :: { P(args) } args-have-appropriate-values && P(args) ==> QQQ k { P#[k](args) } :: 0 ATMOST k HHH P#[k](args)
    ///   AXIOM_ACTIVATION ==> forall args :: { P(args) } args-have-appropriate-values && (QQQ k :: 0 ATMOST k HHH P#[k](args)) ==> P(args)
    ///   AXIOM_ACTIVATION ==> forall args,k :: args-have-appropriate-values && k == 0 ==> NNN P#0#[k](args)
    ///   AXIOM_ACTIVATION ==> forall args,k,m :: args-have-appropriate-values && 0 ATMOST k LESS m ==> (P#[k](args) EEE P#[m](args))  (*)
    /// where
    /// AXIOM_ACTIVATION
    /// means:
    ///   mh LESS ModuleContextHeight ||
    ///   (mh == ModuleContextHeight && fh ATMOST FunctionContextHeight)
    /// There is also a specialized version of (*) for least predicates.
    /// </summary>
    void AddPrefixPredicateAxioms(PrefixPredicate pp) {
      Contract.Requires(pp != null);
      Contract.Requires(predef != null);
      var co = pp.ExtremePred;
      var tok = pp.tok;
      var etran = new ExpressionTranslator(this, predef, tok);

      List<Bpl.Expr> tyexprs;
      var tyvars = MkTyParamBinders(GetTypeParams(pp), out tyexprs);

      var bvs = new List<Variable>(tyvars);
      var coArgs = new List<Bpl.Expr>(tyexprs);
      var prefixArgs = new List<Bpl.Expr>(tyexprs);
      var prefixArgsLimited = new List<Bpl.Expr>(tyexprs);
      var prefixArgsLimitedM = new List<Bpl.Expr>(tyexprs);
      if (pp.IsFuelAware()) {
        var sV = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "$ly", predef.LayerType));
        var s = new Bpl.IdentifierExpr(tok, sV);
        var succS = FunctionCall(tok, BuiltinFunction.LayerSucc, null, s);
        bvs.Add(sV);
        coArgs.Add(succS);
        prefixArgs.Add(succS);
        prefixArgsLimited.Add(s);
        prefixArgsLimitedM.Add(s);
      }
      Bpl.Expr h;
      if (AlwaysUseHeap || pp.ReadsHeap) {
        var heapIdent = new Bpl.TypedIdent(tok, predef.HeapVarName, predef.HeapType);
        var bv = new Bpl.BoundVariable(tok, heapIdent);
        h = new Bpl.IdentifierExpr(tok, bv);
        bvs.Add(bv);
        coArgs.Add(h);
        prefixArgs.Add(h);
        prefixArgsLimited.Add(h);
        prefixArgsLimitedM.Add(h);
      } else {
        h = null;
      }
      // ante:  $IsGoodHeap($Heap) && this != null && formals-have-the-expected-types &&
      Bpl.Expr ante = h != null ? FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, etran.HeapExpr) : (Bpl.Expr)Bpl.Expr.True;

      if (!pp.IsStatic) {
        var bvThis = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, etran.This, TrReceiverType(pp)));
        bvs.Add(bvThis);
        var bvThisIdExpr = new Bpl.IdentifierExpr(tok, bvThis);
        coArgs.Add(bvThisIdExpr);
        prefixArgs.Add(bvThisIdExpr);
        prefixArgsLimited.Add(bvThisIdExpr);
        prefixArgsLimitedM.Add(bvThisIdExpr);
        // add well-typedness conjunct to antecedent
        Type thisType = Resolver.GetReceiverType(tok, pp);
        Bpl.Expr wh = Bpl.Expr.And(
          ReceiverNotNull(bvThisIdExpr),
          GetWhereClause(tok, bvThisIdExpr, thisType, etran, NOALLOC));
        ante = Bpl.Expr.And(ante, wh);
      }

      Bpl.Expr kWhere = null, kId = null, mId = null;
      Bpl.Variable k = null;
      Bpl.Variable m = null;

      // DR: Changed to add the pp formals instead of co (since types would otherwise be wrong)
      //     Note that k is not added to bvs or coArgs.
      foreach (var p in pp.Formals) {
        bool is_k = p == pp.Formals[0];
        var bv = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(pp.IdGenerator), TrType(p.Type)));
        var formal = new Bpl.IdentifierExpr(p.tok, bv);
        if (!is_k) {
          coArgs.Add(formal);
        }
        prefixArgs.Add(formal);
        prefixArgsLimited.Add(formal);
        if (is_k) {
          m = new Bpl.BoundVariable(p.tok, new Bpl.TypedIdent(p.tok, "_m", TrType(p.Type)));
          mId = new Bpl.IdentifierExpr(m.tok, m);
          prefixArgsLimitedM.Add(mId);
        } else {
          prefixArgsLimitedM.Add(formal);
        }
        var wh = GetWhereClause(p.tok, formal, p.Type, etran, NOALLOC);
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
      Contract.Assert(k != null && m != null);  // the loop should have filled these in

      var funcID = new Bpl.IdentifierExpr(tok, co.FullSanitizedName, TrType(co.ResultType));
      var coAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), coArgs);
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixAppl = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgs);

      var activation = AxiomActivation(pp, etran);

      // forall args :: { P(args) } args-have-appropriate-values && P(args) ==> QQQ k { P#[k](args) } :: 0 ATMOST k HHH P#[k](args)
      var tr = BplTrigger(prefixAppl);
      var qqqK = pp.ExtremePred is GreatestPredicate ?
        (Bpl.Expr)new Bpl.ForallExpr(tok, new List<Variable> { k }, tr, kWhere == null ? prefixAppl : BplImp(kWhere, prefixAppl)) :
        (Bpl.Expr)new Bpl.ExistsExpr(tok, new List<Variable> { k }, tr, kWhere == null ? prefixAppl : BplAnd(kWhere, prefixAppl));
      tr = BplTriggerHeap(this, tok, coAppl, AlwaysUseHeap || pp.ReadsHeap ? null : h);
      var allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, coAppl), qqqK));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, allS),
        "1st prefix predicate axiom for " + pp.FullSanitizedName));

      // forall args :: { P(args) } args-have-appropriate-values && (QQQ k :: 0 ATMOST k HHH P#[k](args)) ==> P(args)
      allS = new Bpl.ForallExpr(tok, bvs, tr, BplImp(BplAnd(ante, qqqK), coAppl));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, allS),
        "2nd prefix predicate axiom"));

      // forall args,k :: args-have-appropriate-values && k == 0 ==> NNN P#0#[k](args)
      var moreBvs = new List<Variable>();
      moreBvs.AddRange(bvs);
      moreBvs.Add(k);
      var z = Bpl.Expr.Eq(kId, pp.Formals[0].Type.IsBigOrdinalType ?
        (Bpl.Expr)FunctionCall(tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(0)) :
        Bpl.Expr.Literal(0));
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      Bpl.Expr prefixLimitedBody = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
      Bpl.Expr prefixLimited = pp.ExtremePred is LeastPredicate ? Bpl.Expr.Not(prefixLimitedBody) : prefixLimitedBody;

      var trigger = BplTriggerHeap(this, prefixLimitedBody.tok, prefixLimitedBody, AlwaysUseHeap || pp.ReadsHeap ? null : h);
      var trueAtZero = new Bpl.ForallExpr(tok, moreBvs, trigger, BplImp(BplAnd(ante, z), prefixLimited));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, trueAtZero),
        "3rd prefix predicate axiom"));

#if WILLING_TO_TAKE_THE_PERFORMANCE_HIT
      // forall args,k,m :: args-have-appropriate-values && 0 <= k <= m ==> (P#[k](args) EEE P#[m](args))
      moreBvs = new List<Variable>();
      moreBvs.AddRange(bvs);
      moreBvs.Add(k);
      moreBvs.Add(m);
      Bpl.Expr smaller;
      if (kId.Type.IsInt) {
        smaller = BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), kId), Bpl.Expr.Lt(kId, mId));
      } else {
        smaller = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, kId, mId);
      }
      funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
      var prefixPred_K = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
      var prefixPred_M = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimitedM);
      var direction = pp.ExtremePred is LeastPredicate ? BplImp(prefixPred_K, prefixPred_M) : BplImp(prefixPred_M, prefixPred_K);

      var trigger2 = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { prefixPred_K, prefixPred_M });
      var monotonicity = new Bpl.ForallExpr(tok, moreBvs, trigger2, BplImp(smaller, direction));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, monotonicity),
        "prefix predicate monotonicity axiom"));
#endif
      // A more targeted monotonicity axiom used to increase the power of automation for proving the limit case for
      // least predicates that have more than one focal-predicate term.
      if (pp.ExtremePred is LeastPredicate && pp.Formals[0].Type.IsBigOrdinalType) {
        // forall args,k,m,limit ::
        //   { P#[k](args), ORD#LessThanLimit(k,limit), ORD#LessThanLimit(m,limit) }
        //   args-have-appropriate-values && k < m && P#[k](args) ==> P#[m](args))
        var limit = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, "_limit", TrType(Type.BigOrdinal)));
        var limitId = new Bpl.IdentifierExpr(limit.tok, limit);
        moreBvs = new List<Variable>();
        moreBvs.AddRange(bvs);
        moreBvs.Add(k);
        moreBvs.Add(m);
        moreBvs.Add(limit);
        var kLessLimit = FunctionCall(tok, "ORD#LessThanLimit", Bpl.Type.Bool, kId, limitId);
        var mLessLimit = FunctionCall(tok, "ORD#LessThanLimit", Bpl.Type.Bool, mId, limitId);
        var kLessM = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, kId, mId);
        funcID = new Bpl.IdentifierExpr(tok, pp.FullSanitizedName, TrType(pp.ResultType));
        var prefixPred_K = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimited);
        var prefixPred_M = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(funcID), prefixArgsLimitedM);
        var direction = BplImp(prefixPred_K, prefixPred_M);

        var trigger3 = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { prefixPred_K, kLessLimit, mLessLimit });
        var monotonicity = new Bpl.ForallExpr(tok, moreBvs, trigger3, BplImp(kLessM, direction));
        sink.AddTopLevelDeclaration(new Bpl.Axiom(tok, Bpl.Expr.Imp(activation, monotonicity),
          "targeted prefix predicate monotonicity axiom"));
      }
    }

    /// <summary>
    /// For a non-static field "f" in a class "c(G)", generate:
    ///     // type axiom:
    ///     // If "G" is empty, then TClassA(G) is omitted from trigger.
    ///     // If "c" is an array declaration, then the bound variables also include the index variables "ii" and "h[o, f]" has the form "h[o, Index(ii)]".
    ///     // If "f" is readonly, then "h[o, f]" has the form "f(o)" (for special fields) or "f(G,o)" (for programmer-declared const fields),
    ///     // so "h" and $IsHeap(h) are omitted.
    ///     axiom fh < FunctionContextHeight ==>
    ///       (forall o: ref, h: Heap, G : Ty ::
    ///         { h[o, f], TClassA(G) }  // if "f" is a const, omit TClassA(G) from the trigger and just use { f(G,o) }
    ///         $IsHeap(h) &&
    ///         o != null && $Is(o, TClassA(G))  // or dtype(o) = TClassA(G)
    ///         ==>
    ///         $Is(h[o, f], TT(PP)));
    ///
    ///     // allocation axiom:
    ///     // As above for "G" and "ii", but "h" is included no matter what.
    ///     axiom fh < FunctionContextHeight ==>
    ///       (forall o: ref, h: Heap, G : Ty ::
    ///         { h[o, f], TClassA(G) }  // if "f" is a const, use the trigger { f(G,o), h[o, alloc] }; for other readonly fields, use { f(o), h[o, alloc], TClassA(G) }
    ///         $IsHeap(h) &&
    ///         o != null && $Is(o, TClassA(G)) &&  // or dtype(o) = TClassA(G)
    ///         h[o, alloc]
    ///         ==>
    ///         $IsAlloc(h[o, f], TT(PP), h));
    ///
    /// For a static (necessarily "const") field "f" in a class "c(G)", the expression corresponding to "h[o, f]" or "f(G,o)" above is "f(G)",
    /// so generate:
    ///     // type axiom:
    ///     axiom fh < FunctionContextHeight ==>
    ///       (forall G : Ty ::
    ///         { f(G) }
    ///         $Is(f(G), TT(PP)));
    ///     // Or in the case where G is empty:
    ///     axiom $Is(f(G), TT);
    ///
    ///     // allocation axiom:
    ///     axiom fh < FunctionContextHeight ==>
    ///       (forall h: Heap, G : Ty ::
    ///         { $IsAlloc(f(G), TT(PP), h) }
    ///         $IsHeap(h)
    ///       ==>
    ///         $IsAlloc(f(G), TT(PP), h));
    ///
    ///
    /// The axioms above could be optimised to something along the lines of:
    ///     axiom fh < FunctionContextHeight ==>
    ///       (forall o: ref, h: Heap ::
    ///         { h[o, f] }
    ///         $IsHeap(h) && o != null && Tag(dtype(o)) = TagClass
    ///         ==>
    ///         (h[o, alloc] ==> $IsAlloc(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h)) &&
    ///         $Is(h[o, f], TT(TClassA_Inv_i(dtype(o)),..), h);
    /// <summary>
    void AddAllocationAxiom(Field f, TopLevelDeclWithMembers c, bool is_array = false) {
      Contract.Requires(c != null);
      // IFF you're adding the array axioms, then the field should be null
      Contract.Requires(is_array == (f == null));
      Contract.Requires(sink != null && predef != null);

      Bpl.Expr heightAntecedent = Bpl.Expr.True;
      if (f is ConstantField) {
        var cf = (ConstantField)f;
        AddWellformednessCheck(cf);
        if (InVerificationScope(cf)) {
          var etran = new ExpressionTranslator(this, predef, f.tok);
          heightAntecedent = Bpl.Expr.Lt(Bpl.Expr.Literal(cf.EnclosingModule.CallGraph.GetSCCRepresentativeId(cf)), etran.FunctionContextHeight());
        }
      }

      var bvsTypeAxiom = new List<Bpl.Variable>();
      var bvsAllocationAxiom = new List<Bpl.Variable>();

      // G
      List<Bpl.Expr> tyexprs;
      var tyvars = MkTyParamBinders(GetTypeParams(c), out tyexprs);
      bvsTypeAxiom.AddRange(tyvars);
      bvsAllocationAxiom.AddRange(tyvars);

      if (f is ConstantField && f.IsStatic) {
        var oDotF = new Bpl.NAryExpr(c.tok, new Bpl.FunctionCall(GetReadonlyField(f)), tyexprs);
        var is_hf = MkIs(oDotF, f.Type);              // $Is(h[o, f], ..)
        Bpl.Expr ax = bvsTypeAxiom.Count == 0 ? is_hf : BplForall(bvsTypeAxiom, BplTrigger(oDotF), is_hf);
        sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, BplImp(heightAntecedent, ax), string.Format("{0}.{1}: Type axiom", c, f)));

        if (CommonHeapUse || (NonGhostsUseHeap && !f.IsGhost)) {
          Bpl.Expr h;
          var hVar = BplBoundVar("$h", predef.HeapType, out h);
          bvsAllocationAxiom.Add(hVar);
          var isGoodHeap = FunctionCall(c.tok, BuiltinFunction.IsGoodHeap, null, h);
          var isalloc_hf = MkIsAlloc(oDotF, f.Type, h); // $IsAlloc(h[o, f], ..)
          ax = BplForall(bvsAllocationAxiom, BplTrigger(isalloc_hf), BplImp(isGoodHeap, isalloc_hf));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, BplImp(heightAntecedent, ax), string.Format("{0}.{1}: Allocation axiom", c, f)));
        }

      } else {
        // This is the typical case (that is, f is not a static const field)

        // h, o
        Bpl.Expr h, o;
        var hVar = BplBoundVar("$h", predef.HeapType, out h);
        var oVar = BplBoundVar("$o", TrType(Resolver.GetThisType(c.tok, c)), out o);

        // TClassA(G)
        Bpl.Expr o_ty = ClassTyCon(c, tyexprs);

        var isGoodHeap = FunctionCall(c.tok, BuiltinFunction.IsGoodHeap, null, h);
        Bpl.Expr isalloc_o;
        if (!(c is ClassDecl)) {
          var udt = UserDefinedType.FromTopLevelDecl(c.tok, c);
          isalloc_o = MkIsAlloc(o, udt, h);
        } else if (RevealedInScope(c)) {
          isalloc_o = IsAlloced(c.tok, h, o);
        } else {
          // c is only provided, not revealed, in the scope. Use the non-null type decl's internal synonym
          var cl = (ClassDecl)c;
          Contract.Assert(cl.NonNullTypeDecl != null);
          var udt = UserDefinedType.FromTopLevelDecl(c.tok, cl.NonNullTypeDecl);
          isalloc_o = MkIsAlloc(o, udt, h);
        }

        Bpl.Expr indexBounds = Bpl.Expr.True;
        Bpl.Expr oDotF;
        if (is_array) {
          // generate h[o,Index(ii)]
          bvsTypeAxiom.Add(hVar); bvsTypeAxiom.Add(oVar);
          bvsAllocationAxiom.Add(hVar); bvsAllocationAxiom.Add(oVar);

          var ac = (ArrayClassDecl)c;
          var ixs = new List<Bpl.Expr>();
          for (int i = 0; i < ac.Dims; i++) {
            Bpl.Expr e; Bpl.Variable v = BplBoundVar("$i" + i, Bpl.Type.Int, out e);
            ixs.Add(e);
            bvsTypeAxiom.Add(v);
            bvsAllocationAxiom.Add(v);
          }

          oDotF = ReadHeap(c.tok, h, o, GetArrayIndexFieldName(c.tok, ixs));

          for (int i = 0; i < ac.Dims; i++) {
            // 0 <= i && i < _System.array.Length(o)
            var e1 = Bpl.Expr.Le(Bpl.Expr.Literal(0), ixs[i]);
            var ff = GetReadonlyField((Field)(ac.Members[i]));
            var e2 = Bpl.Expr.Lt(ixs[i], new Bpl.NAryExpr(c.tok, new Bpl.FunctionCall(ff), new List<Bpl.Expr> { o }));
            indexBounds = BplAnd(indexBounds, BplAnd(e1, e2));
          }
        } else if (f.IsMutable) {
          // generate h[o,f]
          oDotF = ReadHeap(c.tok, h, o, new Bpl.IdentifierExpr(c.tok, GetField(f)));
          bvsTypeAxiom.Add(hVar); bvsTypeAxiom.Add(oVar);
          bvsAllocationAxiom.Add(hVar); bvsAllocationAxiom.Add(oVar);
        } else {
          // generate f(G,o)
          var args = new List<Bpl.Expr> { o };
          if (f is ConstantField) {
            args = Concat(tyexprs, args);
          }
          oDotF = new Bpl.NAryExpr(c.tok, new Bpl.FunctionCall(GetReadonlyField(f)), args);
          bvsTypeAxiom.Add(oVar);
          bvsAllocationAxiom.Add(hVar); bvsAllocationAxiom.Add(oVar);
        }

        // antecedent: some subset of: $IsHeap(h) && o != null && $Is(o, TClassA(G)) && indexBounds
        Bpl.Expr ante = Bpl.Expr.True;
        if (is_array || f.IsMutable) {
          ante = BplAnd(ante, isGoodHeap);
          // Note: for the allocation axiom, isGoodHeap is added back in for !f.IsMutable below
        }
        if (!(f is ConstantField)) {
          Bpl.Expr is_o = BplAnd(
            ReceiverNotNull(o),
            c is TraitDecl ? MkIs(o, o_ty) : DType(o, o_ty));  // $Is(o, ..)  or  dtype(o) == o_ty
          ante = BplAnd(ante, is_o);
        }
        ante = BplAnd(ante, indexBounds);

        // trigger
        var t_es = new List<Bpl.Expr>();
        t_es.Add(oDotF);
        if (tyvars.Count > 0 && (is_array || !(f is ConstantField))) {
          t_es.Add(o_ty);
        }
        var tr = new Bpl.Trigger(c.tok, true, t_es);

        // Now for the conclusion of the axioms
        Bpl.Expr is_hf, isalloc_hf = null;
        if (is_array) {
          is_hf = MkIs(oDotF, tyexprs[0], true);
          if (CommonHeapUse || NonGhostsUseHeap) {
            isalloc_hf = MkIsAlloc(oDotF, tyexprs[0], h, true);
          }
        } else {
          is_hf = MkIs(oDotF, f.Type);              // $Is(h[o, f], ..)
          if (CommonHeapUse || (NonGhostsUseHeap && !f.IsGhost)) {
            isalloc_hf = MkIsAlloc(oDotF, f.Type, h); // $IsAlloc(h[o, f], ..)
          }
        }

        Bpl.Expr ax = BplForall(bvsTypeAxiom, tr, BplImp(ante, is_hf));
        sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, BplImp(heightAntecedent, ax), string.Format("{0}.{1}: Type axiom", c, f)));

        if (isalloc_hf != null) {
          if (!is_array && !f.IsMutable) {
            // isGoodHeap wasn't added above, so add it now
            ante = BplAnd(isGoodHeap, ante);
          }
          ante = BplAnd(ante, isalloc_o);

          // compute a different trigger
          t_es = new List<Bpl.Expr>();
          t_es.Add(oDotF);
          if (!is_array && !f.IsMutable) {
            // since "h" is not part of oDotF, we add a separate term that mentions "h"
            t_es.Add(isalloc_o);
          }
          if (!(f is ConstantField) && tyvars.Count > 0) {
            t_es.Add(o_ty);
          }
          tr = new Bpl.Trigger(c.tok, true, t_es);

          ax = BplForall(bvsAllocationAxiom, tr, BplImp(ante, isalloc_hf));
          sink.AddTopLevelDeclaration(new Bpl.Axiom(c.tok, BplImp(heightAntecedent, ax), string.Format("{0}.{1}: Allocation axiom", c, f)));
        }
      }
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
    ICallable codeContext = null;  // the method/iterator whose implementation is currently being translated or the function whose specification is being checked for well-formedness
    Bpl.LocalVariable yieldCountVariable = null;  // non-null when an iterator body is being translated
    bool inBodyInitContext = false;  // true during the translation of the .BodyInit portion of a divided constructor body
    readonly Dictionary<string, Bpl.IdentifierExpr> definiteAssignmentTrackers = new Dictionary<string,Bpl.IdentifierExpr>();
    bool assertAsAssume = false; // generate assume statements instead of assert statements
    public enum StmtType { NONE, ASSERT, ASSUME };
    public StmtType stmtContext = StmtType.NONE;  // the Statement that is currently being translated
    public bool adjustFuelForExists = true;  // fuel need to be adjusted for exists based on whether exists is in assert or assume stmt.

    public readonly FreshIdGenerator defaultIdGenerator = new FreshIdGenerator();

    public FreshIdGenerator CurrentIdGenerator
    {
      get
      {
        var decl = codeContext as Declaration;
        if (decl != null)
        {
          return decl.IdGenerator;
        }
        return defaultIdGenerator;
      }
    }

    Dictionary<string, Bpl.IdentifierExpr> _tmpIEs = new Dictionary<string, Bpl.IdentifierExpr>();

    int assertionCount = 0;

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

    void AddMethodImpl(Method m, Bpl.Procedure proc, bool wellformednessProc)
    {
      Contract.Requires(m != null);
      Contract.Requires(proc != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);
      Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext == null);

      currentModule = m.EnclosingClass.EnclosingModuleDefinition;
      codeContext = m;
      isAllocContext = new IsAllocContext(m.IsGhost);

      List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
      List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

      BoogieStmtListBuilder builder = new BoogieStmtListBuilder(this);
      builder.Add(new CommentCmd("AddMethodImpl: " + m + ", " + proc));
      var etran = new ExpressionTranslator(this, predef, m.tok);
      InitializeFuelConstant(m.tok, builder, etran);
      var localVariables = new List<Variable>();
      GenerateImplPrelude(m, wellformednessProc, inParams, outParams, builder, localVariables);

      if (UseOptimizationInZ3)
      {
        // We ask Z3 to minimize all parameters of type 'nat'.
        foreach (var f in m.Ins)
        {
          var udt = f.Type.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt != null && udt.Name == "nat")
          {
            builder.Add(optimizeExpr(true, new IdentifierExpr(f.tok, f), f.Tok, etran));
          }
        }
      }

      Bpl.StmtList stmts;
      if (!wellformednessProc) {
        var inductionVars = ApplyInduction(m.Ins, m.Attributes);
        if (inductionVars.Count != 0) {
          // Let the parameters be this,x,y of the method M and suppose ApplyInduction returns y.
          // Also, let Pre be the precondition and VF be the decreases clause.
          // Then, insert into the method body what amounts to:
          //     assume case-analysis-on-parameter[[ y' ]];
          //     forall (y' | Pre(this, x, y') && VF(this, x, y') << VF(this, x, y)) {
          //       this.M(x, y');
          //     }
          // Generate bound variables for the forall statement, and a substitution for the Pre and VF

          // assume case-analysis-on-parameter[[ y' ]];
          foreach (var inFormal in m.Ins) {
            var dt = inFormal.Type.AsDatatype;
            if (dt != null) {
              var funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(inFormal.tok, "$IsA#" + dt.FullSanitizedName, Bpl.Type.Bool));
              var f = new Bpl.IdentifierExpr(inFormal.tok, inFormal.AssignUniqueName(m.IdGenerator), TrType(inFormal.Type));
              builder.Add(TrAssumeCmd(inFormal.tok, new Bpl.NAryExpr(inFormal.tok, funcID, new List<Bpl.Expr> { f })));
            }
          }

          var parBoundVars = new List<BoundVar>();
          var parBounds = new List<ComprehensionExpr.BoundedPool>();
          var substMap = new Dictionary<IVariable, Expression>();
          Expression receiverSubst = null;
          foreach (var iv in inductionVars) {
            BoundVar bv;
            if (iv == null) {
              // this corresponds to "this"
              Contract.Assert(!m.IsStatic);  // if "m" is static, "this" should never have gone into the _induction attribute
              Contract.Assert(receiverSubst == null);  // we expect at most one
              var receiverType = Resolver.GetThisType(m.tok, (TopLevelDeclWithMembers)m.EnclosingClass);
              bv = new BoundVar(m.tok, CurrentIdGenerator.FreshId("$ih#this"), receiverType); // use this temporary variable counter, but for a Dafny name (the idea being that the number and the initial "_" in the name might avoid name conflicts)
              var ie = new IdentifierExpr(m.tok, bv.Name);
              ie.Var = bv;  // resolve here
              ie.Type = bv.Type;  // resolve here
              receiverSubst = ie;
            } else {
              IdentifierExpr ie;
              CloneVariableAsBoundVar(iv.tok, iv, "$ih#" + iv.Name, out bv, out ie);
              substMap.Add(iv, ie);
            }
            parBoundVars.Add(bv);
            parBounds.Add(new ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool());  // record that we don't want alloc antecedents for these variables
          }

          // Generate a CallStmt for the recursive call
          Expression recursiveCallReceiver;
          List<Expression> recursiveCallArgs;
          RecursiveCallParameters(m.tok, m, m.TypeArgs, m.Ins, substMap, out recursiveCallReceiver, out recursiveCallArgs);
          var methodSel = new MemberSelectExpr(m.tok, recursiveCallReceiver, m.Name);
          methodSel.Member = m;  // resolve here
          methodSel.TypeApplication_AtEnclosingClass = m.EnclosingClass.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.tok, tp));
          methodSel.TypeApplication_JustMember = m.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp.tok, tp));
          methodSel.Type = new InferredTypeProxy();
          var recursiveCall = new CallStmt(m.tok, m.tok, new List<Expression>(), methodSel, recursiveCallArgs);
          recursiveCall.IsGhost = m.IsGhost;  // resolve here

          Expression parRange = new LiteralExpr(m.tok, true);
          parRange.Type = Type.Bool;  // resolve here
          foreach (var pre in m.Req) {
            parRange = Expression.CreateAnd(parRange, Substitute(pre.E, receiverSubst, substMap));
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
              Expression es = Substitute(ee, receiverSubst, substMap);
              es = Substitute(es, null, decrSubstMap);
              decrCallee.Add(exprTran.TrExpr(es));
            }
            return DecreasesCheck(decrToks, decrTypes, decrTypes, decrCallee, decrCaller, null, null, false, true);
          };

#if VERIFY_CORRECTNESS_OF_TRANSLATION_FORALL_STATEMENT_RANGE
          var definedness = new BoogieStmtListBuilder(this);
          var exporter = new BoogieStmtListBuilder(this);
          TrForallStmtCall(m.tok, parBoundVars, parRange, decrCheck, null, recursiveCall, definedness, exporter, localVariables, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(m.tok, null, definedness.Collect(m.tok), null, exporter.Collect(m.tok)));
#else
          TrForallStmtCall(m.tok, parBoundVars, parBounds, parRange, decrCheck, null, recursiveCall, null, builder, localVariables, etran);
#endif
        }
        // translate the body of the method
        Contract.Assert(m.Body != null);  // follows from method precondition and the if guard

        // $_reverifyPost := false;
        builder.Add(Bpl.Cmd.SimpleAssign(m.tok, new Bpl.IdentifierExpr(m.tok, "$_reverifyPost", Bpl.Type.Bool), Bpl.Expr.False));
        // register output parameters with definite-assignment trackers
        Contract.Assert(definiteAssignmentTrackers.Count == 0);
        m.Outs.Iter(p => AddExistingDefiniteAssignmentTracker(p, m.IsGhost));
        // translate the body
        TrStmt(m.Body, builder, localVariables, etran);
        m.Outs.Iter(p => CheckDefiniteAssignmentReturn(m.BodyEndTok, p, builder));
        stmts = builder.Collect(m.Body.Tok);
        // tear down definite-assignment trackers
        m.Outs.Iter(RemoveDefiniteAssignmentTracker);
        Contract.Assert(definiteAssignmentTrackers.Count == 0);
      } else {
        // check well-formedness of any default-value expressions (before assuming preconditions)
        foreach (var formal in m.Ins.Where(formal => formal.DefaultValue != null)) {
          var e = formal.DefaultValue;
          CheckWellformed(e, new WFOptions(null, false, false, true), localVariables, builder, etran);
          builder.Add(new Bpl.AssumeCmd(e.tok, CanCallAssumption(e, etran)));
          CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, builder);

          if (formal.IsOld) {
            Bpl.Expr wh = GetWhereClause(e.tok, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
            if (wh != null) {
              builder.Add(Assert(e.tok, wh, "default value must be allocated in the two-state lemma's previous state"));
            }
          }
        }
        // check well-formedness of the preconditions, and then assume each one of them
        foreach (AttributedExpression p in m.Req) {
          CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, builder, etran);
        }
        // check well-formedness of the modifies clauses
        CheckFrameWellFormed(new WFOptions(), m.Mod.Expressions, localVariables, builder, etran);
        // check well-formedness of the decreases clauses
        foreach (Expression p in m.Decreases.Expressions)
        {
          CheckWellformed(p, new WFOptions(), localVariables, builder, etran);
        }

        if (!(m is TwoStateLemma)) {
          // play havoc with the heap according to the modifies clause
          builder.Add(new Bpl.HavocCmd(m.tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
          // assume the usual two-state boilerplate information
          foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, etran.Old, etran, etran.Old)) {
            if (tri.IsFree) {
              builder.Add(TrAssumeCmd(m.tok, tri.Expr));
            }
          }
        }

        // also play havoc with the out parameters
        if (outParams.Count != 0) {  // don't create an empty havoc statement
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
        foreach (AttributedExpression p in m.Ens) {
          CheckWellformedAndAssume(p.E, new WFOptions(), localVariables, builder, etran);
        }

        stmts = builder.Collect(m.tok);
      }

      if (EmitImplementation(m.Attributes)) {
        // emit impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(m.Attributes, null);
        Bpl.Implementation impl = new Bpl.Implementation(m.tok, proc.Name,
          new List<Bpl.TypeVariable>(), inParams, outParams,
          localVariables, stmts, kv);
        sink.AddTopLevelDeclaration(impl);

        if (InsertChecksums) {
          InsertChecksum(m, impl);
        }
      }

      isAllocContext = null;
      Reset();
    }

#region Definite-assignment tracking

    bool NeedsDefiniteAssignmentTracker(bool isGhost, Type type) {
      Contract.Requires(type != null);

      if (DafnyOptions.O.DefiniteAssignmentLevel == 0) {
        return false;
      } else if (DafnyOptions.O.DefiniteAssignmentLevel == 1) {
        if (isGhost && type.IsNonempty) {
          return false;
        } else if (!isGhost && type.HasCompilableValue) {
          return false;
        }
      }
      return true;
    }

    Bpl.Expr/*?*/ AddDefiniteAssignmentTracker(IVariable p, List<Bpl.Variable> localVariables, bool isOutParam = false, bool forceGhostVar = false) {
      Contract.Requires(p != null);
      Contract.Requires(localVariables != null);

      if (!NeedsDefiniteAssignmentTracker(p.IsGhost || forceGhostVar, p.Type)) {
        return null;
      }
      Bpl.Variable tracker;
      if (isOutParam) {
        tracker = new Bpl.Formal(p.Tok, new Bpl.TypedIdent(p.Tok, "defass#" + p.UniqueName, Bpl.Type.Bool), false);
      } else {
        tracker = new Bpl.LocalVariable(p.Tok, new Bpl.TypedIdent(p.Tok, "defass#" + p.UniqueName, Bpl.Type.Bool));
      }
      localVariables.Add(tracker);
      var ie = new Bpl.IdentifierExpr(p.Tok, tracker);
      definiteAssignmentTrackers.Add(p.UniqueName, ie);
      return ie;
    }

    void AddExistingDefiniteAssignmentTracker(IVariable p, bool forceGhostVar) {
      Contract.Requires(p != null);

      if (NeedsDefiniteAssignmentTracker(p.IsGhost || forceGhostVar, p.Type)) {
        var ie = new Bpl.IdentifierExpr(p.Tok, "defass#" + p.UniqueName, Bpl.Type.Bool);
        definiteAssignmentTrackers.Add(p.UniqueName, ie);
      }
    }

    void AddDefiniteAssignmentTrackerSurrogate(Field field, TopLevelDeclWithMembers enclosingClass, List<Variable> localVariables) {
      Contract.Requires(field != null);
      Contract.Requires(localVariables != null);

      var type = Resolver.SubstType(field.Type, enclosingClass.ParentFormalTypeParametersToActuals);
      if (!NeedsDefiniteAssignmentTracker(field.IsGhost, type)) {
        return;
      }
      var nm = SurrogateName(field);
      var tracker = new Bpl.LocalVariable(field.tok, new Bpl.TypedIdent(field.tok, "defass#" + nm, Bpl.Type.Bool));
      localVariables.Add(tracker);
      var ie = new Bpl.IdentifierExpr(field.tok, tracker);
      definiteAssignmentTrackers.Add(nm, ie);
    }

    void RemoveDefiniteAssignmentTrackers(List<Statement> ss, int prevDefAssTrackerCount) {
      Contract.Requires(ss != null);
      foreach (var s in ss) {
        if (s is VarDeclStmt vdecl) {
          if (vdecl.Update is AssignOrReturnStmt ars) {
            foreach (var sx in ars.ResolvedStatements) {
              if (sx is VarDeclStmt vdecl2) {
                vdecl2.Locals.Iter(RemoveDefiniteAssignmentTracker);
              }
            }
          } else {
            vdecl.Locals.Iter(RemoveDefiniteAssignmentTracker);
          }
        } else if (s is AssignOrReturnStmt ars) {
          foreach (var sx in ars.ResolvedStatements) {
            if (sx is VarDeclStmt vdecl2) {
              vdecl2.Locals.Iter(RemoveDefiniteAssignmentTracker);
            }
          }
        }
      }
      Contract.Assert(prevDefAssTrackerCount == definiteAssignmentTrackers.Count);
    }

    void RemoveDefiniteAssignmentTracker(IVariable p) {
      Contract.Requires(p != null);
      definiteAssignmentTrackers.Remove(p.UniqueName);
    }

    void RemoveDefiniteAssignmentTrackerSurrogate(Field field) {
      Contract.Requires(field != null);
      definiteAssignmentTrackers.Remove(SurrogateName(field));
    }

    void MarkDefiniteAssignmentTracker(IdentifierExpr expr, BoogieStmtListBuilder builder) {
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);
      MarkDefiniteAssignmentTracker(expr.tok, expr.Var.UniqueName, builder);
    }

    void MarkDefiniteAssignmentTracker(IToken tok, string name, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(builder != null);

      Bpl.IdentifierExpr ie;
      if (definiteAssignmentTrackers.TryGetValue(name, out ie)) {
        builder.Add(Bpl.Cmd.SimpleAssign(tok, ie, Bpl.Expr.True));
      }
    }

    void CheckDefiniteAssignment(IdentifierExpr expr, BoogieStmtListBuilder builder) {
      Contract.Requires(expr != null);
      Contract.Requires(builder!= null);

      Bpl.IdentifierExpr ie;
      if (definiteAssignmentTrackers.TryGetValue(expr.Var.UniqueName, out ie)) {
        builder.Add(Assert(expr.tok, ie, string.Format("variable '{0}', which is subject to definite-assignment rules, might be used before it has been assigned", expr.Var.Name)));
      }
    }

    void CheckDefiniteAssignmentSurrogate(IToken tok, Field field, bool atNew, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(field != null);
      Contract.Requires(builder != null);

      var nm = SurrogateName(field);
      Bpl.IdentifierExpr ie;
      if (definiteAssignmentTrackers.TryGetValue(nm, out ie)) {
        var msg = string.Format("field '{0}', which is subject to definite-assignment rules, {1}", field.Name,
          atNew ? "might not have been defined at this point in the constructor body" : "might be used before it has been assigned");
        builder.Add(Assert(tok, ie, msg));
      }
    }

    void CheckDefiniteAssignmentReturn(IToken tok, Formal p, BoogieStmtListBuilder builder) {
      Contract.Requires(tok != null);
      Contract.Requires(p != null && !p.InParam);
      Contract.Requires(builder != null);

      Bpl.IdentifierExpr ie;
      if (definiteAssignmentTrackers.TryGetValue(p.UniqueName, out ie)) {
        builder.Add(Assert(tok, ie, string.Format("out-parameter '{0}', which is subject to definite-assignment rules, might not have been defined at this return point", p.Name)));
      }
    }
#endregion  // definite-assignment tracking

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
      FuelContext fuelContext  = new FuelContext();
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

    internal static AssumeCmd optimizeExpr(bool minimize, Expression expr, IToken tok, ExpressionTranslator etran)
    {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsIntegerType || expr.Type.IsRealType);
      Contract.Requires(tok != null && etran != null);

      var assumeCmd = new AssumeCmd(tok, Expr.True);
      assumeCmd.Attributes = new QKeyValue(expr.tok, (minimize ? "minimize" : "maximize"), new List<object> { etran.TrExpr(expr) }, null);
      return assumeCmd;
    }

    private void AddFunctionOverrideCheckImpl(Function f)
    {
        Contract.Requires(f != null);
        Contract.Requires(f.EnclosingClass is TopLevelDeclWithMembers);
        Contract.Requires(sink != null && predef != null);
        Contract.Requires(f.OverriddenFunction != null);
        Contract.Requires(f.Formals.Count == f.OverriddenFunction.Formals.Count);
        Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext != null);
        Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext != null);

#region first procedure, no impl yet
        //Function nf = new Function(f.tok, "OverrideCheck_" + f.Name, f.IsStatic, f.IsGhost, f.TypeArgs, f.OpenParen, f.Formals, f.ResultType, f.Req, f.Reads, f.Ens, f.Decreases, f.Body, f.Attributes, f.SignatureEllipsis);
        //AddFunction(f);
        currentModule = f.EnclosingClass.EnclosingModuleDefinition;
        codeContext = f;

        Bpl.Expr prevHeap = null;
        Bpl.Expr currHeap = null;
        var ordinaryEtran = new ExpressionTranslator(this, predef, f.tok);
        ExpressionTranslator etran;
        var inParams_Heap = new List<Bpl.Variable>();
        if (f is TwoStateFunction) {
          var prevHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "previous$Heap", predef.HeapType), true);
          inParams_Heap.Add(prevHeapVar);
          prevHeap = new Bpl.IdentifierExpr(f.tok, prevHeapVar);
          if (f.ReadsHeap) {
            var currHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "current$Heap", predef.HeapType), true);
            inParams_Heap.Add(currHeapVar);
            currHeap = new Bpl.IdentifierExpr(f.tok, currHeapVar);
          }
          etran = new ExpressionTranslator(this, predef, currHeap, prevHeap);
        } else {
          etran = ordinaryEtran;
        }

        // parameters of the procedure
        var typeInParams = MkTyParamFormals(GetTypeParams(f));
        var inParams = new List<Variable>();
        var outParams = new List<Bpl.Variable>();
        if (!f.IsStatic) {
          var th = new Bpl.IdentifierExpr(f.tok, "this", TrReceiverType(f));
          Bpl.Expr wh = Bpl.Expr.And(
            ReceiverNotNull(th),
            etran.GoodRef(f.tok, th, Resolver.GetReceiverType(f.tok, f)));
          Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f), wh), true);
          inParams.Add(thVar);
        }
        foreach (Formal p in f.Formals) {
          Bpl.Type varType = TrType(p.Type);
          Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType), p.Type, etran, NOALLOC);
          inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
        }

        Formal pOut = null;
        if (f.Result != null || f.OverriddenFunction.Result != null) {
          if (f.Result != null) {
            pOut = f.Result;
            Contract.Assert(!pOut.IsOld);
          } else {
            var pp = f.OverriddenFunction.Result;
            Contract.Assert(!pp.IsOld);
            pOut = new Formal(pp.tok, pp.Name, f.ResultType, false, pp.IsGhost, null);
          }
          var varType = TrType(pOut.Type);
          var wh = GetWhereClause(pOut.tok, new Bpl.IdentifierExpr(pOut.tok, pOut.AssignUniqueName(f.IdGenerator), varType), pOut.Type, etran, NOALLOC);
          outParams.Add(new Bpl.Formal(pOut.tok, new Bpl.TypedIdent(pOut.tok, pOut.AssignUniqueName(f.IdGenerator), varType, wh), true));
        }
        // the procedure itself
        var req = new List<Bpl.Requires>();
        // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
        req.Add(Requires(f.tok, true, etran.HeightContext(f.OverriddenFunction), null, null));
        if (f is TwoStateFunction) {
          // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
          var a0 = Bpl.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
          var a1 = HeapSucc(prevHeap, currHeap);
          var a2 = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
          req.Add(Requires(f.tok, true, BplAnd(a0, BplAnd(a1, a2)), null, null));
        }
        // modifies $Heap, $Tick
        var mod = new List<Bpl.IdentifierExpr> {
          (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)ordinaryEtran.HeapExpr,
          etran.Tick()
        };
        var ens = new List<Bpl.Ensures>();

        var proc = new Bpl.Procedure(f.tok, "OverrideCheck$$" + f.FullSanitizedName, new List<Bpl.TypeVariable>(),
          Concat(Concat(typeInParams, inParams_Heap), inParams), outParams,
          req, mod, ens, etran.TrAttributes(f.Attributes, null));
        sink.AddTopLevelDeclaration(proc);
        var implInParams = Bpl.Formal.StripWhereClauses(inParams);
        var implOutParams = Bpl.Formal.StripWhereClauses(outParams);

#endregion

        //List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

        BoogieStmtListBuilder builder = new BoogieStmtListBuilder(this);
        List<Variable> localVariables = new List<Variable>();

        // assume traitTypeParameter == G(overrideTypeParameters);
        AddOverrideCheckTypeArgumentInstantiations(f, builder, localVariables);

        if (f is TwoStateFunction) {
          // $Heap := current$Heap;
          var heap = (Bpl.IdentifierExpr /*TODO: this cast is somewhat dubious*/)ordinaryEtran.HeapExpr;
          builder.Add(Bpl.Cmd.SimpleAssign(f.tok, heap, etran.HeapExpr));
          etran = ordinaryEtran;  // we no longer need the special heap names
        }

        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < f.Formals.Count; i++) {
          //get corresponsing formal in the class
          var ie = new IdentifierExpr(f.Formals[i].tok, f.Formals[i].AssignUniqueName(f.IdGenerator));
          ie.Var = f.Formals[i]; ie.Type = ie.Var.Type;
          substMap.Add(f.OverriddenFunction.Formals[i], ie);
        }

        if (f.OverriddenFunction.Result != null) {
          Contract.Assert(pOut != null);
          //get corresponsing formal in the class
          var ie = new IdentifierExpr(pOut.tok, pOut.AssignUniqueName(f.IdGenerator));
          ie.Var = pOut; ie.Type = ie.Var.Type;
          substMap.Add(f.OverriddenFunction.Result, ie);
        }

        //adding assume Pre’; assert P; // this checks that Pre’ implies P
        AddFunctionOverrideReqsChk(f, builder, etran, substMap);

        //adding assert R <= Rank’;
        AddOverrideTerminationChk(f, f.OverriddenFunction, builder, etran, substMap);

        //adding assert W <= Frame’
        AddFunctionOverrideSubsetChk(f, builder, etran, localVariables, substMap);

        //adding assume Q; assert Post’;
        //adding assume J.F(ins) == C.F(ins);
        AddFunctionOverrideEnsChk(f, builder, etran, substMap, implInParams, implOutParams.Count == 0 ? null : implOutParams[0]);

        var stmts = builder.Collect(f.tok);

        if (EmitImplementation(f.Attributes)) {
          // emit the impl only when there are proof obligations.
          QKeyValue kv = etran.TrAttributes(f.Attributes, null);

          var impl = new Bpl.Implementation(f.tok, proc.Name, new List<Bpl.TypeVariable>(),
            Concat(Concat(typeInParams, inParams_Heap), implInParams), implOutParams, localVariables, stmts, kv);
          sink.AddTopLevelDeclaration(impl);
        }

        if (InsertChecksums)
        {
            InsertChecksum(f, proc, true);
        }

        Reset();
    }

    private void AddOverrideCheckTypeArgumentInstantiations(MemberDecl member, BoogieStmtListBuilder builder, List<Variable> localVariables) {
      Contract.Requires(member is Function || member is Method);
      Contract.Requires(member.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);

      MemberDecl overriddenMember;
      List<TypeParameter> overriddenTypeParameters;
      if (member is Function) {
        var o = ((Function)member).OverriddenFunction;
        overriddenMember = o;
        overriddenTypeParameters = o.TypeArgs;
      } else {
        var o = ((Method)member).OverriddenMethod;
        overriddenMember = o;
        overriddenTypeParameters = o.TypeArgs;
      }
      var typeMap = GetTypeArgumentSubstitutionMap(overriddenMember, member);
      foreach (var tp in Concat(overriddenMember.EnclosingClass.TypeArgs, overriddenTypeParameters)) {
        var local = BplLocalVar(nameTypeParam(tp), predef.Ty, out var lhs);
        localVariables.Add(local);
        var rhs = TypeToTy(typeMap[tp]);
        builder.Add(new Bpl.AssumeCmd(tp.tok, Bpl.Expr.Eq(lhs, rhs)));
      }
    }

    private void AddFunctionOverrideEnsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap, List<Bpl.Variable> implInParams, Bpl.Variable/*?*/ resultVariable) {
      Contract.Requires(f.Formals.Count <= implInParams.Count);

      //generating class post-conditions
      foreach (var en in f.Ens)
      {
        builder.Add(TrAssumeCmd(f.tok, etran.TrExpr(en.E)));
      }

      //generating assume J.F(ins) == C.F(ins)
      Bpl.FunctionCall funcIdC = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
      Bpl.FunctionCall funcIdT = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.OverriddenFunction.tok, f.OverriddenFunction.FullSanitizedName, TrType(f.OverriddenFunction.ResultType)));
      List<Bpl.Expr> argsC = new List<Bpl.Expr>();
      List<Bpl.Expr> argsT = new List<Bpl.Expr>();
      // add type arguments
      argsT.AddRange(GetTypeArguments(f.OverriddenFunction, f).ConvertAll(TypeToTy));
      argsC.AddRange(GetTypeArguments(f, null).ConvertAll(TypeToTy));
      // add fuel arguments
      if (f.IsFuelAware())
      {
        argsC.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }
      if (f.OverriddenFunction.IsFuelAware())
      {
        argsT.Add(etran.layerInterCluster.GetFunctionFuel(f));
      }
      // add heap arguments
      if (f is TwoStateFunction) {
        argsC.Add(etran.Old.HeapExpr);
        argsT.Add(etran.Old.HeapExpr);
      }
      if (AlwaysUseHeap || f.ReadsHeap)
      {
        argsC.Add(etran.HeapExpr);
      }
      if (AlwaysUseHeap || f.OverriddenFunction.ReadsHeap)
      {
        argsT.Add(etran.HeapExpr);
      }
      // add "ordinary" parameters (including "this", if any)
      var prefixCount = implInParams.Count - f.Formals.Count;
      for (var i = 0; i < implInParams.Count; i++) {
        Bpl.Expr cParam = new Bpl.IdentifierExpr(f.tok, implInParams[i]);
        Bpl.Expr tParam = new Bpl.IdentifierExpr(f.OverriddenFunction.tok, implInParams[i]);
        if (prefixCount <= i && ModeledAsBoxType(f.OverriddenFunction.Formals[i - prefixCount].Type)) {
          tParam = BoxIfNecessary(f.tok, tParam, f.Formals[i - prefixCount].Type);
        }
        argsC.Add(cParam);
        argsT.Add(tParam);
      }
      Bpl.Expr funcExpC = new Bpl.NAryExpr(f.tok, funcIdC, argsC);
      Bpl.Expr funcExpT = new Bpl.NAryExpr(f.OverriddenFunction.tok, funcIdT, argsT);
      var funcExpCPossiblyBoxed = funcExpC;
      if (ModeledAsBoxType(f.OverriddenFunction.ResultType)) {
        funcExpCPossiblyBoxed = BoxIfUnboxed(funcExpCPossiblyBoxed, f.ResultType);
      }
      builder.Add(TrAssumeCmd(f.tok, Bpl.Expr.Eq(funcExpCPossiblyBoxed, funcExpT)));

      //generating assume C.F(ins) == out, if a result variable was given
      if (resultVariable != null) {
        var resultVar = new Bpl.IdentifierExpr(resultVariable.tok, resultVariable);
        builder.Add(TrAssumeCmd(f.tok, Bpl.Expr.Eq(funcExpC, resultVar)));
      }

      //generating trait post-conditions with class variables
      foreach (var en in f.OverriddenFunction.Ens) {
        Expression postcond = Substitute(en.E, null, substMap);
        bool splitHappened;  // we don't actually care
        foreach (var s in TrSplitExpr(postcond, etran, false, out splitHappened)) {
          if (s.IsChecked) {
            builder.Add(Assert(f.tok, s.E, "the function must provide an equal or more detailed postcondition than in its parent trait"));
          }
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

    /// <summary>
    /// Return a type-parameter substitution map for function "f", as instantiated by the context of "overridingFunction".
    ///
    /// In more symbols, suppose "f" is declared as follows:
    ///     class/trait Tr[A,B] {
    ///       function f[C,D](...): ...
    ///     }
    /// and "overridingFunction" is declared as follows:
    ///     class/trait Cl[G] extends Tr[X(G),Y(G)] {
    ///       function f[R,S](...): ...
    ///     }
    /// Then, return the following map:
    ///     A -> X(G)
    ///     B -> Y(G)
    ///     C -> R
    ///     D -> S
    ///
    /// See also GetTypeArguments.
    /// </summary>
    private static Dictionary<TypeParameter, Type> GetTypeArgumentSubstitutionMap(MemberDecl member, MemberDecl overridingMember) {
      Contract.Requires(member is Function || member is Method);
      Contract.Requires(overridingMember is Function || overridingMember is Method);
      Contract.Requires(overridingMember.EnclosingClass is TopLevelDeclWithMembers);
      Contract.Requires(((ICallable)member).TypeArgs.Count == ((ICallable)overridingMember).TypeArgs.Count);

      var typeMap = new Dictionary<TypeParameter, Type>();

      var cl = (TopLevelDeclWithMembers)overridingMember.EnclosingClass;
      var classTypeMap = cl.ParentFormalTypeParametersToActuals;
      member.EnclosingClass.TypeArgs.ForEach(tp => typeMap.Add(tp, classTypeMap[tp]));

      var origTypeArgs = ((ICallable)member).TypeArgs;
      var overridingTypeArgs = ((ICallable)overridingMember).TypeArgs;
      for (var i = 0; i < origTypeArgs.Count; i++) {
        var otp = overridingTypeArgs[i];
        typeMap.Add(origTypeArgs[i], new UserDefinedType(otp.tok, otp));
      }

      return typeMap;
    }

    private void HavocFunctionFrameLocations(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables)
    {
        // play havoc with the heap according to the modifies clause
        builder.Add(new Bpl.HavocCmd(f.tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
        // assume the usual two-state boilerplate information
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(f.tok, f.Reads, f.IsGhost, etran.Old, etran, etran.Old))
        {
            if (tri.IsFree)
            {
                builder.Add(TrAssumeCmd(f.tok, tri.Expr));
            }
        }
    }

    private void AddFunctionOverrideSubsetChk(Function func, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables, Dictionary<IVariable, Expression> substMap)
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

    private void AddFunctionOverrideReqsChk(Function f, BoogieStmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
      Contract.Requires(f != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating trait pre-conditions with class variables
      foreach (var req in f.OverriddenFunction.Req) {
        Expression precond = Substitute(req.E, null, substMap);
        builder.Add(TrAssumeCmd(f.tok, etran.TrExpr(precond)));
      }
      //generating class pre-conditions
      foreach (var req in f.Req) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(req.E, etran, false, out splitHappened)) {
          if (s.IsChecked) {
            builder.Add(Assert(f.tok, s.E, "the function must provide an equal or more permissive precondition than in its parent trait"));
          }
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
        Contract.Requires(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext == null);
        Contract.Ensures(currentModule == null && codeContext == null && _tmpIEs.Count == 0 && isAllocContext == null);

        currentModule = m.EnclosingClass.EnclosingModuleDefinition;
        codeContext = m;
        isAllocContext = new IsAllocContext(m.IsGhost);

        List<Variable> inParams = Bpl.Formal.StripWhereClauses(proc.InParams);
        List<Variable> outParams = Bpl.Formal.StripWhereClauses(proc.OutParams);

        var builder = new BoogieStmtListBuilder(this);
        var etran = new ExpressionTranslator(this, predef, m.tok);
        var localVariables = new List<Variable>();

        // assume traitTypeParameter == G(overrideTypeParameters);
        AddOverrideCheckTypeArgumentInstantiations(m, builder, localVariables);

        if (m is TwoStateLemma) {
          // $Heap := current$Heap;
          var heap = (Bpl.IdentifierExpr /*TODO: this cast is somewhat dubious*/)new ExpressionTranslator(this, predef, m.tok).HeapExpr;
          builder.Add(Bpl.Cmd.SimpleAssign(m.tok, heap, new Bpl.IdentifierExpr(m.tok, "current$Heap", predef.HeapType)));
        }


        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < m.Ins.Count; i++)
        {
            //get corresponsing formal in the class
            var ie = new IdentifierExpr(m.Ins[i].tok, m.Ins[i].AssignUniqueName(m.IdGenerator));
            ie.Var = m.Ins[i]; ie.Type = ie.Var.Type;
            substMap.Add(m.OverriddenMethod.Ins[i], ie);
        }
        for (int i = 0; i < m.Outs.Count; i++)
        {
            //get corresponsing formal in the class
            var ie = new IdentifierExpr(m.Outs[i].tok, m.Outs[i].AssignUniqueName(m.IdGenerator));
            ie.Var = m.Outs[i]; ie.Type = ie.Var.Type;
            substMap.Add(m.OverriddenMethod.Outs[i], ie);
        }

        Bpl.StmtList stmts;
        //adding assume Pre’; assert P; // this checks that Pre’ implies P
        AddMethodOverrideReqsChk(m, builder, etran, substMap);

        //adding assert R <= Rank’;
        AddOverrideTerminationChk(m, m.OverriddenMethod, builder, etran, substMap);

        //adding assert W <= Frame’
        AddMethodOverrideSubsetChk(m, builder, etran, localVariables, substMap);

        if (!(m is TwoStateLemma)) {
          //change the heap at locations W
          HavocMethodFrameLocations(m, builder, etran, localVariables);
        }

        //adding assume Q; assert Post’;
        AddMethodOverrideEnsChk(m, builder, etran, substMap);

        stmts = builder.Collect(m.tok);

        if (EmitImplementation(m.Attributes)) {
          // emit the impl only when there are proof obligations.
          QKeyValue kv = etran.TrAttributes(m.Attributes, null);
          Bpl.Implementation impl = new Bpl.Implementation(m.tok, proc.Name, new List<Bpl.TypeVariable>(), inParams, outParams, localVariables, stmts, kv);
          sink.AddTopLevelDeclaration(impl);

          if (InsertChecksums) {
            InsertChecksum(m, impl);
          }
        }

        isAllocContext = null;
        Reset();
    }

    private void HavocMethodFrameLocations(Method m, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables)
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
                builder.Add(TrAssumeCmd(m.tok, tri.Expr));
            }
        }
    }

    private void AddMethodOverrideEnsChk(Method m, BoogieStmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
      Contract.Requires(m != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating class post-conditions
      foreach (var en in m.Ens) {
        builder.Add(TrAssumeCmd(m.tok, etran.TrExpr(en.E)));
      }
      //generating trait post-conditions with class variables
      foreach (var en in m.OverriddenMethod.Ens) {
        Expression postcond = Substitute(en.E, null, substMap);
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(postcond, etran, false, out splitHappened)) {
          if (s.IsChecked) {
            builder.Add(Assert(m.tok, s.E, "the method must provide an equal or more detailed postcondition than in its parent trait"));
          }
        }
      }
    }

    private void AddMethodOverrideReqsChk(Method m, BoogieStmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap)
    {
      Contract.Requires(m != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      //generating trait pre-conditions with class variables
      foreach (var req in m.OverriddenMethod.Req) {
        Expression precond = Substitute(req.E, null, substMap);
        builder.Add(TrAssumeCmd(m.tok, etran.TrExpr(precond)));
      }
      //generating class pre-conditions
      foreach (var req in m.Req) {
        bool splitHappened;  // we actually don't care
        foreach (var s in TrSplitExpr(req.E, etran, false, out splitHappened)) {
          if (s.IsChecked) {
            builder.Add(Assert(m.tok, s.E, "the method must provide an equal or more permissive precondition than in its parent trait"));
          }
        }
      }
    }

    private void AddOverrideTerminationChk(ICallable original, ICallable overryd, BoogieStmtListBuilder builder, ExpressionTranslator etran, Dictionary<IVariable, Expression> substMap) {
      Contract.Requires(original != null);
      Contract.Requires(overryd != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(substMap != null);
      // Note, it is as if the trait's method is calling the class's method.
      var contextDecreases = overryd.Decreases.Expressions;
      var calleeDecreases = original.Decreases.Expressions;
      // We want to check:  calleeDecreases <= contextDecreases (note, we can allow equality, since there is a bounded, namely 1, number of dynamic dispatches)
      if (Contract.Exists(contextDecreases, e => e is WildcardExpr)) {
        // no check needed
        return;
      }

      int N = Math.Min(contextDecreases.Count, calleeDecreases.Count);
      var toks = new List<IToken>();
      var types0 = new List<Type>();
      var types1 = new List<Type>();
      var callee = new List<Expr>();
      var caller = new List<Expr>();

      for (int i = 0; i < N; i++) {
        Expression e0 = calleeDecreases[i];
        Expression e1 = Substitute(contextDecreases[i], null, substMap);
        if (!CompatibleDecreasesTypes(e0.Type, e1.Type)) {
          N = i;
          break;
        }
        toks.Add(new NestedToken(original.Tok, e1.tok));
        types0.Add(e0.Type.NormalizeExpand());
        types1.Add(e1.Type.NormalizeExpand());
        callee.Add(etran.TrExpr(e0));
        caller.Add(etran.TrExpr(e1));
      }

      var decrCountT = contextDecreases.Count;
      var decrCountC = calleeDecreases.Count;
      // Generally, we want to produce a check "decrClass <= decrTrait", allowing (the common case where) they are equal.
      // * If N < decrCountC && N < decrCountT, then "decrClass <= decrTrait" if the comparison ever gets beyond the
      //   parts that survived truncation.  Thus, we compare with "allowNoChange" set to "false".
      // Otherwise:
      // * If decrCountC == decrCountT, then the truncation we did above had no effect and we pass in "allowNoChange" as "true".
      // * If decrCountC > decrCountT, then we will have truncated decrClass above.  Let x,y and x' denote decrClass and
      //   decrTrait, respectively, where x and x' have the same length.  Considering how Dafny in effect pads the end of
      //   decreases tuples with a \top, we were supposed to evaluate (x,(y,\top)) <= (x',\top), which by lexicographic pairs
      //   we can expand to:
      //       x <= x' && (x == x' ==> (y,\top) <= \top)
      //   which is equivalent to just x <= x'.  Thus, we called DecreasesCheck to compare x and x' and we pass in "allowNoChange"
      //   as "true".
      // * If decrCountC < decrCountT, then we will have truncated decrTrait above.  Let x and x',y' denote decrClass and
      //   decrTrait, respectively, where x and x' have the same length.  We then want to check (x,\top) <= (x',(y',\top)), which
      //   expands to:
      //       x <= x' && (x == x' ==> \top <= (y',\top))
      //    =      { \top is strictly larger than a pair }
      //       x <= x' && (x == x' ==> false)
      //    =
      //       x < x'
      //   So we perform our desired check by calling DecreasesCheck to strictly compare x and x', so we pass in "allowNoChange"
      //   as "false".
      bool allowNoChange = N == decrCountT && decrCountT <= decrCountC;
      var decrChk = DecreasesCheck(toks, types0, types1, callee, caller, null, null, allowNoChange, false);
      builder.Add(Assert(original.Tok, decrChk, string.Format("{0}'s decreases clause must be below or equal to that in the trait", original.WhatKind)));
    }

    private void AddMethodOverrideSubsetChk(Method m, BoogieStmtListBuilder builder, ExpressionTranslator etran, List<Variable> localVariables, Dictionary<IVariable, Expression> substMap)
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
      Contract.Requires(VisibleInScope(m));
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintAttributes(m.Attributes);
        printer.PrintFormals(m.Ins, m);
        if (m.Outs.Any())
        {
          writer.Write("returns ");
          printer.PrintFormals(m.Outs, m);
        }
        printer.PrintSpec("", m.Req, 0);
        printer.PrintFrameSpecLine("", m.Mod.Expressions, 0, null);
        printer.PrintSpec("", m.Ens, 0);
        printer.PrintDecreasesSpec(m.Decreases, 0);
        writer.WriteLine();
        if (!specificationOnly && m.Body != null && RevealedInScope(m)) {
          printer.PrintStatement(m.Body, 0);
        }
        data = Encoding.UTF8.GetBytes(writer.ToString());
      }

      InsertChecksum(decl, data);
    }

    private void InsertChecksum(DatatypeDecl d, Bpl.Declaration decl)
    {
      Contract.Requires(VisibleInScope(d));
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        printer.PrintDatatype(d, 0, null);
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
      Contract.Requires(f != null);
      Contract.Requires(decl != null);
      Contract.Requires(VisibleInScope(f));
      byte[] data;
      using (var writer = new System.IO.StringWriter())
      {
        var printer = new Printer(writer);
        writer.Write(f.IsGhost ? "function" : "function method");
        printer.PrintAttributes(f.Attributes);
        printer.PrintFormals(f.Formals, f);
        writer.Write(": ");
        printer.PrintType(f.ResultType);
        printer.PrintSpec("", f.Req, 0);
        printer.PrintFrameSpecLine("", f.Reads, 0, null);
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

    private void InsertChecksum(Bpl.Declaration decl, byte[] data)
    {
      Contract.Requires(decl != null);
      Contract.Requires(data != null);
      var md5 = System.Security.Cryptography.MD5.Create();
      var hashedData = md5.ComputeHash(data);
      var checksum = BitConverter.ToString(hashedData);

      decl.AddAttribute("checksum", checksum);

      InsertUniqueIdForImplementation(decl);
    }

    public void InsertUniqueIdForImplementation(Bpl.Declaration decl)
    {
      var impl = decl as Bpl.Implementation;
      var prefix = UniqueIdPrefix ?? (decl.tok.filename == null ? "" : System.Text.RegularExpressions.Regex.Replace(decl.tok.filename, @".v\d+.dfy", ".dfy"));
      if (impl != null && !string.IsNullOrEmpty(prefix))
      {
        decl.AddAttribute("id", prefix + ":" + impl.Name + ":0");
      }
    }

    void CheckFrameWellFormed(WFOptions wfo, List<FrameExpression> fes, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
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
                             BoogieStmtListBuilder builder, List<Variable> localVariables) {
      Contract.Requires(m != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);
      Contract.Requires(wellformednessProc || m.Body != null);

      if (m is TwoStateLemma) {
        // $Heap := current$Heap;
        var heap = (Bpl.IdentifierExpr /*TODO: this cast is somewhat dubious*/)new ExpressionTranslator(this, predef, m.tok).HeapExpr;
        builder.Add(Bpl.Cmd.SimpleAssign(m.tok, heap, new Bpl.IdentifierExpr(m.tok, "current$Heap", predef.HeapType)));
      }

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
                                     BoogieStmtListBuilder builder, List<Variable> localVariables) {
      Contract.Requires(iter != null);
      Contract.Requires(inParams != null);
      Contract.Requires(outParams != null);
      Contract.Requires(builder != null);
      Contract.Requires(localVariables != null);
      Contract.Requires(predef != null);

      // set up the information used to verify the method's modifies clause
      var iteratorFrame = new List<FrameExpression>();
      var th = new ThisExpr(iter);
      iteratorFrame.Add(new FrameExpression(iter.tok, th, null));
      iteratorFrame.AddRange(iter.Modifies.Expressions);
      DefineFrame(iter.tok, iteratorFrame, builder, localVariables, null);
      builder.Add(CaptureState(iter.tok, false, "initial state"));
    }

    Bpl.Cmd CaptureState(IToken tok, bool isEndToken, string/*?*/ additionalInfo) {
      Contract.Requires(tok != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      var col = tok.col + (isEndToken ? tok.val.Length : 0);
      string description = String.Format("{0}{1}", ErrorReporter.TokenToString(tok), additionalInfo == null ? "" : (": " + additionalInfo));
      QKeyValue kv = new QKeyValue(tok, "captureState", new List<object>() { description }, null);
      return TrAssumeCmd(tok, Bpl.Expr.True, kv);
    }
    Bpl.Cmd CaptureState(Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Ensures(Contract.Result<Bpl.Cmd>() != null);
      return CaptureState(stmt.EndTok, true, null);
    }

    void DefineFrame(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frameClause,
      BoogieStmtListBuilder/*!*/ builder, List<Variable>/*!*/ localVariables, string name, ExpressionTranslator/*?*/ etran = null)
    {
      Contract.Requires(tok != null);
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
      Bpl.IdentifierExpr theFrame = etran.TheFrame(tok);  // this is a throw-away expression, used only to extract the type and name of the $_Frame variable
      Contract.Assert(theFrame.Type != null);  // follows from the postcondition of TheFrame
      Bpl.LocalVariable frame = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name ?? theFrame.Name, theFrame.Type));
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
                          ExpressionTranslator /*!*/ etran,
                          BoogieStmtListBuilder /*!*/ builder,
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
      Contract.Requires(receiverReplacement == null || substMap != null);
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
    void AddFrameAxiom(Function f)
    {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);

      var comment = "frame axiom for " + f.FullSanitizedName;
      // This is the general case
      Bpl.Expr prevH = null;
      Bpl.BoundVariable prevHVar = null;
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
      Bpl.Expr oNotNullAlloced = !AlwaysUseHeap ? oNotNull : Bpl.Expr.And(oNotNull, etran0.IsAlloced(f.tok, o));
      Bpl.Expr unchanged = Bpl.Expr.Eq(ReadHeap(f.tok, h0, o, field), ReadHeap(f.tok, h1, o, field));

      Bpl.Expr h0IsHeapAnchor = FunctionCall(h0.tok, BuiltinFunction.IsHeapAnchor, null, h0);
      Bpl.Expr heapSucc = HeapSucc(h0, h1);
      Bpl.Expr r0 = InRWClause(f.tok, o, field, f.Reads, etran0, null, null);
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

      if (prevH != null) {
        bvars.Add(prevHVar);
        f0args.Add(prevH); f1args.Add(prevH); f0argsCanCall.Add(prevH); f1argsCanCall.Add(prevH);
      }
      bvars.Add(h0Var); bvars.Add(h1Var);
      f0args.Add(h0); f1args.Add(h1); f0argsCanCall.Add(h0); f1argsCanCall.Add(h1);

      var useAlloc = CommonHeapUse && !AlwaysUseHeap && f.Reads.Exists(fe => fe.E is WildcardExpr) ? ISALLOC : NOALLOC;
      if (!f.IsStatic) {
        Bpl.Expr th; var thVar = BplBoundVar("this", TrReceiverType(f), out th);
        bvars.Add(thVar);
        f0args.Add(th); f1args.Add(th); f0argsCanCall.Add(th); f1argsCanCall.Add(th);

        Type thisType = Resolver.GetReceiverType(f.tok, f);
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
      // "rw" is is allowed to contain a WildcardExpr

      Bpl.Expr disjunction = Bpl.Expr.False;
      foreach (FrameExpression rwComponent in rw) {
        Expression e = rwComponent.E;
        if (substMap != null) {
          e = Substitute(e, receiverReplacement, substMap);
        }

        e = Resolver.FrameArrowToObjectSet(e, CurrentIdGenerator, program.BuiltIns);

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
          disjunct = AlwaysUseHeap ? Bpl.Expr.True : etran.IsAlloced(tok, o);
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

    private void AddWellformednessCheck(Function f) {
      Contract.Requires(f != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(f.EnclosingClass != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext != null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext != null);

      Contract.Assert(InVerificationScope(f));

      currentModule = f.EnclosingClass.EnclosingModuleDefinition;
      codeContext = f;

      Bpl.Expr prevHeap = null;
      Bpl.Expr currHeap = null;
      var ordinaryEtran = new ExpressionTranslator(this, predef, f.tok);
      ExpressionTranslator etran;
      var inParams_Heap = new List<Bpl.Variable>();
      if (f is TwoStateFunction) {
        var prevHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "previous$Heap", predef.HeapType), true);
        var currHeapVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "current$Heap", predef.HeapType), true);
        inParams_Heap.Add(prevHeapVar);
        inParams_Heap.Add(currHeapVar);
        prevHeap = new Bpl.IdentifierExpr(f.tok, prevHeapVar);
        currHeap = new Bpl.IdentifierExpr(f.tok, currHeapVar);
        etran = new ExpressionTranslator(this, predef, currHeap, prevHeap);
      } else {
        etran = ordinaryEtran;
      }

      // parameters of the procedure
      var typeInParams = MkTyParamFormals(GetTypeParams(f));
      var inParams = new List<Bpl.Variable>();
      var outParams = new List<Bpl.Variable>();
      if (!f.IsStatic) {
        var th = new Bpl.IdentifierExpr(f.tok, "this", TrReceiverType(f));
        Bpl.Expr wh = Bpl.Expr.And(
          ReceiverNotNull(th),
          (f is TwoStateFunction ? etran.Old : etran).GoodRef(f.tok, th, Resolver.GetReceiverType(f.tok, f)));
        Bpl.Formal thVar = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f), wh), true);
        inParams.Add(thVar);
      }
      foreach (Formal p in f.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType), p.Type,
          p.IsOld ? etran.Old : etran, CommonHeapUse && f is TwoStateFunction ? ISALLOC : NOALLOC);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }
      if (f.Result != null) {
        Formal p = f.Result;
        Contract.Assert(!p.IsOld);
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), varType), p.Type, etran, NOALLOC);
        outParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), varType, wh), true));
      }
      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
      req.Add(Requires(f.tok, true, etran.HeightContext(f), null, null));
      if (f is TwoStateFunction) {
        // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
        var a0 = Bpl.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
        var a1 = HeapSucc(prevHeap, currHeap);
        var a2 = FunctionCall(f.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
        req.Add(Requires(f.tok, true, BplAnd(a0, BplAnd(a1, a2)), null, null));
      }

      // modifies $Heap, $Tick
      var mod = new List<Bpl.IdentifierExpr> {
        (Bpl.IdentifierExpr /*TODO: this cast is rather dubious*/)ordinaryEtran.HeapExpr,
        etran.Tick()
      };
      // check that postconditions hold
      var ens = new List<Bpl.Ensures>();
      foreach (AttributedExpression p in f.Ens) {
        var functionHeight = currentModule.CallGraph.GetSCCRepresentativeId(f);
        var splits = new List<SplitExprInfo>();
        bool splitHappened /*we actually don't care*/ = TrSplitExpr(p.E, splits, true, functionHeight, true, true, etran);
        string errorMessage = CustomErrorMessage(p.Attributes);
        foreach (var s in splits) {
          if (s.IsChecked && !RefinementToken.IsInherited(s.E.tok, currentModule)) {
            AddEnsures(ens, Ensures(s.E.tok, false, s.E, errorMessage, null));
          }
        }
      }
      var proc = new Bpl.Procedure(f.tok, "CheckWellformed$$" + f.FullSanitizedName, new List<Bpl.TypeVariable>(),
        Concat(Concat(typeInParams, inParams_Heap), inParams), outParams,
        req, mod, ens, etran.TrAttributes(f.Attributes, null));
      sink.AddTopLevelDeclaration(proc);

      if (InsertChecksums) {
        InsertChecksum(f, proc, true);
      }

      Contract.Assert(proc.InParams.Count == typeInParams.Count + inParams_Heap.Count + inParams.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var implOutParams = Bpl.Formal.StripWhereClauses(outParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this);
      var builderInitializationArea = new BoogieStmtListBuilder(this);
      builder.Add(new CommentCmd("AddWellformednessCheck for function " + f));
      if (f is TwoStateFunction) {
        // $Heap := current$Heap;
        var heap = (Bpl.IdentifierExpr /*TODO: this cast is somewhat dubious*/)ordinaryEtran.HeapExpr;
        builder.Add(Bpl.Cmd.SimpleAssign(f.tok, heap, etran.HeapExpr));
        etran = ordinaryEtran;  // we no longer need the special heap names
      }
      builder.Add(CaptureState(f.tok, false, "initial state"));

      DefineFrame(f.tok, f.Reads, builder, locals, null);
      InitializeFuelConstant(f.tok, builder, etran);

      // Check well-formedness of any default-value expressions (before assuming preconditions).
      var wfo = new WFOptions(null, true, true, true); // no reads or termination checks
      foreach (var formal in f.Formals.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformed(e, wfo, locals, builder, etran);
        builder.Add(new Bpl.AssumeCmd(e.tok, CanCallAssumption(e, etran)));
        CheckSubrange(e.tok, etran.TrExpr(e), e.Type, formal.Type, builder);

        if (formal.IsOld) {
          Bpl.Expr wh = GetWhereClause(e.tok, etran.TrExpr(e), e.Type, etran.Old, ISALLOC, true);
          if (wh != null) {
            builder.Add(Assert(e.tok, wh, "default value must be allocated in the two-state function's previous state"));
          }
        }
      }
      wfo.ProcessSavedReadsChecks(locals, builderInitializationArea, builder);

      // Check well-formedness of the preconditions (including termination), and then
      // assume each one of them.  After all that (in particular, after assuming all
      // of them), do the postponed reads checks.
      wfo = new WFOptions(null, true, true /* do delayed reads checks */);
      foreach (AttributedExpression p in f.Req) {
        CheckWellformedAndAssume(p.E, wfo, locals, builder, etran);
      }
      wfo.ProcessSavedReadsChecks(locals, builderInitializationArea, builder);

      // Check well-formedness of the reads clause.  Note that this is done after assuming
      // the preconditions.  In other words, the well-formedness of the reads clause is
      // allowed to assume the precondition (yet, the requires clause is checked to
      // read only those things indicated in the reads clause).
      wfo = new WFOptions(null, true, true /* do delayed reads checks */);
      CheckFrameWellFormed(wfo, f.Reads, locals, builder, etran);
      wfo.ProcessSavedReadsChecks(locals, builderInitializationArea, builder);

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
      BoogieStmtListBuilder postCheckBuilder = new BoogieStmtListBuilder(this);
      // Assume the type returned by the call itself respects its type (this matters if the type is "nat", for example)
      {
        var args = new List<Bpl.Expr>();
        foreach (var p in GetTypeParams(f)) {
          args.Add(trTypeParamOrOpaqueType(p));
        }
        if (f.IsFuelAware()) {
          args.Add(etran.layerInterCluster.GetFunctionFuel(f));
        }
        if (f is TwoStateFunction) {
          args.Add(etran.Old.HeapExpr);
        }
        if (AlwaysUseHeap || f.ReadsHeap) {
          args.Add(etran.HeapExpr);
        }
        if (!f.IsStatic) {
          args.Add(new Bpl.IdentifierExpr(f.tok, etran.This));
        }
        foreach (var p in f.Formals) {
          args.Add(new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)));
        }
        Bpl.IdentifierExpr funcID = new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType));
        Bpl.Expr funcAppl = new Bpl.NAryExpr(f.tok, new Bpl.FunctionCall(funcID), args);

        var wh = GetWhereClause(f.tok, funcAppl, f.ResultType, etran, NOALLOC);
        if (wh != null) {
          postCheckBuilder.Add(TrAssumeCmd(f.tok, wh));
        }
      }
      // Now for the ensures clauses
      foreach (AttributedExpression p in f.Ens) {
        // assume the postcondition for the benefit of checking the remaining postconditions
        CheckWellformedAndAssume(p.E, new WFOptions(f, false), locals, postCheckBuilder, etran);
      }
      // Here goes the body (and include both termination checks and reads checks)
      BoogieStmtListBuilder bodyCheckBuilder = new BoogieStmtListBuilder(this);
      if (f.Body == null || !RevealedInScope(f)) {
        // don't fall through to postcondition checks
        bodyCheckBuilder.Add(TrAssumeCmd(f.tok, Bpl.Expr.False));
      } else {
        Bpl.FunctionCall funcID = new Bpl.FunctionCall(new Bpl.IdentifierExpr(f.tok, f.FullSanitizedName, TrType(f.ResultType)));
        List<Bpl.Expr> args = new List<Bpl.Expr>();
        foreach (var p in GetTypeParams(f)) {
          args.Add(trTypeParamOrOpaqueType(p));
        }
        if (f.IsFuelAware()) {
          args.Add(etran.layerInterCluster.GetFunctionFuel(f));
        }
        if (f is TwoStateFunction) {
          args.Add(etran.Old.HeapExpr);
        }
        if (AlwaysUseHeap || f.ReadsHeap) {
          args.Add(etran.HeapExpr);
        }
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

        wfo = new WFOptions(null, true, true /* do delayed reads checks */);
        CheckWellformedWithResult(f.Body, wfo, funcAppl, f.ResultType, locals, bodyCheckBuilder, etran);
        if (f.Result != null) {
          bodyCheckBuilder.Add(TrAssumeCmd(f.tok, Bpl.Expr.Eq(funcAppl, TrVar(f.tok, f.Result))));
        }
        wfo.ProcessSavedReadsChecks(locals, builderInitializationArea, bodyCheckBuilder);
      }
      // Combine the two, letting the postcondition be checked on after the "bodyCheckBuilder" branch
      postCheckBuilder.Add(TrAssumeCmd(f.tok, Bpl.Expr.False));
      builder.Add(new Bpl.IfCmd(f.tok, null, postCheckBuilder.Collect(f.tok), null, bodyCheckBuilder.Collect(f.tok)));

      var s0 = builderInitializationArea.Collect(f.tok);
      var s1 = builder.Collect(f.tok);
      var implBody = new StmtList(new List<BigBlock>(s0.BigBlocks.Concat(s1.BigBlocks)), f.tok);

      if (EmitImplementation(f.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(f.Attributes, null);
        var impl = new Bpl.Implementation(f.tok, proc.Name,
          new List<Bpl.TypeVariable>(), Concat(Concat(typeInParams, inParams_Heap), implInParams), implOutParams,
          locals, implBody, kv);
        sink.AddTopLevelDeclaration(impl);
        if (InsertChecksums) {
          InsertChecksum(f, impl);
        }
      }

      Contract.Assert(currentModule == f.EnclosingClass.EnclosingModuleDefinition);
      Contract.Assert(codeContext == f);
      Reset();
    }

    void AddWellformednessCheck(RedirectingTypeDecl decl) {
      Contract.Requires(decl != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null);

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
      codeContext = decl;
      var etran = new ExpressionTranslator(this, predef, decl.tok);

      // parameters of the procedure
      var inParams = MkTyParamFormals(decl.TypeArgs);
      Bpl.Type varType = TrType(decl.Var.Type);
      Bpl.Expr wh = GetWhereClause(decl.Var.tok, new Bpl.IdentifierExpr(decl.Var.tok, decl.Var.AssignUniqueName(decl.IdGenerator), varType), decl.Var.Type, etran, NOALLOC);
      inParams.Add(new Bpl.Formal(decl.Var.tok, new Bpl.TypedIdent(decl.Var.tok, decl.Var.AssignUniqueName(decl.IdGenerator), varType, wh), true));

      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == TypeContextHeight;
      req.Add(Requires(decl.tok, true, etran.HeightContext(decl), null, null));
      // modifies $Heap, $Tick
      var mod = new List<Bpl.IdentifierExpr> {
        (Bpl.IdentifierExpr /*TODO: this cast is rather dubious*/)etran.HeapExpr,
        etran.Tick()
      };
      var proc = new Bpl.Procedure(decl.tok, "CheckWellformed$$" + decl.FullSanitizedName, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        req, mod, new List<Bpl.Ensures>(), etran.TrAttributes(decl.Attributes, null));
      sink.AddTopLevelDeclaration(proc);

      // TODO: Can a checksum be inserted here?

      Contract.Assert(proc.InParams.Count == inParams.Count);
      // Changed the next line to strip from inParams instead of proc.InParams
      // They should be the same, but hence the added contract
      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for {0} {1}", decl.WhatKind, decl)));
      builder.Add(CaptureState(decl.tok, false, "initial state"));
      isAllocContext = new IsAllocContext(true);

      DefineFrame(decl.tok, new List<FrameExpression>(), builder, locals, null);

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
      var constraintCheckBuilder = new BoogieStmtListBuilder(this);
      var builderInitializationArea = new BoogieStmtListBuilder(this);
      var wfo = new WFOptions(null, true, true /* do delayed reads checks */);
      CheckWellformedAndAssume(decl.Constraint, wfo, locals, constraintCheckBuilder, etran);
      wfo.ProcessSavedReadsChecks(locals, builderInitializationArea, constraintCheckBuilder);

      // Check that the type is inhabited.
      // Note, the possible witness in this check should be coordinated with the compiler, so the compiler knows how to do the initialization
      Expression witnessExpr = null;
      string witnessErrorMsg = null;
      var witnessCheckBuilder = new BoogieStmtListBuilder(this);
      if (decl.Witness != null) {
        // check well-formedness of the witness expression (including termination, and reads checks)
        CheckWellformed(decl.Witness, new WFOptions(null, true), locals, witnessCheckBuilder, etran);
        // check that the witness is assignable to the type of the given bound variable
        if (decl is SubsetTypeDecl) {
          // Note, for new-types, this has already been checked by CheckWellformed.
          CheckResultToBeInType(decl.Witness.tok, decl.Witness, decl.Var.Type, locals, witnessCheckBuilder, etran);
        }
        // check that the witness expression checks out
        witnessExpr = Substitute(decl.Constraint, decl.Var, decl.Witness);
        witnessErrorMsg = "the given witness expression might not satisfy constraint";
      } else if (decl.WitnessKind == SubsetTypeDecl.WKind.CompiledZero) {
        var witness = Zero(decl.tok, decl.Var.Type);
        var errMsg = "cannot find witness that shows type is inhabited";
        var hintMsg = "; try giving a hint through a 'witness' or 'ghost witness' clause, or use 'ghost *' to treat as a possibly empty type";
        if (witness == null) {
          witnessCheckBuilder.Add(Assert(decl.tok, Bpl.Expr.False, $"{errMsg}{hintMsg}"));
        } else {
          // before trying 0 as a witness, check that 0 can be assigned to decl.Var
          var witnessString = Printer.ExprToString(witness);
          CheckResultToBeInType(decl.tok, witness, decl.Var.Type, locals, witnessCheckBuilder, etran, $"trying witness {witnessString}: ");
          witnessExpr = Substitute(decl.Constraint, decl.Var, witness);
          witnessErrorMsg = $"{errMsg} (only tried {witnessString}){hintMsg}";
        }
      }
      if (witnessExpr != null) {
        Contract.Assert(witnessErrorMsg != null);
        var witnessCheckTok = decl.Witness != null ? decl.Witness.tok : decl.tok;
        witnessCheckBuilder.Add(new Bpl.AssumeCmd(witnessCheckTok, CanCallAssumption(witnessExpr, etran)));
        var witnessCheck = etran.TrExpr(witnessExpr);

        bool splitHappened;
        var ss = TrSplitExpr(witnessExpr, etran, true, out splitHappened);
        if (!splitHappened) {
          witnessCheckBuilder.Add(Assert(witnessCheckTok, etran.TrExpr(witnessExpr), witnessErrorMsg));
        } else {
          foreach (var split in ss) {
            if (split.IsChecked) {
              var tok = new NestedToken(witnessCheckTok, split.E.tok);
              witnessCheckBuilder.Add(AssertNS(tok, split.E, witnessErrorMsg));
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

        var impl = new Bpl.Implementation(decl.tok, proc.Name,
          new List<Bpl.TypeVariable>(), implInParams, new List<Variable>(),
          locals, implBody, kv);
        sink.AddTopLevelDeclaration(impl);
      }

      // TODO: Should a checksum be inserted here?

      Contract.Assert(currentModule == decl.Module);
      Contract.Assert(codeContext == decl);
      isAllocContext = null;
      Reset();
    }

    void AddWellformednessCheck(ConstantField decl) {
      Contract.Requires(decl != null);
      Contract.Requires(sink != null && predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null && fuelContext == null);

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
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(decl.EnclosingClass));
      if (!decl.IsStatic) {
        var receiverType = Resolver.GetThisType(decl.tok, (TopLevelDeclWithMembers)decl.EnclosingClass);
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
      req.Add(Requires(decl.tok, true, etran.HeightContext(decl), null, null));
      var heapVar = new Bpl.IdentifierExpr(decl.tok, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar, etran.Tick() };
      var proc = new Bpl.Procedure(decl.tok, "CheckWellformed$$" + decl.FullSanitizedName, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        req, varlist, new List<Bpl.Ensures>(), etran.TrAttributes(decl.Attributes, null));
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for {0} {1}", decl.WhatKind, decl)));
      builder.Add(CaptureState(decl.tok, false, "initial state"));
      isAllocContext = new IsAllocContext(true);

      DefineFrame(decl.tok, new List<FrameExpression>(), builder, locals, null);

      // check well-formedness of the RHS expression
      CheckWellformed(decl.Rhs, new WFOptions(null, true), locals, builder, etran);
      builder.Add(new Bpl.AssumeCmd(decl.Rhs.tok, CanCallAssumption(decl.Rhs, etran)));
      CheckSubrange(decl.Rhs.tok, etran.TrExpr(decl.Rhs), decl.Rhs.Type, decl.Type, builder);

      if (EmitImplementation(decl.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(decl.Attributes, null);
        var implBody = builder.Collect(decl.tok);
        var impl = new Bpl.Implementation(decl.tok, proc.Name,
          new List<Bpl.TypeVariable>(), implInParams, new List<Variable>(),
          locals, implBody, kv);
        sink.AddTopLevelDeclaration(impl);
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
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(ctor.EnclosingDatatype));
      foreach (var p in ctor.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.tok, new Bpl.IdentifierExpr(p.tok, p.AssignUniqueName(ctor.IdGenerator), varType), p.Type, etran, NOALLOC);
        inParams.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(ctor.IdGenerator), varType, wh), true));
      }

      // the procedure itself
      var req = new List<Bpl.Requires>();
      // free requires mh == ModuleContextHeight && fh == TypeContextHeight;
      req.Add(Requires(ctor.tok, true, etran.HeightContext(ctor.EnclosingDatatype), null, null));
      var heapVar = new Bpl.IdentifierExpr(ctor.tok, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar, etran.Tick() };
      var proc = new Bpl.Procedure(ctor.tok, "CheckWellformed$$" + ctor.FullName, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        req, varlist, new List<Bpl.Ensures>(), etran.TrAttributes(ctor.Attributes, null));
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new List<Variable>();
      var builder = new BoogieStmtListBuilder(this);
      builder.Add(new CommentCmd(string.Format("AddWellformednessCheck for datatype constructor {0}", ctor)));
      builder.Add(CaptureState(ctor.tok, false, "initial state"));
      isAllocContext = new IsAllocContext(true);

      DefineFrame(ctor.tok, new List<FrameExpression>(), builder, locals, null);

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
        var impl = new Bpl.Implementation(ctor.tok, proc.Name,
          new List<Bpl.TypeVariable>(), implInParams, new List<Variable>(),
          locals, implBody, kv);
        sink.AddTopLevelDeclaration(impl);
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
        var pFormalType = Resolver.SubstType(mc.Ctor.Formals[i].Type, subst);
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
        if (e.ResolvedUpdateExpr != null)
        {
          return CanCallAssumption(e.ResolvedUpdateExpr, etran);
        }
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
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null);
          Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
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
            if (7 <= DafnyOptions.O.ArithMode) {
              if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int) && !DafnyOptions.O.DisableNLarith) {
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
        var q = e as QuantifierExpr;
        if (q != null && q.SplitQuantifier != null) {
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
            var p = new Bpl.NAryExpr(mc.tok, new Bpl.FunctionCall(mc.ProjectionFunctions[i]), new List<Bpl.Expr> { F });
            substMap.Add(e.BoundVars[i], new BoogieWrapper(p, e.BoundVars[i].Type));
          }
          var Rprime = etran.TrExpr(Substitute(mc.Range, null, substMap));
          var Fprime = etran.TrExpr(Substitute(mc.TermLeft, null, substMap));
          var defn = BplForall(bvs, trig, BplImp(R, BplAnd(Rprime, Bpl.Expr.Eq(F, Fprime))));
          canCall = BplAnd(canCall, defn);
        }
        // Create a list of all possible bound variables
        var bvarsAndAntecedents = etran.TrBoundVariables_SeparateWhereClauses(e.BoundVars);
        if (q != null) {
          var tyvars = MkTyParamBinders(q.TypeArgs);
          foreach (var tv in tyvars) {
            bvarsAndAntecedents.Add(Tuple.Create<Bpl.Variable, Bpl.Expr>(tv, null));
          }
        }
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

    void CheckCasePatternShape<VT>(CasePattern<VT> pat, Bpl.Expr rhs, IToken rhsTok, Type rhsType, BoogieStmtListBuilder builder) where VT: IVariable {
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
        var typeSubstMap = Resolver.TypeSubstitutionMap(rhsTypeUdt.ResolvedClass.TypeArgs, rhsTypeUdt.TypeArgs);

        var ctor = pat.Ctor;
        var correctConstructor = FunctionCall(pat.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, rhs);
        if (ctor.EnclosingDatatype.Ctors.Count == 1) {
          // There is only one constructor, so the value must have been constructed by it; might as well assume that here.
          builder.Add(TrAssumeCmd(pat.tok, correctConstructor));
        } else {
          builder.Add(Assert(pat.tok, correctConstructor, string.Format("RHS is not certain to look like the pattern '{0}'", ctor.Name)));
        }
        for (int i = 0; i < pat.Arguments.Count; i++) {
          var arg = pat.Arguments[i];
          var dtor = ctor.Destructors[i];

          var r = new Bpl.NAryExpr(arg.tok, new Bpl.FunctionCall(GetReadonlyField(dtor)), new List<Bpl.Expr> { rhs });
          Type argType = Resolver.SubstType(dtor.Type, typeSubstMap);
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
        builder.Add(Assert(tok, Bpl.Expr.Neq(etran.TrExpr(e), predef.Null), "target object may be null", kv));
        if (!CommonHeapUse) {
          builder.Add(Assert(tok, MkIsAlloc(etran.TrExpr(e), e.Type, etran.HeapExpr), "target object may not be allocated", kv));
        }
      }
    }

    /// <summary>
    /// Instances of WFContext are used as an argument to CheckWellformed, supplying options for the
    /// checks to be performed.
    /// If "SelfCallsAllowance" is non-null, termination checks will be omitted for calls that look
    /// like it.  This is useful in function postconditions, where the result of the function is
    /// syntactically given as what looks like a recursive call with the same arguments.
    /// "DoReadsChecks" indicates whether or not to perform reads checks.  If so, the generated code
    /// will make references to $_Frame.  If "saveReadsChecks" is true, then the reads checks will
    /// be recorded but postponsed.  In particular, CheckWellformed will append to .Locals a list of
    /// fresh local variables and will append to .Assert assertions with appropriate error messages
    /// that can be used later.  As a convenience, the ProcessSavedReadsChecks will make use of .Locals
    /// and .Asserts (and AssignLocals) and update a given StmtListBuilder.
    /// "LValueContext" indicates that the expression checked for well-formedness is an L-value of
    /// some assignment.
    /// </summary>
    private class WFOptions
    {
      public readonly Function SelfCallsAllowance;
      public readonly bool DoReadsChecks;
      public readonly bool DoOnlyCoarseGrainedTerminationChecks; // termination checks don't look at decreases clause, but reports errors for any intra-SCC call (this is used in default-value expressions)
      public readonly List<Bpl.Variable> Locals;
      public readonly List<Bpl.Cmd> Asserts;
      public readonly bool LValueContext;
      public readonly Bpl.QKeyValue AssertKv;

      public WFOptions() {
      }

      public WFOptions(Function selfCallsAllowance, bool doReadsChecks, bool saveReadsChecks = false, bool doOnlyCoarseGrainedTerminationChecks = false) {
        Contract.Requires(!saveReadsChecks || doReadsChecks);  // i.e., saveReadsChecks ==> doReadsChecks
        SelfCallsAllowance = selfCallsAllowance;
        DoReadsChecks = doReadsChecks;
        DoOnlyCoarseGrainedTerminationChecks = doOnlyCoarseGrainedTerminationChecks;
        if (saveReadsChecks) {
          Locals = new List<Variable>();
          Asserts = new List<Bpl.Cmd>();
        }
      }

      public WFOptions(Bpl.QKeyValue kv) {
        AssertKv = kv;
      }

      /// <summary>
      /// This constructor clones the given "options", but turns off reads checks.  (I wish C# allowed
      /// me to name the constructor something to indicate this semantics in its name.  Sigh.)
      /// </summary>
      public WFOptions(WFOptions options) {
        Contract.Requires(options != null);
        SelfCallsAllowance = options.SelfCallsAllowance;
        DoReadsChecks = false;  // so just leave .Locals and .Asserts as null
        DoOnlyCoarseGrainedTerminationChecks = options.DoOnlyCoarseGrainedTerminationChecks;
        LValueContext = options.LValueContext;
        AssertKv = options.AssertKv;
      }

      /// <summary>
      /// This constructor clones the given "options", but sets "LValueContext" to "lValueContext".
      /// (I wish C# allowed me to name the constructor something to indicate this semantics in its name.  Sigh.)
      /// </summary>
      public WFOptions(bool lValueContext, WFOptions options) {
        Contract.Requires(options != null);
        SelfCallsAllowance = options.SelfCallsAllowance;
        DoReadsChecks = options.DoReadsChecks;
        DoOnlyCoarseGrainedTerminationChecks = options.DoOnlyCoarseGrainedTerminationChecks;
        Locals = options.Locals;
        Asserts = options.Asserts;
        LValueContext = lValueContext;
        AssertKv = options.AssertKv;
      }

      public Action<IToken, Bpl.Expr, string, Bpl.QKeyValue> AssertSink(Translator tran, BoogieStmtListBuilder builder) {
        return (t, e, s, qk) => {
          if (Locals != null) {
            var b = BplLocalVar(tran.CurrentIdGenerator.FreshId("b$reqreads#"), Bpl.Type.Bool, Locals);
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

      public void ProcessSavedReadsChecks(List<Variable> locals, BoogieStmtListBuilder builderInitializationArea, BoogieStmtListBuilder builder) {
        Contract.Requires(locals != null);
        Contract.Requires(builderInitializationArea != null);
        Contract.Requires(builder != null);
        Contract.Requires(Locals != null && Asserts != null);  // ProcessSavedReadsChecks should be called only if the constructor was called with saveReadsChecks

        // var b$reads_guards#0 : bool  ...
        locals.AddRange(Locals);
        // b$reads_guards#0 := true   ...
        foreach (var cmd in AssignLocals) {
          builderInitializationArea.Add(cmd);
        }
        // assert b$reads_guards#0;  ...
        foreach (var a in Asserts) {
          builder.Add(a);
        }
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
      if (lValueContext) {
        options = new WFOptions(true, options);
      }
      CheckWellformed(expr, options, locals, builder, etran);
      builder.Add(TrAssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
    }

    void CheckWellformedAndAssume(Expression expr, WFOptions options, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type != null && expr.Type.IsBoolType);
      Contract.Requires(options != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
            // WF[e0]; assume e0; WF[e1]; assume e1;
            CheckWellformedAndAssume(e.E0, options, locals, builder, etran);
            CheckWellformedAndAssume(e.E1, options, locals, builder, etran);
            return;
          case BinaryExpr.ResolvedOpcode.Imp: {
              // if (*) {
              //   WF[e0]; assume e0; WF[e1]; assume e1;
              // } else {
              //   assume e0 ==> e1;
              // }
              var bAnd = new BoogieStmtListBuilder(this);
              CheckWellformedAndAssume(e.E0, options, locals, bAnd, etran);
              CheckWellformedAndAssume(e.E1, options, locals, bAnd, etran);
              var bImp = new BoogieStmtListBuilder(this);
              bImp.Add(TrAssumeCmd(expr.tok, etran.TrExpr(expr)));
              builder.Add(new Bpl.IfCmd(expr.tok, null, bAnd.Collect(expr.tok), null, bImp.Collect(expr.tok)));
            }
            return;
          case BinaryExpr.ResolvedOpcode.Or: {
              // if (*) {
              //   WF[e0]; assume e0;
              // } else {
              //   assume !e0;
              //   WF[e1]; assume e1;
              // }
              var b0 = new BoogieStmtListBuilder(this);
              CheckWellformedAndAssume(e.E0, options, locals, b0, etran);
              var b1 = new BoogieStmtListBuilder(this);
              b1.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.E0))));
              CheckWellformedAndAssume(e.E1, options, locals, b1, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, null, b0.Collect(expr.tok), null, b1.Collect(expr.tok)));
            }
            return;
          default:
            break;
        }
      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        // if (*) {
        //   WF[test]; assume test;
        //   WF[thn]; assume thn;
        // } else {
        //   assume !test;
        //   WF[els]; assume els;
        // }
        var bThn = new BoogieStmtListBuilder(this);
        CheckWellformedAndAssume(e.Test, options, locals, bThn, etran);
        CheckWellformedAndAssume(e.Thn, options, locals, bThn, etran);
        var bEls = new BoogieStmtListBuilder(this);
        bEls.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.Test))));
        CheckWellformedAndAssume(e.Els, options, locals, bEls, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, null, bThn.Collect(expr.tok), null, bEls.Collect(expr.tok)));
        return;
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        // For (Q x :: body(x)), introduce fresh local variable x'.  Then:
        //   havoc x'
        //   WF[body(x')]; assume body(x');
        // If the quantifier is universal, then continue as:
        //   assume (\forall x :: body(x));
        // Create local variables corresponding to the type arguments:

        var typeArgumentCopies = Map(e.TypeArgs, tp => e.Refresh(tp, CurrentIdGenerator));
        var typeMap = Util.Dict(e.TypeArgs, Map(typeArgumentCopies, tp => (Type)new UserDefinedType(tp)));
        var newLocals = Map(typeArgumentCopies, tp => new Bpl.LocalVariable(tp.tok, new TypedIdent(tp.tok, nameTypeParam(tp), predef.Ty)));
        locals.AddRange(newLocals);
        // Create local variables corresponding to the bound variables:
        var substMap = SetupBoundVarsAsLocals(e.BoundVars, builder, locals, etran, typeMap);
        // Get the body of the quantifier and suitably substitute for the type variables and bound variables
        var body = Substitute(e.LogicalBody(true), null, substMap, typeMap);
        CheckWellformedAndAssume(body, options, locals, builder, etran);

        if (e is ForallExpr) {
          // Although we do the WF check on the original quantifier, we assume the split one.
          // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.
          builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(e.SplitQuantifierExpression ?? e)));
        }
        return;
      }

      // resort to the behavior of simply checking well-formedness followed by assuming the translated expression
      CheckWellformed(expr, options, locals, builder, etran);

      // NOTE: If the CheckWellformed call above found a split quantifier, it ignored
      //       the splitting and proceeded to decompose the full quantifier as
      //       normal. This call to TrExpr, on the other hand, will indeed use the
      //       split quantifier.
      builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(expr)));
    }

    /// <summary>
    /// Check the well-formedness of "expr" (but don't leave hanging around any assumptions that affect control flow)
    /// </summary>
    void CheckWellformed(Expression expr, WFOptions options, List<Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
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
                                   List<Bpl.Variable> locals, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(options != null);
      Contract.Requires((result == null) == (resultType == null));
      Contract.Requires(locals != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      var origOptions = options;
      if (options.LValueContext) {
        // Turn off LValueContext for any recursive call
        options = new WFOptions(false, options);
      }

      if (expr is StaticReceiverExpr stexpr) {
        if (stexpr.OriginalResolved != null) {
          CheckWellformedWithResult(stexpr.OriginalResolved, options, null, null, locals, builder, etran);
        }
      } else if (expr is LiteralExpr) {
        CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
      } else if (expr is ThisExpr || expr is WildcardExpr || expr is BoogieWrapper) {
        // always allowed
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        if (!origOptions.LValueContext) {
          CheckDefiniteAssignment(e, builder);
        }
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Contract.Assert(e.Type is CollectionType);
        var elementType = ((CollectionType)e.Type).Arg;
        foreach (Expression el in e.Elements) {
          CheckWellformed(el, options, locals, builder, etran);
          CheckSubrange(el.tok, etran.TrExpr(el), el.Type, elementType, builder);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Contract.Assert(e.Type is MapType);
        var keyType = ((MapType)e.Type).Domain;
        var valType = ((MapType)e.Type).Range;
        foreach (ExpressionPair p in e.Elements) {
          CheckWellformed(p.A, options, locals, builder, etran);
          CheckSubrange(p.A.tok, etran.TrExpr(p.A), p.A.Type, keyType, builder);
          CheckWellformed(p.B, options, locals, builder, etran);
          CheckSubrange(p.B.tok, etran.TrExpr(p.B), p.B.Type, valType, builder);
        }
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        CheckFunctionSelectWF("naked function", builder, etran, e, " Possible solution: eta expansion.");
        CheckWellformed(e.Obj, options, locals, builder, etran);
        if (e.Obj.Type.IsRefType) {
          if (inBodyInitContext && Expression.AsThis(e.Obj) != null && !e.Member.IsInstanceIndependentConstant) {
            // this uses the surrogate local
            if (!origOptions.LValueContext) {
              CheckDefiniteAssignmentSurrogate(expr.tok, (Field)e.Member, false, builder);
            }
          } else {
            CheckNonNull(expr.tok, e.Obj, builder, etran, options.AssertKv);
            // Check that the receiver is available in the state in which the dereference occurs
          }
        } else if (e.Member is DatatypeDestructor) {
          var dtor = (DatatypeDestructor)e.Member;
          var correctConstructor = BplOr(dtor.EnclosingCtors.ConvertAll(
            ctor => FunctionCall(e.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Obj))));
          if (dtor.EnclosingCtors.Count == dtor.EnclosingCtors[0].EnclosingDatatype.Ctors.Count) {
            // Every constructor has this destructor; might as well assume that here.
            builder.Add(TrAssumeCmd(expr.tok, correctConstructor));
          } else {
            builder.Add(Assert(expr.tok, correctConstructor,
              string.Format("destructor '{0}' can only be applied to datatype values constructed by {1}", dtor.Name, dtor.EnclosingCtorNames("or"))));
          }
        }
        if (!e.Member.IsStatic) {
          if (e.Member is TwoStateFunction) {
            Bpl.Expr wh = GetWhereClause(expr.tok, etran.TrExpr(e.Obj), e.Obj.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
            if (wh != null) {
              builder.Add(Assert(expr.tok, wh, "receiver argument must be allocated in the two-state function's previous state"));
            }
          } else if (etran.UsesOldHeap) {
            Bpl.Expr wh = GetWhereClause(expr.tok, etran.TrExpr(e.Obj), e.Obj.Type, etran, ISALLOC, true);
            if (wh != null) {
              builder.Add(Assert(expr.tok, wh, $"receiver must be allocated in the state in which its {(e.Member is Field ? "fields" : "members")} are accessed"));
            }
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
          if (!CommonHeapUse || etran.UsesOldHeap) {
            builder.Add(Assert(e.Seq.tok, MkIsAlloc(seq, eSeqType, etran.HeapExpr), "array may not be allocated"));
          }
        }
        Bpl.Expr e0 = null;
        if (eSeqType is MapType) {
          bool finite = ((MapType)eSeqType).Finite;
          e0 = etran.TrExpr(e.E0);
          CheckWellformed(e.E0, options, locals, builder, etran);
          var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
          Bpl.Expr inDomain = FunctionCall(expr.tok, f, predef.MapType(e.tok, finite, predef.BoxType, predef.BoxType), seq);
          inDomain = Bpl.Expr.Select(inDomain, BoxIfNecessary(e.tok, e0, e.E0.Type));
          builder.Add(Assert(expr.tok, inDomain, "element may not be in domain", options.AssertKv));
        } else if (eSeqType is MultiSetType) {
          // cool

        } else {
          if (e.E0 != null) {
            e0 = etran.TrExpr(e.E0);
            CheckWellformed(e.E0, options, locals, builder, etran);
            builder.Add(Assert(expr.tok, InSeqRange(expr.tok, e0, e.E0.Type, seq, isSequence, null, !e.SelectOne), e.SelectOne ? "index out of range" : "lower bound out of range", options.AssertKv));
          }
          if (e.E1 != null) {
            CheckWellformed(e.E1, options, locals, builder, etran);
            Bpl.Expr lowerBound;
            if (e0 != null && e.E0.Type.IsBitVectorType) {
              lowerBound = ConvertExpression(e.E0.tok, e0, e.E0.Type, Type.Int);
            } else {
              lowerBound = e0;
            }
            builder.Add(Assert(expr.tok, InSeqRange(expr.tok, etran.TrExpr(e.E1), e.E1.Type, seq, isSequence, lowerBound, true), "upper bound below lower bound or above length of " + (isSequence ? "sequence" : "array"), options.AssertKv));
          }
        }
        if (options.DoReadsChecks && eSeqType.IsArrayType) {
          if (e.SelectOne) {
            Contract.Assert(e.E0 != null);
            var i = etran.TrExpr(e.E0);
            i = ConvertExpression(expr.tok, i, e.E0.Type, Type.Int);
            Bpl.Expr fieldName = FunctionCall(expr.tok, BuiltinFunction.IndexField, null, i);
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
            var trigger = BplTrigger(allowedToRead); // Note, the assertion we're about to produce only seems useful in the check-only mode (that is, with subsumption 0), but if it were to be assumed, we'll use this entire RHS as the trigger
            var qq = new Bpl.ForallExpr(e.tok, new List<Variable> { iVar }, trigger, BplImp(range, allowedToRead));
            options.AssertSink(this, builder)(expr.tok, qq, "insufficient reads clause to read the indicated range of array elements", options.AssertKv);
          }
        }
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        CheckWellformed(e.Array, options, locals, builder, etran);
        Bpl.Expr array = etran.TrExpr(e.Array);
        builder.Add(Assert(e.Array.tok, Bpl.Expr.Neq(array, predef.Null), "array may be null"));
        if (!CommonHeapUse || etran.UsesOldHeap) {
          builder.Add(Assert(e.Array.tok, MkIsAlloc(array, e.Array.Type, etran.HeapExpr), "array may not be allocated"));
        }
        for (int idxId = 0; idxId < e.Indices.Count; idxId++) {
          var idx = e.Indices[idxId];
          CheckWellformed(idx, options, locals, builder, etran);

          var index = etran.TrExpr(idx);
          index = ConvertExpression(idx.tok, index, idx.Type, Type.Int);
          var lower = Bpl.Expr.Le(Bpl.Expr.Literal(0), index);
          var length = ArrayLength(idx.tok, array, e.Indices.Count, idxId);
          var upper = Bpl.Expr.Lt(index, length);
          var tok = idx is IdentifierExpr ? e.tok : idx.tok; // TODO: Reusing the token of an identifier expression would underline its definition. but this is still not perfect.

          builder.Add(Assert(tok, Bpl.Expr.And(lower, upper), String.Format("index {0} out of range", idxId), options.AssertKv));
        }
        if (options.DoReadsChecks) {
          Bpl.Expr fieldName = etran.GetArrayIndexFieldName(e.tok, e.Indices);
          options.AssertSink(this, builder)(expr.tok, Bpl.Expr.SelectTok(expr.tok, etran.TheFrame(expr.tok), array, fieldName), "insufficient reads clause to read array element", options.AssertKv);
        }
      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        if (e.ResolvedUpdateExpr != null) {
          CheckWellformedWithResult(e.ResolvedUpdateExpr, options, result, resultType, locals, builder, etran);
        } else {
          CheckWellformed(e.Seq, options, locals, builder, etran);
          Bpl.Expr seq = etran.TrExpr(e.Seq);
          Bpl.Expr index = etran.TrExpr(e.Index);
          Bpl.Expr value = etran.TrExpr(e.Value);
          var collectionType = (CollectionType)e.Seq.Type.NormalizeExpand();
          // validate index
          CheckWellformed(e.Index, options, locals, builder, etran);
          if (collectionType is SeqType) {
            builder.Add(Assert(e.Index.tok, InSeqRange(expr.tok, index, e.Index.Type, seq, true, null, false), "index out of range", options.AssertKv));
          } else {
            CheckSubrange(e.Index.tok, index, e.Index.Type, collectionType.Arg, builder);
          }
          // validate value
          CheckWellformed(e.Value, options, locals, builder, etran);
          if (collectionType is SeqType) {
            CheckSubrange(e.Value.tok, value, e.Value.Type, collectionType.Arg, builder);
          } else if (collectionType is MapType mapType) {
            CheckSubrange(e.Value.tok, value, e.Value.Type, mapType.Range, builder);
          } else if (collectionType is MultiSetType) {
            builder.Add(Assert(e.Value.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), value), "new number of occurrences might be negative", options.AssertKv));
          } else {
            Contract.Assert(false);
          }
        }
      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        int arity = e.Args.Count;
        var tt = e.Function.Type.AsArrowType;
        Contract.Assert(tt != null);
        Contract.Assert(tt.Arity == arity);

        // check WF of receiver and arguments
        CheckWellformed(e.Function, options, locals, builder, etran);
        foreach (Expression arg in e.Args) {
          CheckWellformed(arg, options, locals, builder, etran);
        }

        // check subranges of arguments
        for (int i = 0; i < arity; ++i) {
          CheckSubrange(e.Args[i].tok, etran.TrExpr(e.Args[i]), e.Args[i].Type, tt.Args[i], builder);
        }

        // check parameter availability
        if (etran.UsesOldHeap) {
          Bpl.Expr wh = GetWhereClause(e.Function.tok, etran.TrExpr(e.Function), e.Function.Type, etran, ISALLOC, true);
          if (wh != null) {
            builder.Add(Assert(e.Function.tok, wh, "function must be allocated in the state in which the function is invoked"));
          }
          for (int i = 0; i < e.Args.Count; i++) {
            Expression ee = e.Args[i];
            wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
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
          Cons(etran.HeapExpr,
          Cons(etran.TrExpr(e.Function),
          e.Args.ConvertAll(arg => TrArg(arg)))));

        // Because type inference often gravitates towards inferring non-constrained types, we'll
        // do some digging on our own to see if we can discover a more precise type.
        var fnCore = e.Function;
        while (true) {
          var prevCore = fnCore;
          fnCore = Expression.StripParens(fnCore.Resolved);
          if (object.ReferenceEquals(fnCore, prevCore)) {
            break;  // we've done what we can do
          }
        }
        Type fnCoreType;
        if (fnCore is IdentifierExpr) {
          var v = (IdentifierExpr)fnCore;
          fnCoreType = v.Var.Type;
        } else if (fnCore is MemberSelectExpr) {
          var m = (MemberSelectExpr)fnCore;
          fnCoreType = m.Member is Field ? ((Field)m.Member).Type : ((Function)m.Member).GetMemberType((ArrowTypeDecl)tt.ResolvedClass);
        } else {
          fnCoreType = fnCore.Type;
        }

        if (!fnCoreType.IsArrowTypeWithoutPreconditions) {
          // check precond
          var precond = FunctionCall(e.tok, Requires(arity), Bpl.Type.Bool, args);
          builder.Add(Assert(expr.tok, precond, "possible violation of function precondition"));
        }

        if (options.DoReadsChecks && !fnCoreType.IsArrowTypeWithoutReadEffects) {
          // check read effects
          Type objset = new SetType(true, program.BuiltIns.ObjectQ());
          Expression wrap = new BoogieWrapper(
            FunctionCall(e.tok, Reads(arity), TrType(objset), args),
            objset);
          var reads = new FrameExpression(e.tok, wrap, null);
          CheckFrameSubset(expr.tok, new List<FrameExpression> { reads }, null, null,
            etran, options.AssertSink(this, builder), "insufficient reads clause to invoke function", options.AssertKv);
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Contract.Assert(e.Function != null);  // follows from the fact that expr has been successfully resolved
        if (e.Function is SpecialFunction) {
          CheckWellformedSpecialFunction(e, options, null, null, locals, builder, etran);
        } else {
          // check well-formedness of receiver
          CheckWellformed(e.Receiver, options, locals, builder, etran);
          if (!e.Function.IsStatic && !(e.Receiver is ThisExpr) && !e.Receiver.Type.IsArrowType) {
            CheckNonNull(expr.tok, e.Receiver, builder, etran, options.AssertKv);
          } else if (e.Receiver.Type.IsArrowType) {
            CheckFunctionSelectWF("function specification", builder, etran, e.Receiver, "");
          }
          if (!e.Function.IsStatic && CommonHeapUse && !etran.UsesOldHeap) {
            // the argument can't be assumed to be allocated for the old heap
            Type et = Resolver.SubstType(UserDefinedType.FromTopLevelDecl(e.tok, e.Function.EnclosingClass), e.GetTypeArgumentSubstitutions());
            builder.Add(new Bpl.CommentCmd("assume allocatedness for receiver argument to function"));
            builder.Add(TrAssumeCmd(e.Receiver.tok, MkIsAlloc(etran.TrExpr(e.Receiver), et, etran.HeapExpr)));
          }
          // check well-formedness of the other parameters
          foreach (Expression arg in e.Args) {
            if (!(arg is DefaultValueExpression)) {
              CheckWellformed(arg, options, locals, builder, etran);
            }
          }
          // create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
          Dictionary<IVariable, Expression> substMap = new Dictionary<IVariable, Expression>();
          for (int i = 0; i < e.Function.Formals.Count; i++) {
            Formal p = e.Function.Formals[i];
            // Note, in the following, the "##" makes the variable invisible in BVD.  An alternative would be to communicate
            // to BVD what this variable stands for and display it as such to the user.
            Type et = Resolver.SubstType(p.Type, e.GetTypeArgumentSubstitutions());
            LocalVariable local = new LocalVariable(p.tok, p.tok, "##" + p.Name, et, p.IsGhost);
            local.type = local.OptionalType;  // resolve local here
            IdentifierExpr ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
            ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
            substMap.Add(p, ie);
            locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type))));
            Bpl.IdentifierExpr lhs = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
            Expression ee = e.Args[i];
            CheckSubrange(ee.tok, etran.TrExpr(ee), ee.Type, et, builder);
            Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(p.tok, lhs, CondApplyBox(p.tok, etran.TrExpr(ee), cce.NonNull(ee.Type), et));
            builder.Add(cmd);
            if (CommonHeapUse && !etran.UsesOldHeap) {
              // the argument can't be assumed to be allocated for the old heap
              builder.Add(new Bpl.CommentCmd("assume allocatedness for argument to function"));
              builder.Add(TrAssumeCmd(e.Args[i].tok, MkIsAlloc(lhs, et, etran.HeapExpr)));
            }
          }

          // Check that every parameter is available in the state in which the function is invoked; this means checking that it has
          // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
          // access to expressions of the appropriate type and that are allocated in the current state.  However, if the function is
          // invoked in the 'old' state or if the function invoked is a two-state function with a non-new parameter, then we need to
          // check that its arguments were all available at that time as well.
          if (etran.UsesOldHeap) {
            if (!e.Function.IsStatic) {
              Bpl.Expr wh = GetWhereClause(e.Receiver.tok, etran.TrExpr(e.Receiver), e.Receiver.Type, etran, ISALLOC, true);
              if (wh != null) {
                builder.Add(Assert(e.Receiver.tok, wh, "receiver argument must be allocated in the state in which the function is invoked"));
              }
            }
            for (int i = 0; i < e.Args.Count; i++) {
              Expression ee = e.Args[i];
              Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
              if (wh != null) {
                builder.Add(Assert(ee.tok, wh, "argument must be allocated in the state in which the function is invoked"));
              }
            }
          } else if (e.Function is TwoStateFunction) {
            if (!e.Function.IsStatic) {
              Bpl.Expr wh = GetWhereClause(e.Receiver.tok, etran.TrExpr(e.Receiver), e.Receiver.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
              if (wh != null) {
                builder.Add(Assert(e.Receiver.tok, wh, "receiver argument must be allocated in the two-state function's previous state"));
              }
            }
            Contract.Assert(e.Function.Formals.Count == e.Args.Count);
            for (int i = 0; i < e.Args.Count; i++) {
              var formal = e.Function.Formals[i];
              if (formal.IsOld) {
                Expression ee = e.Args[i];
                Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran.OldAt(e.AtLabel), ISALLOC, true);
                if (wh != null) {
                  builder.Add(Assert(ee.tok, wh, string.Format("argument{0} ('{1}') must be allocated in the two-state function's previous state",
                    e.Args.Count == 1 ? "" : " " + i, formal.Name)));
                }
              }
            }
          }
          // check that the preconditions for the call hold
          foreach (AttributedExpression p in e.Function.Req) {
            Expression precond = Substitute(p.E, e.Receiver, substMap, e.GetTypeArgumentSubstitutions());
            bool splitHappened;  // we don't actually care
            string errorMessage = CustomErrorMessage(p.Attributes);
            foreach (var ss in TrSplitExpr(precond, etran, true, out splitHappened)) {
              if (ss.IsChecked) {
                var tok = new NestedToken(expr.tok, ss.E.tok);
                if (options.AssertKv != null) {
                  // use the given assert attribute only
                  builder.Add(Assert(tok, ss.E, errorMessage ?? "possible violation of function precondition", options.AssertKv));
                } else {
                  builder.Add(AssertNS(tok, ss.E, errorMessage ?? "possible violation of function precondition"));
                }
              }
            }
            if (options.AssertKv == null) {
              // assume only if no given assert attribute is given
              builder.Add(TrAssumeCmd(expr.tok, etran.TrExpr(precond)));
            }
          }
          if (options.DoReadsChecks) {
            // check that the callee reads only what the caller is already allowed to read
            var s = new Substituter(null, new Dictionary<IVariable, Expression>(), e.GetTypeArgumentSubstitutions());
            CheckFrameSubset(expr.tok,
              e.Function.Reads.ConvertAll(s.SubstFrameExpr),
              e.Receiver, substMap, etran, options.AssertSink(this, builder), "insufficient reads clause to invoke function", options.AssertKv);
          }

          Bpl.Expr allowance = null;
          if (codeContext != null && e.CoCall != FunctionCallExpr.CoCallResolution.Yes && !(e.Function is ExtremePredicate)) {
            // check that the decreases measure goes down
            if (ModuleDefinition.InSameSCC(e.Function, codeContext)) {
              if (options.DoOnlyCoarseGrainedTerminationChecks) {
                builder.Add(Assert(expr.tok, Bpl.Expr.False, "default-value expression is not allowed to involve recursive or mutually recursive calls"));
              } else {
                List<Expression> contextDecreases = codeContext.Decreases.Expressions;
                List<Expression> calleeDecreases = e.Function.Decreases.Expressions;
                if (e.Function == options.SelfCallsAllowance) {
                  allowance = Bpl.Expr.True;
                  if (!e.Function.IsStatic) {
                    allowance = BplAnd(allowance, Bpl.Expr.Eq(etran.TrExpr(e.Receiver), new Bpl.IdentifierExpr(e.tok, etran.This)));
                  }
                  for (int i = 0; i < e.Args.Count; i++) {
                    Expression ee = e.Args[i];
                    Formal ff = e.Function.Formals[i];
                    allowance = BplAnd(allowance,
                      Bpl.Expr.Eq(etran.TrExpr(ee),
                        new Bpl.IdentifierExpr(e.tok, ff.AssignUniqueName(currentDeclaration.IdGenerator), TrType(ff.Type))));
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
                    Contract.Assert(false); // unexpected CoCallResolution
                    goto case FunctionCallExpr.CoCallResolution.No; // please the compiler
                }
                if (e.CoCallHint != null) {
                  hint = hint == null ? e.CoCallHint : string.Format("{0}; {1}", hint, e.CoCallHint);
                }
                CheckCallTermination(expr.tok, contextDecreases, calleeDecreases, allowance, e.Receiver, substMap, e.GetTypeArgumentSubstitutions(),
                  etran, etran, builder, codeContext.InferredDecreases, hint);
              }
            }
          }
          // all is okay, so allow this function application access to the function's axiom, except if it was okay because of the self-call allowance.
          Bpl.IdentifierExpr canCallFuncID = new Bpl.IdentifierExpr(expr.tok, e.Function.FullSanitizedName + "#canCall", Bpl.Type.Bool);
          List<Bpl.Expr> args = etran.FunctionInvocationArguments(e, null);
          Bpl.Expr canCallFuncAppl = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(canCallFuncID), args);
          builder.Add(TrAssumeCmd(expr.tok, allowance == null ? canCallFuncAppl : Bpl.Expr.Or(allowance, canCallFuncAppl)));

          var returnType = e.Type.AsDatatype;
          if (returnType != null && returnType.Ctors.Count == 1) {
            var correctConstructor = FunctionCall(e.tok, returnType.Ctors[0].QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e));
            // There is only one constructor, so the value must be been constructed by it; might as well assume that here.
            builder.Add(TrAssumeCmd(expr.tok, correctConstructor));
          }
        }
      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        for (int i = 0; i < dtv.Ctor.Formals.Count; i++) {
          var formal = dtv.Ctor.Formals[i];
          var arg = dtv.Arguments[i];
          if (!(arg is DefaultValueExpression)) {
            CheckWellformed(arg, options, locals, builder, etran);
          }
          // Cannot use the datatype's formals, so we substitute the inferred type args:
          var su = new Dictionary<TypeParameter, Type>();
          foreach (var p in LinqExtender.Zip(dtv.Ctor.EnclosingDatatype.TypeArgs, dtv.InferredTypeArgs)) {
            su[p.Item1] = p.Item2;
          }
          Type ty = Resolver.SubstType(formal.Type, su);
          CheckSubrange(arg.tok, etran.TrExpr(arg), arg.Type, ty, builder);
        }
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        CheckWellformed(e.N, options, locals, builder, etran);
        builder.Add(Assert(e.N.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.N)),
          "sequence size might be negative"));

        CheckWellformed(e.Initializer, options, locals, builder, etran);
        var eType = e.Type.AsSeqType.Arg;
        CheckElementInit(e.tok, false, new List<Expression>() {e.N}, eType, e.Initializer, null, builder, etran, options);
      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // Anything read inside the 'old' expressions depends only on the old heap, which isn't included in the
        // frame axiom.  In other words, 'old' expressions have no dependencies on the current heap.  Therefore,
        // we turn off any reads checks for "e.E".
        CheckWellformed(e.E, new WFOptions(options), locals, builder, etran.OldAt(e.AtLabel));
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        foreach (var fe in e.Frame) {
          CheckWellformed(fe.E, options, locals, builder, etran);
        }
      } else if (expr is UnaryExpr) {
        UnaryExpr e = (UnaryExpr)expr;
        CheckWellformed(e.E, options, locals, builder, etran);
        if (e is ConversionExpr) {
          var ee = (ConversionExpr)e;
          CheckResultToBeInType(expr.tok, ee.E, ee.ToType, locals, builder, etran);
        }
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        CheckWellformed(e.E0, options, locals, builder, etran);
        switch (e.ResolvedOp) {
          case BinaryExpr.ResolvedOpcode.And:
          case BinaryExpr.ResolvedOpcode.Imp: {
              BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.E0), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Or: {
              BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
              CheckWellformed(e.E1, options, locals, b, etran);
              builder.Add(new Bpl.IfCmd(expr.tok, Bpl.Expr.Not(etran.TrExpr(e.E0)), b.Collect(expr.tok), null, null));
            }
            break;
          case BinaryExpr.ResolvedOpcode.Add:
          case BinaryExpr.ResolvedOpcode.Sub:
          case BinaryExpr.ResolvedOpcode.Mul:
            CheckWellformed(e.E1, options, locals, builder, etran);
            if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub && e.E0.Type.IsBigOrdinalType) {
              var rhsIsNat = FunctionCall(expr.tok, "ORD#IsNat", Bpl.Type.Bool, etran.TrExpr(e.E1));
              builder.Add(Assert(expr.tok, rhsIsNat, "RHS of ORDINAL subtraction must be a natural number, but the given RHS might be larger"));
              var offset0 = FunctionCall(expr.tok, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E0));
              var offset1 = FunctionCall(expr.tok, "ORD#Offset", Bpl.Type.Int, etran.TrExpr(e.E1));
              builder.Add(Assert(expr.tok, Bpl.Expr.Le(offset1, offset0), "ORDINAL subtraction might underflow a limit ordinal (that is, RHS might be too large)"));
            } else if (e.Type.IsCharType) {
              var e0 = FunctionCall(expr.tok, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E0));
              var e1 = FunctionCall(expr.tok, "char#ToInt", Bpl.Type.Int, etran.TrExpr(e.E1));
              if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.Add) {
                builder.Add(Assert(expr.tok, Bpl.Expr.Lt(Bpl.Expr.Binary(BinaryOperator.Opcode.Add, e0, e1), Bpl.Expr.Literal(65536)), "char addition might overflow"));
              } else {
                Contract.Assert(e.ResolvedOp == BinaryExpr.ResolvedOpcode.Sub);  // .Mul is not supported for char
                builder.Add(Assert(expr.tok, Bpl.Expr.Le(e1, e0), "char subtraction might underflow"));
              }
            }
            CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
            break;
          case BinaryExpr.ResolvedOpcode.Div:
          case BinaryExpr.ResolvedOpcode.Mod: {
              Bpl.Expr zero;
              if (e.E1.Type.IsBitVectorType) {
                zero = BplBvLiteralExpr(e.tok, BaseTypes.BigNum.ZERO, e.E1.Type.AsBitVectorType);
              } else if (e.E1.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
                zero = Bpl.Expr.Literal(BaseTypes.BigDec.ZERO);
              } else {
                zero = Bpl.Expr.Literal(0);
              }
              CheckWellformed(e.E1, options, locals, builder, etran);
              builder.Add(Assert(expr.tok, Bpl.Expr.Neq(etran.TrExpr(e.E1), zero), "possible division by zero", options.AssertKv));
              CheckResultToBeInType(expr.tok, expr, expr.Type, locals, builder, etran);
            }
            break;
          case BinaryExpr.ResolvedOpcode.LeftShift:
          case BinaryExpr.ResolvedOpcode.RightShift: {
              CheckWellformed(e.E1, options, locals, builder, etran);
              var w = e.Type.AsBitVectorType.Width;
              var upperMsg = string.Format("shift amount must not exceed the width of the result ({0})", w);
              if (e.E1.Type.IsBitVectorType) {
                // Known to be non-negative, so we don't need to check lower bound.
                // Check upper bound, that is, check "E1 <= w"
                var e1Width = e.E1.Type.AsBitVectorType.Width;
                if (w < (BigInteger.One << e1Width)) {
                  // w is a number that can be represented in the e.E1.Type, so do the comparison in that bitvector type.
                  var bound = BplBvLiteralExpr(e.tok, BaseTypes.BigNum.FromInt(w), e1Width);
                  var cmp = etran.TrToFunctionCall(expr.tok, "le_bv" + e1Width, Bpl.Type.Bool, etran.TrExpr(e.E1), bound, false);
                  builder.Add(Assert(expr.tok, cmp, upperMsg, options.AssertKv));
                } else {
                  // In the previous branch, we had:
                  //     w < 2^e1Width               (*)
                  // From the type of E1, we have:
                  //     E1 < 2^e1Width
                  // In this branch, (*) does not hold, so we therefore have the following:
                  //     E1 < 2^e1Width <= w
                  // In other words, the condition
                  //     E1 <= w
                  // already holds, so there is no reason to check it.
                }
              } else {
                builder.Add(Assert(expr.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E1)), "shift amount must be non-negative", options.AssertKv));
                builder.Add(Assert(expr.tok, Bpl.Expr.Le(etran.TrExpr(e.E1), Bpl.Expr.Literal(w)), upperMsg, options.AssertKv));
              }
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
            if (e.E0.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
              builder.Add(Assert(expr.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(e.E0)), "prefix-equality limit must be at least 0", options.AssertKv));
            }
            break;
          default:
            Contract.Assert(false);  // unexpected ternary expression
            break;
        }

      } else if (expr is LetExpr) {
        result = CheckWellformedLetExprWithResult((LetExpr)expr, options, result, resultType, locals, builder, etran, true);

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var q = e as QuantifierExpr;
        var lam = e as LambdaExpr;
        var mc = e as MapComprehension;
        if (mc != null && !mc.IsGeneralMapComprehension) {
          mc = null;  // mc will be non-null when "e" is a general map comprehension
        }

        // This is a WF check, so we look at the original quantifier, not the split one.
        // This ensures that cases like forall x :: x != null && f(x.a) do not fail to verify.

        var typeMap = new Dictionary<TypeParameter, Type>();
        var copies = new List<TypeParameter>();
        if (q != null) {
          copies = Map(q.TypeArgs, tp => q.Refresh(tp, CurrentIdGenerator));
          typeMap = Util.Dict(q.TypeArgs, Map(copies, tp => (Type)new UserDefinedType(tp)));
        }
        locals.AddRange(Map(copies,
          tp => new Bpl.LocalVariable(tp.tok, new TypedIdent(tp.tok, nameTypeParam(tp), predef.Ty))));

        builder.Add(new Bpl.CommentCmd("Begin Comprehension WF check"));
        BplIfIf(e.tok, lam != null, null, builder, nextBuilder => {
          var comprehensionEtran = etran;
          if (lam != null) {
            // Havoc heap
            locals.Add(BplLocalVar(CurrentIdGenerator.FreshId((etran.UsesOldHeap ? "$Heap_at_" : "") + "$lambdaHeap#"), predef.HeapType, out var lambdaHeap));
            comprehensionEtran = new ExpressionTranslator(comprehensionEtran, lambdaHeap);
            nextBuilder.Add(new HavocCmd(expr.tok, Singleton((Bpl.IdentifierExpr)comprehensionEtran.HeapExpr)));
            nextBuilder.Add(new AssumeCmd(expr.tok, FunctionCall(expr.tok, BuiltinFunction.IsGoodHeap, null, comprehensionEtran.HeapExpr)));
            nextBuilder.Add(new AssumeCmd(expr.tok, HeapSameOrSucc(etran.HeapExpr, comprehensionEtran.HeapExpr)));
          }

          var substMap = SetupBoundVarsAsLocals(e.BoundVars, out var typeAntecedents, nextBuilder, locals, comprehensionEtran, typeMap);
          BplIfIf(e.tok, true, typeAntecedents, nextBuilder, newBuilder => {
            var s = new Substituter(null, substMap, typeMap);
            var body = Substitute(e.Term, null, substMap, typeMap);
            var bodyLeft = mc != null ? Substitute(mc.TermLeft, null, substMap, typeMap) : null;
            var substMapPrime = mc != null ? SetupBoundVarsAsLocals(e.BoundVars, newBuilder, locals, comprehensionEtran, typeMap, "#prime") : null;
            var bodyLeftPrime = mc != null ? Substitute(mc.TermLeft, null, substMapPrime, typeMap) : null;
            var bodyPrime = mc != null ? Substitute(e.Term, null, substMapPrime, typeMap) : null;
            List<FrameExpression> reads = null;

            var newOptions = options;
            if (lam != null) {
              // Set up a new frame
              var frameName = CurrentIdGenerator.FreshId("$_Frame#l");
              reads = lam.Reads.ConvertAll(s.SubstFrameExpr);
              DefineFrame(e.tok, reads, newBuilder, locals, frameName, comprehensionEtran);
              comprehensionEtran = new ExpressionTranslator(comprehensionEtran, frameName);

              // Check frame WF and that it read covers itself
              newOptions = new WFOptions(options.SelfCallsAllowance, true /* check reads clauses */, true /* delay reads checks */);
              CheckFrameWellFormed(newOptions, reads, locals, newBuilder, comprehensionEtran);
              // new options now contains the delayed reads checks
              newOptions.ProcessSavedReadsChecks(locals, builder, newBuilder);

              // continue doing reads checks, but don't delay them
              newOptions = new WFOptions(options.SelfCallsAllowance, true, false);
            }

            // check requires/range
            Bpl.Expr guard = null;
            if (e.Range != null) {
              var range = Substitute(e.Range, null, substMap);
              CheckWellformed(range, newOptions, locals, newBuilder, comprehensionEtran);
              guard = comprehensionEtran.TrExpr(range);
            }

            if (mc != null) {
              Contract.Assert(bodyLeft != null);
              BplIfIf(e.tok, guard != null, guard, newBuilder, b => { CheckWellformed(bodyLeft, newOptions, locals, b, comprehensionEtran); });
            }
            BplIfIf(e.tok, guard != null, guard, newBuilder, b => {
              Bpl.Expr resultIe = null;
              Type rangeType = null;
              if (lam != null) {
                var resultName = CurrentIdGenerator.FreshId("lambdaResult#");
                var resultVar = new Bpl.LocalVariable(body.tok, new Bpl.TypedIdent(body.tok, resultName, TrType(body.Type)));
                locals.Add(resultVar);
                resultIe = new Bpl.IdentifierExpr(body.tok, resultVar);
                rangeType = lam.Type.AsArrowType.Result;
              }
              CheckWellformedWithResult(body, newOptions, resultIe, rangeType, locals, b, comprehensionEtran);
            });

            if (mc != null) {
              Contract.Assert(substMapPrime != null);
              Contract.Assert(bodyLeftPrime != null);
              Contract.Assert(bodyPrime != null);
              Bpl.Expr guardPrime = null;
              if (guard != null) {
                Contract.Assert(e.Range != null);
                var rangePrime = Substitute(e.Range, null, substMapPrime);
                guardPrime = comprehensionEtran.TrExpr(rangePrime);
              }
              BplIfIf(e.tok, guard != null, BplAnd(guard, guardPrime), newBuilder, b => {
                var different = BplOr(
                  Bpl.Expr.Neq(comprehensionEtran.TrExpr(bodyLeft), comprehensionEtran.TrExpr(bodyLeftPrime)),
                  Bpl.Expr.Eq(comprehensionEtran.TrExpr(body), comprehensionEtran.TrExpr(bodyPrime)));
                b.Add(Assert(mc.TermLeft.tok, different, "key expressions may be referring to the same value"));
              });
            }
          });

          if (lam != null) {
            // assume false (heap was havoced inside an if)
            Contract.Assert(nextBuilder != builder);
            nextBuilder.Add(new AssumeCmd(e.tok, Bpl.Expr.False));
          }
        });
        builder.Add(new Bpl.CommentCmd("End Comprehension WF check"));

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        TrStmt(e.S, builder, locals, etran);
        CheckWellformedWithResult(e.E, options, result, resultType, locals, builder, etran);
        result = null;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        CheckWellformed(e.Test, options, locals, builder, etran);
        var bThen = new BoogieStmtListBuilder(this);
        var bElse = new BoogieStmtListBuilder(this);
        if (e.IsBindingGuard) {
          // if it is BindingGuard, e.Thn is a let-such-that created from the BindingGuard.
          // We don't need to do well-formedness check on the Rhs of the LetExpr since it
          // has already been checked in e.Test
          var letExpr = (LetExpr)e.Thn;
          Contract.Assert(letExpr != null);
          CheckWellformedLetExprWithResult(letExpr, options, result, resultType, locals, bThen, etran, false);
        } else {
          CheckWellformedWithResult(e.Thn, options, result, resultType, locals, bThen, etran);
        }
        CheckWellformedWithResult(e.Els, options, result, resultType, locals, bElse, etran);
        builder.Add(new Bpl.IfCmd(expr.tok, etran.TrExpr(e.Test), bThen.Collect(expr.tok), null, bElse.Collect(expr.tok)));
        result = null;
      } else if (expr is MatchExpr) {
        MatchExpr me = (MatchExpr)expr;
        CheckWellformed(me.Source, options, locals, builder, etran);
        Bpl.Expr src = etran.TrExpr(me.Source);
        Bpl.IfCmd ifCmd = null;
        BoogieStmtListBuilder elsBldr = new BoogieStmtListBuilder(this);
        elsBldr.Add(TrAssumeCmd(expr.tok, Bpl.Expr.False));
        StmtList els = elsBldr.Collect(expr.tok);
        foreach (var missingCtor in me.MissingCases) {
          // havoc all bound variables
          var b = new BoogieStmtListBuilder(this);
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(me.tok, missingCtor, etran, newLocals, b);
          locals.AddRange(newLocals);

          if (newLocals.Count != 0) {
            List<Bpl.IdentifierExpr> havocIds = new List<Bpl.IdentifierExpr>();
            foreach (Variable local in newLocals) {
              havocIds.Add(new Bpl.IdentifierExpr(local.tok, local));
            }
            builder.Add(new Bpl.HavocCmd(me.tok, havocIds));
          }

          String missingStr = me.Context.FillHole(new IdCtx(new KeyValuePair<string, DatatypeCtor>(missingCtor.Name, missingCtor))).AbstractAllHoles().ToString();
          b.Add(Assert(me.tok, Bpl.Expr.False, "missing case in match expression: " + missingStr));

          Bpl.Expr guard = Bpl.Expr.Eq(src, r);
          ifCmd = new Bpl.IfCmd(me.tok, guard, b.Collect(me.tok), ifCmd, els);
          els = null;
        }
        for (int i = me.Cases.Count; 0 <= --i;) {
          MatchCaseExpr mc = me.Cases[i];
          BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
          Bpl.Expr ct = CtorInvocation(mc, me.Source.Type, etran, locals, b, NOALLOC, false);
          // generate:  if (src == ctor(args)) { assume args-is-well-typed; mc.Body is well-formed; assume Result == TrExpr(case); } else ...
          CheckWellformedWithResult(mc.Body, options, result, resultType, locals, b, etran);
          ifCmd = new Bpl.IfCmd(mc.tok, Bpl.Expr.Eq(src, ct), b.Collect(mc.tok), ifCmd, els);
          els = null;
        }
        builder.Add(ifCmd);
        result = null;

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        // check that source expression is created from one of the legal source constructors, then proceed according to the .ResolvedExpression
        var correctConstructor = BplOr(e.LegalSourceConstructors.ConvertAll(
          ctor => FunctionCall(e.tok, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, etran.TrExpr(e.Root))));
        if (e.LegalSourceConstructors.Count == e.Type.AsDatatype.Ctors.Count) {
          // Every constructor has this destructor; no need to check anything
        } else {
          builder.Add(Assert(expr.tok, correctConstructor,
            string.Format("source of datatype update must be constructed by {0}", DatatypeDestructor.PrintableCtorNameList(e.LegalSourceConstructors, "or"))));
        }

        CheckWellformedWithResult(e.ResolvedExpression, options, result, resultType, locals, builder, etran);
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
        CheckSubrange(expr.tok, bResult, expr.Type, resultType, builder);
        builder.Add(TrAssumeCmd(expr.tok, Bpl.Expr.Eq(result, bResult)));
        builder.Add(TrAssumeCmd(expr.tok, CanCallAssumption(expr, etran)));
        builder.Add(new CommentCmd("CheckWellformedWithResult: any expression"));
        if (AlwaysUseHeap) {
          builder.Add(TrAssumeCmd(expr.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
        }
        builder.Add(TrAssumeCmd(expr.tok, MkIs(result, resultType)));
      }
    }

    void CheckWellformedSpecialFunction(FunctionCallExpr expr, WFOptions options, Bpl.Expr result, Type resultType, List<Bpl.Variable> locals,
                               BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(expr.Function is SpecialFunction);

      string name = expr.Function.Name;
      CheckWellformed(expr.Receiver, options, locals, builder, etran);
      if (name == "RotateLeft" || name == "RotateRight") {
        var w = expr.Type.AsBitVectorType.Width;
        Expression arg = expr.Args[0];
        builder.Add(Assert(expr.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(arg)), "shift amount must be non-negative", options.AssertKv));
        var upperMsg = string.Format("shift amount must not exceed the width of the result ({0})", w);
        builder.Add(Assert(expr.tok, Bpl.Expr.Le(etran.TrExpr(arg), Bpl.Expr.Literal(w)), upperMsg, options.AssertKv));
      }
    }

    Bpl.Expr CheckWellformedLetExprWithResult(LetExpr e, WFOptions options, Bpl.Expr result, Type resultType, List<Bpl.Variable> locals,
                                BoogieStmtListBuilder builder, ExpressionTranslator etran, bool checkRhs) {
      if (e.Exact) {
        var uniqueSuffix = "#Z" + defaultIdGenerator.FreshNumericId("#Z");
        var substMap = SetupBoundVarsAsLocals(e.BoundVars.ToList<BoundVar>(), builder, locals, etran, null, "#Z");
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("let#");
        for (int i = 0; i < e.LHSs.Count; i++) {
          var pat = e.LHSs[i];
          var rhs = e.RHSs[i];
          var nm = varNameGen.FreshId(string.Format("#{0}#", i));
          var r = new Bpl.LocalVariable(pat.tok, new Bpl.TypedIdent(pat.tok, nm, TrType(rhs.Type)));
          locals.Add(r);
          var rIe = new Bpl.IdentifierExpr(rhs.tok, r);
          CheckWellformedWithResult(e.RHSs[i], options, rIe, pat.Expr.Type, locals, builder, etran);
          CheckCasePatternShape(pat, rIe, rhs.tok, pat.Expr.Type, builder);
          builder.Add(TrAssumeCmd(pat.tok, Bpl.Expr.Eq(etran.TrExpr(Substitute(pat.Expr, null, substMap)), rIe)));
        }
        CheckWellformedWithResult(Substitute(e.Body, null, substMap), options, result, resultType, locals, builder, etran);
        result = null;

      } else {
        // CheckWellformed(var b :| RHS(b); Body(b)) =
        //   var b;
        //   if (typeAntecedent(b)) {
        //     CheckWellformed(RHS(b));
        //   }
        //   assert (exists b' :: typeAntecedent' && RHS(b'));
        //   assume typeAntecedent(b);
        //   assume RHS(b);
        //   CheckWellformed(Body(b));
        //   If non-ghost:  var b' where typeAntecedent; assume RHS(b'); assert Body(b) == Body(b');
        //   assume CanCall
        Contract.Assert(e.RHSs.Count == 1);  // this is true of all successfully resolved let-such-that expressions
        var lhsVars = e.BoundVars.ToList<BoundVar>();
        var substMap = SetupBoundVarsAsLocals(lhsVars, out var typeAntecedent, builder, locals, etran);
        var rhs = Substitute(e.RHSs[0], null, substMap);
        if (checkRhs) {
          var wellFormednessBuilder = new BoogieStmtListBuilder(this);
          CheckWellformed(rhs, options, locals, wellFormednessBuilder, etran);
          var ifCmd = new Bpl.IfCmd(e.tok, typeAntecedent, wellFormednessBuilder.Collect(e.tok), null, null);
          builder.Add(ifCmd);

          var bounds = lhsVars.ConvertAll(_ => (ComprehensionExpr.BoundedPool)new ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool());  // indicate "no alloc" (is this what we want?)
          GenerateAndCheckGuesses(e.tok, lhsVars, bounds, e.RHSs[0], TrTrigger(etran, e.Attributes, e.tok), builder, etran);
        }
        // assume typeAntecedent(b);
        builder.Add(TrAssumeCmd(e.tok, typeAntecedent));
        // assume RHS(b);
        builder.Add(TrAssumeCmd(e.tok, etran.TrExpr(rhs)));
        var letBody = Substitute(e.Body, null, substMap);
        CheckWellformed(letBody, options, locals, builder, etran);
        if (e.Constraint_Bounds != null) {
          var substMap_prime = SetupBoundVarsAsLocals(lhsVars, builder, locals, etran);
          var nonGhostMap_prime = new Dictionary<IVariable, Expression>();
          foreach (BoundVar bv in lhsVars) {
            nonGhostMap_prime.Add(bv, bv.IsGhost ? substMap[bv] : substMap_prime[bv]);
          }
          var rhs_prime = Substitute(e.RHSs[0], null, nonGhostMap_prime);
          var letBody_prime = Substitute(e.Body, null, nonGhostMap_prime);
          builder.Add(TrAssumeCmd(e.tok, CanCallAssumption(rhs_prime, etran)));
          builder.Add(TrAssumeCmd(e.tok, etran.TrExpr(rhs_prime)));
          builder.Add(TrAssumeCmd(e.tok, CanCallAssumption(letBody_prime, etran)));
          var eq = Expression.CreateEq(letBody, letBody_prime, e.Body.Type);
          builder.Add(Assert(e.tok, etran.TrExpr(eq), "to be compilable, the value of a let-such-that expression must be uniquely determined"));
        }
        // assume $let$canCall(g);
        LetDesugaring(e);  // call LetDesugaring to prepare the desugaring and populate letSuchThatExprInfo with something for e
        var info = letSuchThatExprInfo[e];
        builder.Add(new Bpl.AssumeCmd(e.tok, info.CanCallFunctionCall(this, etran)));
        // If we are supposed to assume "result" to equal this expression, then use the body of the let-such-that, not the generated $let#... function
        if (result != null) {
          Contract.Assert(resultType != null);
          var bResult = etran.TrExpr(letBody);
          CheckSubrange(letBody.tok, bResult, letBody.Type, resultType, builder);
          builder.Add(TrAssumeCmd(letBody.tok, Bpl.Expr.Eq(result, bResult)));
          builder.Add(TrAssumeCmd(letBody.tok, CanCallAssumption(letBody, etran)));
          builder.Add(new CommentCmd("CheckWellformedWithResult: Let expression"));
          if (AlwaysUseHeap) {
            builder.Add(TrAssumeCmd(letBody.tok, MkIsAlloc(result, resultType, etran.HeapExpr)));
          }
          builder.Add(TrAssumeCmd(letBody.tok, MkIs(result, resultType)));
          result = null;
        }
      }
      return result;
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
      } else if (fromType.IsRefType) {
        return r;
      } else {
        Contract.Assert(false, $"No translation implemented from {fromType} to {toType}");
      }
      return r;
    }

    private Bpl.Expr IntToBV(IToken tok, Bpl.Expr r, Type toType) {
      var toWidth = toType.AsBitVectorType.Width;
      if (RemoveLit(r) is Bpl.LiteralExpr) {
        Bpl.LiteralExpr e = (Bpl.LiteralExpr) RemoveLit(r);
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
      System.Action PutSourceIntoLocal = () => {
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
      };

      Contract.Assert(expr.Type.IsRefType == toType.IsRefType);
      if (toType.IsRefType) {
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
        builder.Add(Assert(tok, e, $"{errorMsgPrefix}the real-based number must be an integer (if you want truncation, apply .Floor to the real-based number)"));
      }

      if (expr.Type.IsBigOrdinalType && !toType.IsBigOrdinalType) {
        PutSourceIntoLocal();
        Bpl.Expr boundsCheck = FunctionCall(tok, "ORD#IsNat", Bpl.Type.Bool, o);
        builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}value to be converted might be bigger than every natural number"));
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
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}value to be converted might not fit in {toType}"));
        }
      }

      if (toType.IsCharType) {
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          PutSourceIntoLocal();
          Bpl.Expr boundsCheck =
            Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), o), Bpl.Expr.Lt(o, Bpl.Expr.Literal(65536)));
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}value to be converted might not fit in {toType}"));
        } else if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
          var boundsCheck =
            Bpl.Expr.And(Bpl.Expr.Le(Bpl.Expr.Literal(0), oi), Bpl.Expr.Lt(oi, Bpl.Expr.Literal(65536)));
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}real value to be converted might not fit in {toType}"));
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
            builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}bit-vector value to be converted might not fit in {toType}"));
          }
        } else if (expr.Type.IsBigOrdinalType) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, "ORD#Offset", Bpl.Type.Int, o);
          int toWidth = 16;
          var toBound = BaseTypes.BigNum.FromBigInt(BigInteger.One << toWidth); // 1 << toWidth
          var bound = Bpl.Expr.Literal(toBound);
          var boundsCheck = Bpl.Expr.Lt(oi, bound);
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}ORDINAL value to be converted might not fit in {toType}"));
        }
      } else if (toType.IsBigOrdinalType) {
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
          PutSourceIntoLocal();
          Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), o);
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}a negative integer cannot be converted to an {toType}"));
        }
        if (expr.Type.IsNumericBased(Type.NumericPersuasion.Real)) {
          PutSourceIntoLocal();
          var oi = FunctionCall(tok, BuiltinFunction.RealToInt, null, o);
          Bpl.Expr boundsCheck = Bpl.Expr.Le(Bpl.Expr.Literal(0), oi);
          builder.Add(Assert(tok, boundsCheck, $"{errorMsgPrefix}a negative real cannot be converted to an {toType}"));
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
      } else {
        baseType = ((NewtypeDecl)rdt).BaseType;
        kind = "newtype";
      }
      if (baseType.AsRedirectingType != null) {
        CheckResultToBeInType_Aux(tok, expr, baseType, builder, etran, errorMsgPrefix);
      }
      // Check any constraint defined in 'dd'
      if (rdt.Var != null) {
        // TODO: use TrSplitExpr
        var substMap = new Dictionary<IVariable, Expression>();
        substMap.Add(rdt.Var, expr);
        var typeMap = Resolver.TypeSubstitutionMap(rdt.TypeArgs, udt.TypeArgs);
        var constraint = etran.TrExpr(Substitute(rdt.Constraint, null, substMap, typeMap));
        builder.Add(Assert(tok, constraint, $"{errorMsgPrefix}result of operation might violate {kind} constraint for '{rdt.Name}'"));
      }
    }


    void CheckFunctionSelectWF(string what, BoogieStmtListBuilder builder, ExpressionTranslator etran, Expression e, string hint) {
      if (e is MemberSelectExpr sel && sel.Member is Function fn) {
        Bpl.Expr assertion = !InVerificationScope(fn) ? Bpl.Expr.True : Bpl.Expr.Not(etran.HeightContext(fn));
        builder.Add(Assert(e.tok, assertion,
          "cannot use " + what + " in recursive setting." + hint));
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
        var formals = MkTyParamFormals(GetTypeParams(f), false);
        var tyargs = new List<Bpl.Expr>();
        foreach (var fm in f.Formals) {
          tyargs.Add(TypeToTy(fm.Type));
        }
        tyargs.Add(TypeToTy(f.ResultType));
        if (f.IsFuelAware()) {
          Bpl.Expr ly; vars.Add(BplBoundVar("$ly", predef.LayerType, out ly)); args.Add(ly);
          formals.Add(BplFormalVar(null, predef.LayerType, true));
          AddLayerSynonymAxiom(f, true);
        }

        Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocSelf = x => x;
        Func<List<Bpl.Expr>, List<Bpl.Expr>> SnocPrevH = x => x;
        Expression selfExpr;
        Dictionary<IVariable, Expression> rhs_dict = new Dictionary<IVariable, Expression>();
        if (f is TwoStateFunction) {
          // also add previous-heap to the list of fixed arguments of the handle
          var prevH = BplBoundVar("$prevHeap", predef.HeapType, vars);
          formals.Add(BplFormalVar(null, predef.HeapType, true));
          SnocPrevH = xs => Snoc(xs, prevH);
        }
        if (f.IsStatic) {
          selfExpr = null;
        } else {
          var selfTy = TrType(UserDefinedType.FromTopLevelDecl(f.tok, f.EnclosingClass));
          var self = BplBoundVar("$self", selfTy, vars);
          formals.Add(BplFormalVar(null, selfTy, true));
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
          var lhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
          var args_h = AlwaysUseHeap || f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
          var rhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), rhs_args));
          var rhs_boxed = BoxIfUnboxed(rhs, f.ResultType);

          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs_boxed))));
        }

        {
          // Requires(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
          //   = F#Requires(Ty1, .., TyN, Layer, Heap, self, [Unbox] arg1, .., [Unbox] argN)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          var lhs = FunctionCall(f.tok, Requires(arity), Bpl.Type.Bool, Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));
          Bpl.Expr rhs;
          if (f.EnclosingClass is ArrowTypeDecl) {
            // In case this is the /requires/ or /reads/ function, then there is no precondition
            rhs = Bpl.Expr.True;
          } else {
            var args_h = AlwaysUseHeap || f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
            rhs = FunctionCall(f.tok, RequiresName(f), Bpl.Type.Bool, Concat(SnocSelf(args_h), rhs_args));
          }

          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Concat(vars, bvars), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }

        {
          // Reads(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, arg1, ..., argN)
          //   =  $Frame_F(args...)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          Bpl.Expr lhs_inner = FunctionCall(f.tok, Reads(arity), TrType(new SetType(true, program.BuiltIns.ObjectQ())), Concat(tyargs, Cons(h, Cons(fhandle, lhs_args))));

          Bpl.Expr bx; var bxVar = BplBoundVar("$bx", predef.BoxType, out bx);
          Bpl.Expr unboxBx = FunctionCall(f.tok, BuiltinFunction.Unbox, predef.RefType, bx);
          Bpl.Expr lhs = Bpl.Expr.SelectTok(f.tok, lhs_inner, bx);

          var et = new ExpressionTranslator(this, predef, h);
          var rhs = InRWClause_Aux(f.tok, unboxBx, bx, null, f.Reads, false, et, selfExpr, rhs_dict);

          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Cons(bxVar, Concat(vars, bvars)), BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs))));
        }

        {
          // F(Ty1, .., TyN, Layer, Heap, self, arg1, .., argN)
          // = [Unbox]Apply1(Ty.., F#Handle( Ty1, ..., TyN, Layer, self), Heap, [Box]arg1, ..., [Box]argN)

          var fhandle = FunctionCall(f.tok, name, predef.HandleType, SnocSelf(SnocPrevH(args)));
          var args_h = AlwaysUseHeap || f.ReadsHeap ? Snoc(SnocPrevH(args), h) : args;
          var lhs = FunctionCall(f.tok, f.FullSanitizedName, TrType(f.ResultType), Concat(SnocSelf(args_h), func_args));
          var rhs = FunctionCall(f.tok, Apply(arity), TrType(f.ResultType), Concat(tyargs, Cons(h, Cons(fhandle, boxed_func_args))));
          var rhs_unboxed = UnboxIfBoxed(rhs, f.ResultType);
          var tr = BplTriggerHeap(this, f.tok, lhs, AlwaysUseHeap || f.ReadsHeap ? null : h);

          sink.AddTopLevelDeclaration(new Axiom(f.tok,
            BplForall(Concat(vars, func_vars), tr, Bpl.Expr.Eq(lhs, rhs_unboxed))));
        }
      }
      return name;
    }

    private Expr NewOneHeapExpr(IToken tok) {
      return new Bpl.IdentifierExpr(tok, "$OneHeap", predef.HeapType);
    }

    private void AddArrowTypeAxioms(ArrowTypeDecl ad) {
      Contract.Requires(ad != null);
      var arity = ad.Arity;
      var tok = ad.tok;

      // [Heap, Box, ..., Box]
      var map_args = Cons(predef.HeapType, Map(Enumerable.Range(0, arity), i => predef.BoxType));
      // [Heap, Box, ..., Box] Box
      var apply_ty = new Bpl.MapType(tok, new List<Bpl.TypeVariable>(), map_args, predef.BoxType);
      // [Heap, Box, ..., Box] Bool
      var requires_ty = new Bpl.MapType(tok, new List<Bpl.TypeVariable>(), map_args, Bpl.Type.Bool);
      // Set Box
      var objset_ty = TrType(new SetType(true, program.BuiltIns.ObjectQ()));
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
        sink.AddTopLevelDeclaration(new Bpl.Function(Token.NoToken, Handle(arity), arg, res));
      }

      Action<string, Bpl.Type> SelectorFunction = (s, t) => {
        var args = new List<Bpl.Variable>();
        MapM(Enumerable.Range(0, arity + 1), i => args.Add(BplFormalVar(null, predef.Ty, true)));
        args.Add(BplFormalVar(null, predef.HeapType, true));
        args.Add(BplFormalVar(null, predef.HandleType, true));
        MapM(Enumerable.Range(0, arity), i => args.Add(BplFormalVar(null, predef.BoxType, true)));
        sink.AddTopLevelDeclaration(new Bpl.Function(Token.NoToken, s, args, BplFormalVar(null, t, false)));
      };

      // function ApplyN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Box
      if (arity != 1) {  // Apply1 is already declared in DafnyPrelude.bpl
        SelectorFunction(Apply(arity), predef.BoxType);
      }
      // function RequiresN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Bool
      SelectorFunction(Requires(arity), Bpl.Type.Bool);
      // function ReadsN(Ty, ... Ty, HandleType, Heap, Box, ..., Box) : Set Box
      SelectorFunction(Reads(arity), objset_ty);

      {
        // forall t1, .., tN+1 : Ty, p: [Heap, Box, ..., Box] Box, heap : Heap, b1, ..., bN : Box
        //      :: ApplyN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == h[heap, b1, ..., bN]
        //      :: RequiresN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) <== r[heap, b1, ..., bN]
        //      :: ReadsN(t1, .. tN+1, heap, HandleN(h, r, rd), b1, ..., bN) == rd[heap, b1, ..., bN]
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

          var lhsargs = Concat(types, Cons(heap, Cons(FunctionCall(tok, Handle(arity), predef.HandleType, handleargs), boxes)));
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
            lhs = Bpl.Expr.SelectTok(tok, lhs, bx);
            rhs = Bpl.Expr.SelectTok(tok, rhs, bx);
            // op = Bpl.Expr.Imp;
          }
          if (selectorVar == "r") {
            op = (u, v) => Bpl.Expr.Imp(v, u);
          }
          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvars, BplTrigger(lhs), op(lhs, rhs))));
        };
        SelectorSemantics(Apply(arity), predef.BoxType, "h", apply_ty, Requires(arity), requires_ty);
        SelectorSemantics(Requires(arity), Bpl.Type.Bool, "r", requires_ty, null, null);
        SelectorSemantics(Reads(arity), objset_ty, "rd", reads_ty, null, null);

        // function {:inline true}
        //   FuncN._requires#canCall(G...G G: Ty, H:Heap, f:Handle, x ... x :Box): bool
        //   { true }
        // + similar for Reads
        Action<string, Function> UserSelectorFunction = (fname, f) => {
          var formals = new List<Bpl.Variable>();
          var rhsargs = new List<Bpl.Expr>();

          MapM(Enumerable.Range(0, arity + 1), i => rhsargs.Add(BplFormalVar("t" + i, predef.Ty, true, formals)));

          var heap = BplFormalVar("heap", predef.HeapType, true, formals);
          rhsargs.Add(heap);
          rhsargs.Add(BplFormalVar("f", predef.HandleType, true, formals));

          MapM(Enumerable.Range(0, arity), i => rhsargs.Add(BplFormalVar("bx" + i, predef.BoxType, true, formals)));

          sink.AddTopLevelDeclaration(
            new Bpl.Function(f.tok, f.FullSanitizedName + "#canCall", new List<TypeVariable>(), formals,
              BplFormalVar(null, Bpl.Type.Bool, false), null,
              InlineAttribute(f.tok)) {
                Body = Bpl.Expr.True
              });
        };

        UserSelectorFunction(Requires(ad.Arity), ad.Requires);
        UserSelectorFunction(Reads(ad.Arity), ad.Reads);

        // frame axiom
        /*

          forall t0..tN+1 : Ty, h0, h1 : Heap, f : Handle, bx1 .. bxN : Box,
            HeapSucc(h0, h1) && GoodHeap(h0) && GoodHeap(h1)
            && Is[&IsAllocBox](bxI, tI, h0)              // in h0, not hN
            && Is[&IsAlloc](f, Func(t1,..,tN, tN+1), h0) // in h0, not hN
            &&
            (forall o : ref::
                 o != null [&& h0[o, alloc] && h1[o, alloc] &&]
                 Reads(h,hN,bxs)[Box(o)]             // for hN in h0 and h1
              ==> h0[o,field] == h1[o,field])
          ==>  Reads(..h0..) == Reads(..h1..)
           AND Requires(f,h0,bxs) == Requires(f,h1,bxs) // which is needed for the next
           AND  Apply(f,h0,bxs) == Apply(f,h0,bxs)

           The [...] expressions are omitted for /allocated:0 and /allocated:1:
             - in these modes, functions are pure values and IsAlloc of a function is trivially true
             - o may be unallocated even if f reads it, so we require a stronger condition that
               even fields of *unallocated* objects o are unchanged from h0 to h1
             - given this stronger condition, we can say that f(bx1...bxN) does not change from h0 to h1
               even if some of bx1...bxN are unallocated
             - it's harder to satisfy the stronger condition, but two cases are nevertheless useful:
               1) f has an empty reads clause
               2) f explictly states that everything is its reads clause is allocated
         */
        {
          var bvars = new List<Bpl.Variable>();

          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));

          var h0 = BplBoundVar("h0", predef.HeapType, bvars);
          var h1 = BplBoundVar("h1", predef.HeapType, bvars);
          var heapSucc = HeapSucc(h0, h1);
          var goodHeaps = BplAnd(
            FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h0),
            FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h1));

          var f = BplBoundVar("f", predef.HandleType, bvars);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var isness = BplAnd(
            Snoc(Map(Enumerable.Range(0, arity), i =>
              BplAnd(MkIs(boxes[i], types[i], true),
                CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(boxes[i], types[i], h0, true) : Bpl.Expr.True)),
            BplAnd(MkIs(f, ClassTyCon(ad, types)),
              CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(f, ClassTyCon(ad, types), h0) : Bpl.Expr.True)));

          Action<Bpl.Expr, string> AddFrameForFunction = (hN, fname) => {

            // inner forall vars
            var ivars = new List<Bpl.Variable>();
            var o = BplBoundVar("o", predef.RefType, ivars);
            var a = new TypeVariable(tok, "a");
            var fld = BplBoundVar("fld", predef.FieldName(tok, a), ivars);

            var inner_forall = new Bpl.ForallExpr(tok, Singleton(a), ivars, BplImp(
              BplAnd(
                Bpl.Expr.Neq(o, predef.Null),
                // Note, the MkIsAlloc conjunct of "isness" implies that everything in the reads frame is allocated in "h0", which by HeapSucc(h0,h1) also implies the frame is allocated in "h1"
                new Bpl.NAryExpr(tok, new Bpl.MapSelect(tok, 1), new List<Bpl.Expr> {
                  FunctionCall(tok, Reads(ad.Arity), objset_ty, Concat(types, Cons(hN, Cons(f, boxes)))),
                  FunctionCall(tok, BuiltinFunction.Box, null, o)
                })
              ),
              Bpl.Expr.Eq(ReadHeap(tok, h0, o, fld), ReadHeap(tok, h1, o, fld))));

            Func<Bpl.Expr, Bpl.Expr> fn = h => FunctionCall(tok, fname, Bpl.Type.Bool, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));

            sink.AddTopLevelDeclaration(new Axiom(tok,
              BplForall(bvars,
                new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapSucc, fn(h1) }),
                BplImp(
                  BplAnd(BplAnd(BplAnd(heapSucc, goodHeaps), isness), inner_forall),
                  Bpl.Expr.Eq(fn(h0), fn(h1)))), "frame axiom for " + fname));
          };

          AddFrameForFunction(h0, Reads(ad.Arity));
          AddFrameForFunction(h1, Reads(ad.Arity));
          AddFrameForFunction(h0, Requires(ad.Arity));
          AddFrameForFunction(h1, Requires(ad.Arity));
          AddFrameForFunction(h0, Apply(ad.Arity));
          AddFrameForFunction(h1, Apply(ad.Arity));
        }

        /* axiom (forall T..: Ty, heap: Heap, f: HandleType, bx..: Box ::
         *   { ReadsN(T.., $OneHeap, f, bx..), $IsGoodHeap(heap) }
         *   { ReadsN(T.., heap, f, bx..) }
         *   $IsGoodHeap(heap) && Is...(f...bx...) ==>
         *   Set#Equal(ReadsN(T.., OneHeap, f, bx..), EmptySet) == Set#Equal(ReadsN(T.., heap, f, bx..), EmptySet));
         */
        {
          var bvars = new List<Bpl.Variable>();
          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));
          var oneheap = NewOneHeapExpr(tok);
          var h = BplBoundVar("heap", predef.HeapType, bvars);
          var f = BplBoundVar("f", predef.HandleType, bvars);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);

          var isness = BplAnd(
            Snoc(Map(Enumerable.Range(0, arity), i =>
              BplAnd(MkIs(boxes[i], types[i], true),
                CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(boxes[i], types[i], h, true) : Bpl.Expr.True)),
            BplAnd(MkIs(f, ClassTyCon(ad, types)),
              CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(f, ClassTyCon(ad, types), h) : Bpl.Expr.True)));

          var readsOne = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(oneheap, Cons(f, boxes))));
          var readsH = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(h, Cons(f, boxes))));
          var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, predef.BoxType);
          var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);
          var readsNothingH = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsH, empty);

          sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsOne, goodHeap },
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { readsH })),
            BplImp(
              BplAnd(goodHeap, isness),
              BplIff(readsNothingOne, readsNothingH))),
            string.Format("empty-reads property for {0} ", Reads(arity))));
        }

        /* axiom (forall T..: Ty, heap: Heap, f: HandleType, bx..: Box ::
         *   { RequiresN(T.., OneHeap, f, bx..), $IsGoodHeap(heap) }
         *   { RequiresN(T.., heap, f, bx..) }
         *   $IsGoodHeap(heap) && Is...(f...bx...) &&
         *   Set#Equal(ReadsN(T.., OneHeap, f, bx..), EmptySet)
         *   ==>
         *   RequiresN(T.., OneHeap, f, bx..) == RequiresN(T.., heap, f, bx..));
         */
        {
          var bvars = new List<Bpl.Variable>();
          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvars));
          var oneheap = NewOneHeapExpr(tok);
          var h = BplBoundVar("heap", predef.HeapType, bvars);
          var f = BplBoundVar("f", predef.HandleType, bvars);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvars));

          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);

          var isness = BplAnd(
            Snoc(Map(Enumerable.Range(0, arity), i =>
              BplAnd(MkIs(boxes[i], types[i], true),
                CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(boxes[i], types[i], h, true) : Bpl.Expr.True)),
            BplAnd(MkIs(f, ClassTyCon(ad, types)),
              CommonHeapUse && !FrugalHeapUse ? MkIsAlloc(f, ClassTyCon(ad, types), h) : Bpl.Expr.True)));

          var readsOne = FunctionCall(tok, Reads(arity), objset_ty, Concat(types, Cons(oneheap, Cons(f, boxes))));
          var empty = FunctionCall(tok, BuiltinFunction.SetEmpty, predef.BoxType);
          var readsNothingOne = FunctionCall(tok, BuiltinFunction.SetEqual, null, readsOne, empty);

          var requiresOne = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(oneheap, Cons(f, boxes))));
          var requiresH = FunctionCall(tok, Requires(arity), Bpl.Type.Bool, Concat(types, Cons(h, Cons(f, boxes))));

          sink.AddTopLevelDeclaration(new Axiom(tok, BplForall(bvars,
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresOne, goodHeap },
            new Bpl.Trigger(tok, true, new List<Bpl.Expr> { requiresH })),
            BplImp(
              BplAnd(BplAnd(goodHeap, isness), readsNothingOne),
              Bpl.Expr.Eq(requiresOne, requiresH))),
            string.Format("empty-reads property for {0}", Requires(arity))));
        }

        // $Is and $IsAlloc axioms
        /*
          axiom (forall f: HandleType, t0: Ty, t1: Ty ::
            { $Is(f, Tclass._System.___hFunc1(t0, t1)) }
            $Is(f, Tclass._System.___hFunc1(t0, t1))
               <==> (forall h: Heap, bx0: Box ::
                 { Apply1(t0, t1, f, h, bx0) }
                 $IsGoodHeap(h) && $IsBox(bx0, t0)
                 && precondition of f(bx0) holds in h
                 ==> $IsBox(Apply1(t0, t1, f, h, bx0), t1)));
        */
        {
          var bvarsOuter = new List<Bpl.Variable>();
          var f = BplBoundVar("f", predef.HandleType, bvarsOuter);
          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvarsOuter));
          var Is = MkIs(f, ClassTyCon(ad, types));

          var bvarsInner = new List<Bpl.Variable>();
          var h = BplBoundVar("h", predef.HeapType, bvarsInner);
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvarsInner));
          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
          var isBoxes = BplAnd(Map(Enumerable.Range(0, arity), i => MkIs(boxes[i], types[i], true)));
          var pre = FunctionCall(tok, Requires(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var applied = FunctionCall(tok, Apply(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var applied_is = MkIs(applied, types[ad.Arity], true);

          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvarsOuter, BplTrigger(Is),
              BplIff(Is,
                BplForall(bvarsInner, BplTrigger(applied),
                  BplImp(BplAnd(BplAnd(goodHeap, isBoxes), pre), applied_is))))));
        }
        /*
           axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty ::
             { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) }
             $Is(f, Tclass._System.___hFunc1(t0, t1)) &&
             (forall bx: Box :: { $IsBox(bx, u0), $IsBox(bx, t0) }
                 $IsBox(bx, u0) ==> $IsBox(bx, t0)) &&  // contravariant arguments
             (forall bx: Box :: { $IsBox(bx, t1), $IsBox(bx, u1) }
                 $IsBox(bx, t1) ==> $IsBox(bx, u1))     // covariant result
             ==>
             $Is(f, Tclass._System.___hFunc1(u0, u1)));
        */
        {
          var bvarsOuter = new List<Bpl.Variable>();
          var f = BplBoundVar("f", predef.HandleType, bvarsOuter);
          var typesT = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvarsOuter));
          var IsT = MkIs(f, ClassTyCon(ad, typesT));
          var typesU = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("u" + i, predef.Ty, bvarsOuter));
          var IsU = MkIs(f, ClassTyCon(ad, typesU));

          Func<Expr, Expr, Expr> Inner = (a, b) => {
            var bvarsInner = new List<Bpl.Variable>();
            var bx = BplBoundVar("bx", predef.BoxType, bvarsInner);
            var isBoxA = MkIs(bx, a, true);
            var isBoxB = MkIs(bx, b, true);
            var tr = new Bpl.Trigger(tok, true, new[] { isBoxA }, new Bpl.Trigger(tok, true, new[] { isBoxB }));
            var imp = BplImp(isBoxA, isBoxB);
            return BplForall(bvarsInner, tr, imp);
          };

          var body = IsT;
          for (int i = 0; i < arity; i++) {
            body = BplAnd(body, Inner(typesU[i], typesT[i]));
          }
          body = BplAnd(body, Inner(typesT[arity], typesU[arity]));
          body = BplImp(body, IsU);
          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvarsOuter, new Bpl.Trigger(tok, true, new[] { IsT, IsU }), body)));
        }
        /*  This is the definition of $IsAlloc function the arrow type:
          axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
            { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
            $IsGoodHeap(h)
            ==>
            (
              $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
                <==>
                (forall bx0: Box ::
                  { Apply1(t0, t1, f, h, bx0) } { Reads1(t0, t1, f, h, bx0) }
                  $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h)
                  && precondition of f(bx0) holds in h
                  ==>
                    (everything in reads set of f(bx0) is allocated in h)
            ));
          However, for /allocated:0 and /allocated:1, IsAlloc for arrow types is trivially true
          and implies nothing about the reads set.
        */
        {
          var bvarsOuter = new List<Bpl.Variable>();
          var f = BplBoundVar("f", predef.HandleType, bvarsOuter);
          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvarsOuter));
          var h = BplBoundVar("h", predef.HeapType, bvarsOuter);
          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
          var isAlloc = MkIsAlloc(f, ClassTyCon(ad, types), h);

          var bvarsInner = new List<Bpl.Variable>();
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvarsInner));
          var isAllocBoxes = BplAnd(Map(Enumerable.Range(0, arity), i =>
            BplAnd(MkIs(boxes[i], types[i], true), MkIsAlloc(boxes[i], types[i], h, true))));
          var pre = FunctionCall(tok, Requires(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var applied = FunctionCall(tok, Apply(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));

          // (forall r: ref :: {Reads1(t0, t1, f, h, bx0)[$Box(r)]}  r != null && Reads1(t0, t1, f, h, bx0)[$Box(r)] ==> h[r, alloc])
          var bvarsR = new List<Bpl.Variable>();
          var r = BplBoundVar("r", predef.RefType, bvarsR);
          var rNonNull = Bpl.Expr.Neq(r, predef.Null);
          var reads = FunctionCall(tok, Reads(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var rInReads = Bpl.Expr.Select(reads, FunctionCall(tok, BuiltinFunction.Box, null, r));
          var rAlloc = IsAlloced(tok, h, r);
          var isAllocReads = BplForall(bvarsR, BplTrigger(rInReads), BplImp(BplAnd(rNonNull, rInReads), rAlloc));

          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvarsOuter, BplTrigger(isAlloc),
              BplImp(goodHeap,
                BplIff(isAlloc, !CommonHeapUse ? Bpl.Expr.True :
                  BplForall(bvarsInner,
                    new Bpl.Trigger(tok, true, new List<Bpl.Expr> { applied }, BplTrigger(reads)),
                    BplImp(BplAnd(isAllocBoxes, pre), isAllocReads)))))));
        }
        /*  This is the allocatedness consequence axiom of arrow types:
          axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap ::
            { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) }
            $IsGoodHeap(h) &&
            $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
            ==>
                (forall bx0: Box ::
                  { Apply1(t0, t1, f, h, bx0) }
                  $IsAllocBox(bx0, t0, h)
                  && precondition of f(bx0) holds in h
                  ==>
                    $IsAllocBox(Apply1(t0, t1, f, h, bx0), t1, h))
            ));
        */
        if (CommonHeapUse) {
          var bvarsOuter = new List<Bpl.Variable>();
          var f = BplBoundVar("f", predef.HandleType, bvarsOuter);
          var types = Map(Enumerable.Range(0, arity + 1), i => BplBoundVar("t" + i, predef.Ty, bvarsOuter));
          var h = BplBoundVar("h", predef.HeapType, bvarsOuter);
          var goodHeap = FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, h);
          var isAlloc = MkIsAlloc(f, ClassTyCon(ad, types), h);

          var bvarsInner = new List<Bpl.Variable>();
          var boxes = Map(Enumerable.Range(0, arity), i => BplBoundVar("bx" + i, predef.BoxType, bvarsInner));
          var isAllocBoxes = BplAnd(Map(Enumerable.Range(0, arity), i => MkIsAlloc(boxes[i], types[i], h, true)));
          var pre = FunctionCall(tok, Requires(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var applied = FunctionCall(tok, Apply(ad.Arity), predef.BoxType, Concat(types, Cons(h, Cons<Bpl.Expr>(f, boxes))));
          var applied_isAlloc = MkIsAlloc(applied, types[ad.Arity], h, true);

          sink.AddTopLevelDeclaration(new Axiom(tok,
            BplForall(bvarsOuter, BplTrigger(isAlloc),
              BplImp(BplAnd(goodHeap, isAlloc),
                BplForall(bvarsInner, BplTrigger(applied),
                  BplImp(BplAnd(isAllocBoxes, pre), applied_isAlloc))))));
        }
      }
    }

    private string AddTyAxioms(TopLevelDecl td) {
      Contract.Requires(td != null);
      IToken tok = td.tok;

      var ty_repr = TrType(UserDefinedType.FromTopLevelDecl(td.tok, td));
      var arity = td.TypeArgs.Count;
      var inner_name = GetClass(td).TypedIdent.Name;
      string name = "T" + inner_name;
      // Create the type constructor
      if (td is ClassDecl cl && cl.IsObjectTrait) {
        // the type constructor for "object" is in DafnyPrelude.bpl
      } else if (td is TupleTypeDecl ttd && ttd.Dims == 2) {
        // the type constructor for "Tuple2" is in DafnyPrelude.bpl
      } else {
        Bpl.Variable tyVarOut = BplFormalVar(null, predef.Ty, false);
        List<Bpl.Variable> args = new List<Bpl.Variable>(
          Enumerable.Range(0, arity).Select(i =>
            (Bpl.Variable)BplFormalVar(null, predef.Ty, true)));
        var func = new Bpl.Function(tok, name, args, tyVarOut);
        sink.AddTopLevelDeclaration(func);
      }

      // Helper action to create variables and the function call.
      Action<Action<List<Bpl.Expr>, List<Bpl.Variable>, Bpl.Expr>> Helper = K => {
        List<Bpl.Expr> argExprs;
        var args = MkTyParamBinders(td.TypeArgs, out argExprs);
        var inner = FunctionCall(tok, name, predef.Ty, argExprs);
        K(argExprs, args, inner);
      };

      /* Create the Tag and calling Tag on this type constructor
       *
       * The common case:
       *     const unique TagList: TyTag;
       *     const unique tytagFamily$List: TyTagFamily;  // defined once for each type named "List"
       *     axiom (forall t0: Ty :: { List(t0) } Tag(List(t0)) == TagList && TagFamily(List(t0)) == tytagFamily$List);
       * For types obtained via an abstract import, just do:
       *     const unique tytagFamily$List: TyTagFamily;  // defined once for each type named "List"
       *     axiom (forall t0: Ty :: { List(t0) } TagFamily(List(t0)) == tytagFamily$List);
       */
      Helper((argExprs, args, inner) => {
        Bpl.Expr body = Bpl.Expr.True;

        if (!td.EnclosingModuleDefinition.IsFacade) {
          var tagName = "Tag" + inner_name;
          var tag = new Bpl.Constant(tok, new Bpl.TypedIdent(tok, tagName, predef.TyTag), true);
          sink.AddTopLevelDeclaration(tag);
          body = Bpl.Expr.Eq(FunctionCall(tok, "Tag", predef.TyTag, inner), new Bpl.IdentifierExpr(tok, tag));
        }

        if (!tytagConstants.TryGetValue(td.Name, out var tagFamily)) {
          tagFamily = new Bpl.Constant(Token.NoToken, new Bpl.TypedIdent(Token.NoToken, "tytagFamily$" + td.Name, predef.TyTagFamily), true);
          tytagConstants.Add(td.Name, tagFamily);
        }
        body = BplAnd(body, Bpl.Expr.Eq(FunctionCall(tok, "TagFamily", predef.TyTagFamily, inner), new Bpl.IdentifierExpr(tok, tagFamily)));

        var qq = BplForall(args, BplTrigger(inner), body);
        sink.AddTopLevelDeclaration(new Axiom(tok, qq, name + " Tag"));
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
          sink.AddTopLevelDeclaration(new Axiom(tok, qq, name + " injectivity " + i));
          sink.AddTopLevelDeclaration(injfunc);
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
      if (!ModeledAsBoxType(UserDefinedType.FromTopLevelDecl(td.tok, td))) {
        Helper((argExprs, args, _inner) => {
          var typeTerm = FunctionCall(tok, name, predef.Ty, argExprs);
          AddBoxUnboxAxiom(tok, name, typeTerm, ty_repr, args);
        });
      }

      return name;
    }

    /// <summary>
    /// Generate:
    ///     axiom (forall args: Ty, bx: Box ::
    ///       { $IsBox(bx, name(argExprs)) }
    ///       $IsBox(bx, name(argExprs)) ==>
    ///         $Box($Unbox(bx): tyRepr) == bx &&
    ///         $Is($Unbox(bx): tyRepr, name(argExprs)));
    /// </summary>
    private void AddBoxUnboxAxiom(IToken tok, string printableName, Bpl.Expr typeTerm, Bpl.Type tyRepr, List<Variable> args) {
      Contract.Requires(tok != null);
      Contract.Requires(printableName != null);
      Contract.Requires(typeTerm != null);
      Contract.Requires(tyRepr != null);
      Contract.Requires(args != null);

      var bxVar = BplBoundVar("bx", predef.BoxType, out var bx);
      var unbox = FunctionCall(tok, BuiltinFunction.Unbox, tyRepr, bx);
      var box_is = MkIs(bx, typeTerm, true);
      var unbox_is = MkIs(unbox, typeTerm, false);
      var box_unbox = FunctionCall(tok, BuiltinFunction.Box, null, unbox);
      sink.AddTopLevelDeclaration(
        new Axiom(tok,
          BplForall(Snoc(args, bxVar), BplTrigger(box_is),
            BplImp(box_is, BplAnd(Bpl.Expr.Eq(box_unbox, bx), unbox_is))),
          "Box/unbox axiom for " + printableName));
    }

    Bpl.Constant GetClass(TopLevelDecl cl)
    {
      Contract.Requires(cl != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Constant>() != null);

      if (classes.TryGetValue(cl, out var cc)) {
        Contract.Assert(cc != null);
      } else {
        var name = cl.FullSanitizedName;
        if (cl is ClassDecl && ((ClassDecl)cl).NonNullTypeDecl != null) {
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

    Bpl.Constant GetField(Field f)
    {
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
        sink.AddTopLevelDeclaration(ax);
      }
      return fc;
    }


    Bpl.Function GetReadonlyField(Field f)
    {
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
        } else if (f.EnclosingClass == null && f.Name == "Floor") {
          return predef.RealFloor;
        } else if (f is SpecialField && (f.Name == "Keys" || f.Name == "Values" || f.Name == "Items")) {
          Contract.Assert(f.Type is SetType);
          var setType = (SetType)f.Type;
          if (f.Name == "Keys") {
            return setType.Finite ? predef.MapDomain : predef.IMapDomain;
          } else if (f.Name == "Values") {
            return setType.Finite ? predef.MapValues : predef.IMapValues;
          } else {
            return setType.Finite ? predef.MapItems : predef.IMapItems;
          }
        } else if (f is SpecialField && f.Name == "IsLimit") {
          return predef.ORDINAL_IsLimit;
        } else if (f is SpecialField && f.Name == "IsSucc") {
          return predef.ORDINAL_IsSucc;
        } else if (f is SpecialField && f.Name == "Offset") {
          return predef.ORDINAL_Offset;
        } else if (f is SpecialField && f.Name == "IsNat") {
          return predef.ORDINAL_IsNat;
        } else if (f.FullSanitizedName == "_System.Tuple2._0") {
          return predef.Tuple2Destructors0;
        } else if (f.FullSanitizedName == "_System.Tuple2._1") {
          return predef.Tuple2Destructors1;
        }

        // Create a new function
        // function f(Ref): ty;
        List<Variable> formals = new List<Variable>();
        if (f is ConstantField) {
          formals.AddRange(MkTyParamFormals(GetTypeParams(f.EnclosingClass)));
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
            sink.AddTopLevelDeclaration(ff.CreateDefinitionAxiom(etran.TrExpr(cf.Rhs)));
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
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f)));
        if (f.IsFuelAware()) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$ly", predef.LayerType), true));
        }
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType), true));
        }
        if (AlwaysUseHeap || f.ReadsHeap) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$heap", predef.HeapType), true));
        }
        if (!f.IsStatic) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "this", TrReceiverType(f)), true));
        }
        foreach (var p in f.Formals) {
          formals.Add(new Bpl.Formal(p.tok, new Bpl.TypedIdent(p.tok, p.AssignUniqueName(f.IdGenerator), TrType(p.Type)), true));
        }
        var res = new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, Bpl.TypedIdent.NoName, TrType(f.ResultType)), false);
        var func = new Bpl.Function(f.tok, f.FullSanitizedName, new List<Bpl.TypeVariable>(), formals, res, "function declaration for " + f.FullName);
        if (InsertChecksums) {
          InsertChecksum(f, func);
        }
        sink.AddTopLevelDeclaration(func);
      }

      // declare the corresponding canCall function
      {
        var formals = new List<Variable>();
        formals.AddRange(MkTyParamFormals(GetTypeParams(f)));
        if (f is TwoStateFunction) {
          formals.Add(new Bpl.Formal(f.tok, new Bpl.TypedIdent(f.tok, "$prevHeap", predef.HeapType), true));
        }
        if (AlwaysUseHeap || f.ReadsHeap) {
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

    /// <summary>
    /// This method is expected to be called at most once for each parameter combination, and in particular
    /// at most once for each value of "kind".
    /// </summary>
    Bpl.Procedure AddMethod(Method m, MethodTranslationKind kind)
    {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(predef != null);
      Contract.Requires(currentModule == null && codeContext == null && isAllocContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && isAllocContext == null);
      Contract.Ensures(Contract.Result<Bpl.Procedure>() != null);
      Contract.Assert(VisibleInScope(m));

      currentModule = m.EnclosingClass.EnclosingModuleDefinition;
      codeContext = m;
      isAllocContext = new IsAllocContext(m.IsGhost);

      Bpl.Expr prevHeap = null;
      Bpl.Expr currHeap = null;
      var ordinaryEtran = new ExpressionTranslator(this, predef, m.tok);
      ExpressionTranslator etran;
      var inParams = new List<Bpl.Variable>();
      if (m is TwoStateLemma) {
        var prevHeapVar = new Bpl.Formal(m.tok, new Bpl.TypedIdent(m.tok, "previous$Heap", predef.HeapType), true);
        var currHeapVar = new Bpl.Formal(m.tok, new Bpl.TypedIdent(m.tok, "current$Heap", predef.HeapType), true);
        inParams.Add(prevHeapVar);
        inParams.Add(currHeapVar);
        prevHeap = new Bpl.IdentifierExpr(m.tok, prevHeapVar);
        currHeap = new Bpl.IdentifierExpr(m.tok, currHeapVar);
        etran = new ExpressionTranslator(this, predef, currHeap, prevHeap);
      } else {
        etran = ordinaryEtran;
      }

      List<Variable> outParams;
      GenerateMethodParameters(m.tok, m, kind, etran, inParams, out outParams);

      var req = new List<Bpl.Requires>();
      var mod = new List<Bpl.IdentifierExpr>();
      var ens = new List<Bpl.Ensures>();
      // FREE PRECONDITIONS
      if (kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation || kind == MethodTranslationKind.OverrideCheck) {  // the other cases have no need for a free precondition
        // free requires mh == ModuleContextHeight && fh == FunctionContextHeight;
        req.Add(Requires(m.tok, true, etran.HeightContext(kind == MethodTranslationKind.OverrideCheck ? m.OverriddenMethod : m), null, null));
        if (m is TwoStateLemma) {
          // free requires prevHeap == Heap && HeapSucc(prevHeap, currHeap) && IsHeap(currHeap)
          var a0 = Bpl.Expr.Eq(prevHeap, ordinaryEtran.HeapExpr);
          var a1 = HeapSucc(prevHeap, currHeap);
          var a2 = FunctionCall(m.tok, BuiltinFunction.IsGoodHeap, null, currHeap);
          req.Add(Requires(m.tok, true, BplAnd(a0, BplAnd(a1, a2)), null, null));
        }
      }
      if (m is TwoStateLemma) {
        // Checked preconditions that old parameters really existed in previous state
        var index = 0;
        foreach (var formal in m.Ins) {
          if (formal.IsOld) {
            var dafnyFormalIdExpr = new IdentifierExpr(formal.tok, formal);
            req.Add(Requires(formal.tok, false, MkIsAlloc(etran.TrExpr(dafnyFormalIdExpr), formal.Type, prevHeap),
              string.Format("parameter{0} ('{1}') must be allocated in the two-state lemma's previous state",
              m.Ins.Count == 1 ? "" : " " + index, formal.Name), null));
          }
          index++;
        }
      }
      mod.Add((Bpl.IdentifierExpr/*TODO: this cast is somewhat dubious*/)ordinaryEtran.HeapExpr);
      mod.Add(etran.Tick());

      var bodyKind = kind == MethodTranslationKind.SpecWellformedness || kind == MethodTranslationKind.Implementation;

      if (kind != MethodTranslationKind.SpecWellformedness && kind != MethodTranslationKind.OverrideCheck)
      {
        // USER-DEFINED SPECIFICATIONS
        var comment = "user-defined preconditions";
        foreach (var p in m.Req) {
          string errorMessage = CustomErrorMessage(p.Attributes);
          if (p.Label != null && kind == MethodTranslationKind.Implementation) {
            // don't include this precondition here, but record it for later use
            p.Label.E = (m is TwoStateLemma ? ordinaryEtran : etran.Old).TrExpr(p.E);
          } else {
            foreach (var s in TrSplitExprForMethodSpec(p.E, etran, kind)) {
              if (s.IsOnlyChecked && bodyKind) {
                // don't include in split
              } else if (s.IsOnlyFree && !bodyKind) {
                // don't include in split -- it would be ignored, anyhow
              } else {
                req.Add(Requires(s.E.tok, s.IsOnlyFree, s.E, errorMessage, comment));
                comment = null;
                // the free here is not linked to the free on the original expression (this is free things generated in the splitting.)
              }
            }
          }
        }
        comment = "user-defined postconditions";
        foreach (var p in m.Ens) {
          string errorMessage = CustomErrorMessage(p.Attributes);
          AddEnsures(ens, Ensures(p.E.tok, true, CanCallAssumption(p.E, etran), errorMessage, comment));
          comment = null;
          foreach (var s in TrSplitExprForMethodSpec(p.E, etran, kind)) {
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
              AddEnsures(ens, Ensures(s.E.tok, s.IsOnlyFree, post, errorMessage, null));
            }
          }
        }
        if (m is Constructor && kind == MethodTranslationKind.Call) {
          var fresh = Bpl.Expr.Not(etran.Old.IsAlloced(m.tok, new Bpl.IdentifierExpr(m.tok, "this", TrReceiverType(m))));
          AddEnsures(ens, Ensures(m.tok, false, fresh, null, "constructor allocates the object"));
        }
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(m.tok, m.Mod.Expressions, m.IsGhost, ordinaryEtran.Old, ordinaryEtran, ordinaryEtran.Old)) {
          AddEnsures(ens, Ensures(tri.tok, tri.IsFree, tri.Expr, tri.ErrorMessage, tri.Comment));
        }

        // add the fuel assumption for the reveal method of a opaque method
        if (IsOpaqueRevealLemma(m)) {
          List<Expression> args = Attributes.FindExpressions(m.Attributes, "fuel");
          if (args != null) {
            MemberSelectExpr selectExpr = args[0].Resolved as MemberSelectExpr;
            if (selectExpr != null) {
              Function f = selectExpr.Member as Function;
              FuelConstant fuelConstant = this.functionFuel.Find(x => x.f == f);
              if (fuelConstant != null) {
                Bpl.Expr startFuel = fuelConstant.startFuel;
                Bpl.Expr startFuelAssert = fuelConstant.startFuelAssert;
                Bpl.Expr moreFuel_expr = fuelConstant.MoreFuel(sink, predef, f.IdGenerator);
                Bpl.Expr layer = etran.layerInterCluster.LayerN(1, moreFuel_expr);
                Bpl.Expr layerAssert = etran.layerInterCluster.LayerN(2, moreFuel_expr);

                AddEnsures(ens, Ensures(m.tok, true, Bpl.Expr.Eq(startFuel, layer), null, null));
                AddEnsures(ens, Ensures(m.tok, true, Bpl.Expr.Eq(startFuelAssert, layerAssert), null, null));

                AddEnsures(ens, Ensures(m.tok, true, Bpl.Expr.Eq(FunctionCall(f.tok, BuiltinFunction.AsFuelBottom, null, moreFuel_expr), moreFuel_expr), null, "Shortcut to LZ"));
                }
            }
          }
        }
      }

      var name = MethodName(m, kind);
      var proc = new Bpl.Procedure(m.tok, name, new List<Bpl.TypeVariable>(), inParams, outParams, req, mod, ens, etran.TrAttributes(m.Attributes, null));

      if (InsertChecksums)
      {
        InsertChecksum(m, proc, true);
      }

      currentModule = null;
      codeContext = null;
      isAllocContext = null;

      return proc;
    }

    static string MethodName(ICodeContext m, MethodTranslationKind kind) {
      Contract.Requires(m != null);
      switch (kind) {
        case MethodTranslationKind.SpecWellformedness:
          return "CheckWellformed$$" + m.FullSanitizedName;
        case MethodTranslationKind.Call:
          return "Call$$" + m.FullSanitizedName;
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
      inParams.AddRange(MkTyParamFormals(GetTypeParams(m)));
      if (includeReceiver) {
        var receiverType = m is MemberDecl ? Resolver.GetReceiverType(tok, (MemberDecl)m) : Resolver.GetThisType(tok, (IteratorDecl)m);
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
          if (!VisibleInScope(p.Type)) {
            Contract.Assert(false);
          }
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
        m.Outs.Iter(RemoveDefiniteAssignmentTracker);
        Contract.Assert(definiteAssignmentTrackers.Count == 0);

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
    List<BoilerplateTriple/*!*/>/*!*/ GetTwoStateBoilerplate(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ modifiesClause, bool isGhostContext,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod)
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
        bool fieldGranularity = true;
        bool objectGranularity = !fieldGranularity;
        // the frame condition, which is free since it is checked with every heap update and call
        boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, isGhostContext, Resolver.FrameExpressionUse.Modifies, etranPre, etran, etranMod, objectGranularity), null, "frame condition: object granularity"));
        if (modifiesClause.Exists(fe => fe.FieldName != null)) {
          boilerplate.Add(new BoilerplateTriple(tok, true, FrameCondition(tok, modifiesClause, isGhostContext, Resolver.FrameExpressionUse.Modifies, etranPre, etran, etranMod, fieldGranularity), null, "frame condition: field granularity"));
        }
        // HeapSucc(S1, S2) or HeapSuccGhost(S1, S2)
        Bpl.Expr heapSucc = HeapSucc(etranPre.HeapExpr, etran.HeapExpr, isGhostContext);
        boilerplate.Add(new BoilerplateTriple(tok, true, heapSucc, null, "boilerplate"));
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
    Bpl.Expr/*!*/ FrameCondition(IToken/*!*/ tok, List<FrameExpression/*!*/>/*!*/ frame, bool isGhostContext, Resolver.FrameExpressionUse use,
      ExpressionTranslator/*!*/ etranPre, ExpressionTranslator/*!*/ etran, ExpressionTranslator/*!*/ etranMod, bool fieldGranularity)
    {
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
      //      && old($Heap)[o][alloc]                     // include only in non-ghost contexts
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
      //      && old($Heap)[o][alloc]                     // include only in non-ghost contexts
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
        heapOF = ReadHeap(tok, etran.HeapExpr, o, f);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o, f);
      } else {
        // object granularity
        typeVars = new List<TypeVariable>();
        f = null;
        quantifiedVars = new List<Variable> { oVar };
        heapOF = ReadHeap(tok, etran.HeapExpr, o);
        preHeapOF = ReadHeap(tok, etranPre.HeapExpr, o);
      }

      Bpl.Expr ante = Bpl.Expr.Neq(o, predef.Null);
      if (!isGhostContext && use == Resolver.FrameExpressionUse.Modifies) {
        ante = Bpl.Expr.And(ante, etranMod.IsAlloced(tok, o));
      }
      var eq = Bpl.Expr.Eq(heapOF, preHeapOF);
      var ofInFrame = InRWClause(tok, o, f, frame, use == Resolver.FrameExpressionUse.Unchanged, etranMod, null, null);
      Bpl.Expr consequent = use == Resolver.FrameExpressionUse.Modifies ? Bpl.Expr.Or(eq, ofInFrame) : Bpl.Expr.Imp(ofInFrame, eq);

      var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> { heapOF });
      return new Bpl.ForallExpr(tok, typeVars, quantifiedVars, null, tr, Bpl.Expr.Imp(ante, consequent));
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
      } else if (type.IsTypeParameter || type.IsOpaqueType) {
        return predef.BoxType;
      } else if (type.IsInternalTypeSynonym) {
        return predef.BoxType;
      } else if (type.IsRefType) {
        // object and class types translate to ref
        return predef.RefType;
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

    public Bpl.Expr CondApplyBox(IToken tok, Bpl.Expr e, Type fromType, Type toType) {
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
    /// KRML: The name of this method is really confusing. It seems it should be named something like UnboxUnlessInherentlyBoxed.
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
      var res = t.IsTypeParameter || t.IsOpaqueType || t.IsInternalTypeSynonym;
      Contract.Assert(t.IsArrowType ? !res : true);
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
        return TrAssumeCmd(tok, condition, kv);
      } else {
        var cmd = TrAssertCmd(ForceCheckToken.Unwrap(tok), condition, kv);
        cmd.ErrorData = "Error: " + errorMessage;
        this.assertionCount++;
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
        return TrAssumeCmd(tok, Bpl.Expr.True, kv);
      } else {
        tok = ForceCheckToken.Unwrap(tok);
        var args = new List<object>();
        args.Add(Bpl.Expr.Literal(0));
        Bpl.AssertCmd cmd = TrAssertCmd(tok, condition, new Bpl.QKeyValue(tok, "subsumption", args, kv));
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
        return TrAssumeCmd(tok, condition, kv);
      } else {
        var cmd = TrAssertCmd(ForceCheckToken.Unwrap(tok), condition, kv);
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
      Contract.Ensures(Contract.Result<Bpl.Requires>() != null);
      Bpl.Requires req = new Bpl.Requires(ForceCheckToken.Unwrap(tok), free, condition, comment);
      if (errorMessage != null) {
        req.ErrorData = errorMessage;
      }
      return req;
    }

    Bpl.StmtList TrStmt2StmtList(BoogieStmtListBuilder builder, Statement block, List<Variable> locals, ExpressionTranslator etran)
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

    string CustomErrorMessage(Attributes attrs)
    {
      if (attrs == null) { return null; }
      List<Expression> args = Attributes.FindExpressions(attrs, "error");
      if (args == null) { return null; }
      if (args.Count > 0) {
        StringLiteralExpr l = args[0] as StringLiteralExpr;
        return (string)l.Value;
      } else {
        return null;
      }
    }

    void TrStmt(Statement stmt, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(codeContext != null && predef != null);
      Contract.Ensures(fuelContext == Contract.OldValue(fuelContext));

      stmtContext = StmtType.NONE;
      adjustFuelForExists = true;  // fuel for exists might need to be adjusted based on whether it's in an assert or assume stmt.
      if (stmt is PredicateStmt) {
        var stmtBuilder = new BoogieStmtListBuilder(this);
        string errorMessage = CustomErrorMessage(stmt.Attributes);
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        var defineFuel = DefineFuelConstant(stmt.Tok, stmt.Attributes, stmtBuilder, etran);
        var b = defineFuel ? stmtBuilder : builder;
        if (stmt is AssertStmt || DafnyOptions.O.DisallowSoundnessCheating) {
          stmtContext = StmtType.ASSERT;
          AddComment(b, stmt, "assert statement");
          PredicateStmt s = (PredicateStmt)stmt;
          TrStmt_CheckWellformed(s.Expr, b, locals, etran, false);
          IToken enclosingToken = null;
          if (Attributes.Contains(stmt.Attributes, "_prependAssertToken")) {
            enclosingToken = stmt.Tok;
          }
          BoogieStmtListBuilder proofBuilder = null;
          var assertStmt = stmt as AssertStmt;
          if (assertStmt != null && assertStmt.Proof != null) {
            proofBuilder = new BoogieStmtListBuilder(this);
            AddComment(proofBuilder, stmt, "assert statement proof");
            TrStmt(((AssertStmt)stmt).Proof, proofBuilder, locals, etran);
          } else if (assertStmt != null && assertStmt.Label != null) {
            proofBuilder = new BoogieStmtListBuilder(this);
            AddComment(proofBuilder, stmt, "assert statement proof");
          }
          bool splitHappened;
          var ss = TrSplitExpr(s.Expr, etran, true, out splitHappened);
          if (!splitHappened) {
            var tok = enclosingToken == null ? s.Expr.tok : new NestedToken(enclosingToken, s.Expr.tok);
            (proofBuilder ?? b).Add(Assert(tok, etran.TrExpr(s.Expr), errorMessage ?? "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));
          } else {
            foreach (var split in ss) {
              if (split.IsChecked) {
                var tok = enclosingToken == null ? split.E.tok : new NestedToken(enclosingToken, split.E.tok);
                (proofBuilder ?? b).Add(AssertNS(tok, split.E, errorMessage ?? "assertion violation", stmt.Tok, etran.TrAttributes(stmt.Attributes, null)));  // attributes go on every split
              }
            }
          }
          if (proofBuilder != null) {
            PathAsideBlock(stmt.Tok, proofBuilder, b);
          }
          stmtContext = StmtType.NONE; // done with translating assert stmt
          if (splitHappened || proofBuilder != null) {
            if (assertStmt != null && assertStmt.Label != null) {
              // make copies of the variables used in the assertion
              var name = "$Heap_at_" + assertStmt.Label.AssignUniqueId(CurrentIdGenerator);
              var heapAt = new Bpl.LocalVariable(stmt.Tok, new Bpl.TypedIdent(stmt.Tok, name, predef.HeapType));
              locals.Add(heapAt);
              var h = new Bpl.IdentifierExpr(stmt.Tok, heapAt);
              b.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, h, etran.HeapExpr));
              var substMap = new Dictionary<IVariable, Expression>();
              foreach (var v in ComputeFreeVariables(assertStmt.Expr)) {
                if (v is LocalVariable) {
                  var vcopy = new LocalVariable(stmt.Tok, stmt.Tok, string.Format("##{0}#{1}", name, v.Name), v.Type, v.IsGhost);
                  vcopy.type = vcopy.OptionalType;  // resolve local here
                  IdentifierExpr ie = new IdentifierExpr(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator));
                  ie.Var = vcopy; ie.Type = ie.Var.Type;  // resolve ie here
                  substMap.Add(v, ie);
                  locals.Add(new Bpl.LocalVariable(vcopy.Tok, new Bpl.TypedIdent(vcopy.Tok, vcopy.AssignUniqueName(currentDeclaration.IdGenerator), TrType(vcopy.Type))));
                  b.Add(Bpl.Cmd.SimpleAssign(stmt.Tok, TrVar(stmt.Tok, vcopy), TrVar(stmt.Tok, v)));
                }
              }
              var exprToBeRevealed = Substitute(assertStmt.Expr, null, substMap);
              var etr = new ExpressionTranslator(etran, h);
              assertStmt.Label.E = etr.TrExpr(exprToBeRevealed);
            } else if (!defineFuel) {
              // Adding the assume stmt, resetting the stmtContext
              stmtContext = StmtType.ASSUME;
              adjustFuelForExists = true;
              b.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
              stmtContext = StmtType.NONE;
            }
          }
          if (defineFuel) {
            var ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), null, null);  // BUGBUG: shouldn't this first append "assume false" to "b"? (use PathAsideBlock to do this)  --KRML
            builder.Add(ifCmd);
            // Adding the assume stmt, resetting the stmtContext
            stmtContext = StmtType.ASSUME;
            adjustFuelForExists = true;
            builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr)));
            stmtContext = StmtType.NONE;
          }
        } else if (stmt is ExpectStmt) {
          AddComment(builder, stmt, "expect statement");
          ExpectStmt s = (ExpectStmt)stmt;
          stmtContext = StmtType.ASSUME;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);

          // Need to check the message is well-formed, assuming the expected expression
          // does NOT hold:
          //
          // if Not(TrExpr[[ s.Expr ]]) {
          //  CheckWellformed[[ s.Message ]]
          //  assume false;
          // }
          BoogieStmtListBuilder thnBuilder = new BoogieStmtListBuilder(this);
          TrStmt_CheckWellformed(s.Message, thnBuilder, locals, etran, false);
          thnBuilder.Add(TrAssumeCmd(stmt.Tok, new Bpl.LiteralExpr(stmt.Tok, false), etran.TrAttributes(stmt.Attributes, null)));
          Bpl.StmtList thn = thnBuilder.Collect(s.Tok);
          builder.Add(new Bpl.IfCmd(stmt.Tok, Bpl.Expr.Not(etran.TrExpr(s.Expr)), thn, null, null));

          stmtContext = StmtType.NONE;  // done with translating expect stmt.
        } else if (stmt is AssumeStmt) {
          AddComment(builder, stmt, "assume statement");
          AssumeStmt s = (AssumeStmt)stmt;
          stmtContext = StmtType.ASSUME;
          TrStmt_CheckWellformed(s.Expr, builder, locals, etran, false);
          builder.Add(TrAssumeCmd(stmt.Tok, etran.TrExpr(s.Expr), etran.TrAttributes(stmt.Attributes, null)));
          stmtContext = StmtType.NONE;  // done with translating assume stmt.
        }
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is PrintStmt) {
        AddComment(builder, stmt, "print statement");
        PrintStmt s = (PrintStmt)stmt;
        foreach (var arg in s.Args) {
          TrStmt_CheckWellformed(arg, builder, locals, etran, false);
        }

      } else if (stmt is RevealStmt) {
        AddComment(builder, stmt, "reveal statement");
        var s = (RevealStmt)stmt;
        foreach (var la in s.LabeledAsserts) {
          Contract.Assert(la.E != null);  // this should have been filled in by now
          builder.Add(new Bpl.AssumeCmd(s.Tok, la.E));
        }
        foreach (var resolved in s.ResolvedStatements) {
          TrStmt(resolved, builder, locals, etran);
        }

      } else if (stmt is BreakStmt) {
        AddComment(builder, stmt, "break statement");
        var s = (BreakStmt)stmt;
        builder.Add(new GotoCmd(s.Tok, new List<String> { "after_" + s.TargetStmt.Labels.Data.AssignUniqueId(CurrentIdGenerator) }));
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
        if (codeContext is IMethodCodeContext) {
          var method = (IMethodCodeContext)codeContext;
          method.Outs.Iter(p => CheckDefiniteAssignmentReturn(stmt.Tok, p, builder));
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
        var th = new ThisExpr(iter);
        Contract.Assert(iter.OutsFields.Count == iter.OutsHistoryFields.Count);
        for (int i = 0; i < iter.OutsFields.Count; i++) {
          var y = iter.OutsFields[i];
          var dafnyY = new MemberSelectExpr(s.Tok, th, y);
          var ys = iter.OutsHistoryFields[i];
          var dafnyYs = new MemberSelectExpr(s.Tok, th, ys);
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
        builder.Add(TrAssumeCmd(s.Tok, YieldCountAssumption(iter, etran)));
        // assume $IsGoodHeap($Heap);
        builder.Add(AssumeGoodHeap(s.Tok, etran));
        // assert YieldEnsures[subst];  // where 'subst' replaces "old(E)" with "E" being evaluated in $_OldIterHeap
        var yeEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, new Bpl.IdentifierExpr(s.Tok, "$_OldIterHeap", predef.HeapType));
        foreach (var p in iter.YieldEnsures) {
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
          builder.Add(TrAssumeCmd(stmt.Tok, yeEtran.TrExpr(p.E)));
        }
        YieldHavoc(iter.tok, iter, builder, etran);
        builder.Add(CaptureState(s));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        AddComment(builder, s, "assign-such-that statement");
        // Essentially, treat like an assert (that values for the LHS exist), a havoc (of the LHS), and an
        // assume (of the RHS).  However, we also need to check the well-formedness of the LHS and RHS.
        // The well-formedness of the LHS is done by the havoc. The well-formedness of the RHS is most
        // easily done after that havoc, but we need to be careful about two things:
        //   - We should not generate any errors for uses of LHSs. This is not an issue for fields or
        //     array elements, because they already have values before reaching the assign-such-that statement.
        //     (Note, "this.f" is not allowed as a LHS in the first division of a constructor.)
        //     For any local variable or out-parameter x that's a LHS, we create a new variable x' and
        //     substitute x' for x in the RHS before doing the well-formedness check.
        //   - The well-formedness checks need to be able to assume that each x' has a value of its
        //     type. However, this assumption must not carry over to the existence assertion, because
        //     then everything will be provable if x' is of a known-empty type. Instead, the well-formedness
        //     check is wrapped inside an "if" whose guard is the type antecedent. After the existence
        //     check, the type antecedent is assumed of the original x, the RHS is assumed, and x is
        //     marked off has having been definitely assigned.
        //
        // So, the Dafny statement
        //     E.f, x :| RHS(x);
        // is translated into the following Boogie code:
        //     var x';
        //     Tr[[ E.f := *; ]]  // this havoc is translated like a Dafny assignment statement, which means
        //                        // the well-formedness of E is checked here
        //     if (typeAntecedent(x')) {
        //       check well-formedness of RHS(x');
        //     }
        //     assert (exists x'' :: RHS(x''));  // for ":| assume", omit this line; for ":|", LHS is only allowed to contain simple variables
        //     defass$x := true;
        //     havoc x;
        //     assume RHS(x);

        var simpleLHSs = new List<IdentifierExpr>();
        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        var havocLHSs = new List<Expression>();
        var havocRHSs = new List<AssignmentRhs>();
        var substMap = new Dictionary<IVariable, Expression>();
        foreach (var lhs in s.Lhss) {
          var lvalue = lhs.Resolved;
          if (lvalue is IdentifierExpr ide) {
            simpleLHSs.Add(ide);
            var wh = SetupVariableAsLocal(ide.Var, substMap, builder, locals, etran);
            typeAntecedent = BplAnd(typeAntecedent, wh);
          } else {
            havocLHSs.Add(lhs.Resolved);
            havocRHSs.Add(new HavocRhs(lhs.tok));  // note, a HavocRhs is constructed as already resolved
          }
        }
        ProcessLhss(havocLHSs, false, true, builder, locals, etran, out var lhsBuilder, out var bLhss, out _, out _, out _);
        ProcessRhss(lhsBuilder, bLhss, havocLHSs, havocRHSs, builder, locals, etran);

        // Here comes the well-formedness check
        var wellFormednessBuilder = new BoogieStmtListBuilder(this);
        var rhs = Substitute(s.Expr, null, substMap);
        TrStmt_CheckWellformed(rhs, wellFormednessBuilder, locals, etran, false);
        var ifCmd = new Bpl.IfCmd(s.Tok, typeAntecedent, wellFormednessBuilder.Collect(s.Tok), null, null);
        builder.Add(ifCmd);

        // Here comes the assert part
        if (s.AssumeToken == null) {
          substMap = new Dictionary<IVariable, Expression>();
          var bvars = new List<BoundVar>();
          foreach (var lhs in s.Lhss) {
            var l = lhs.Resolved;
            if (l is IdentifierExpr x) {
              CloneVariableAsBoundVar(x.tok, x.Var, "$as#" + x.Name, out var bv, out var ie);
              bvars.Add(bv);
              substMap.Add(x.Var, ie);
            } else {
              // other forms of LHSs have been ruled out by the resolver (it would be possible to
              // handle them, but it would involve heap-update expressions--the translation would take
              // effort, and it's not certain that the existential would be successful in verification).
              Contract.Assume(false);  // unexpected case
            }
          }

          GenerateAndCheckGuesses(s.Tok, bvars, s.Bounds, Substitute(s.Expr, null, substMap), TrTrigger(etran, s.Attributes, s.Tok, substMap), builder, etran);
        }

        // Mark off the simple variables as having definitely been assigned AND THEN havoc their values. By doing them
        // in this order, they type antecedents will in effect be assumed.
        var bHavocLHSs = new List<Bpl.IdentifierExpr>();
        foreach (var lhs in simpleLHSs) {
          MarkDefiniteAssignmentTracker(lhs, builder);
          bHavocLHSs.Add((Bpl.IdentifierExpr)etran.TrExpr(lhs));
        }
        builder.Add(new Bpl.HavocCmd(s.Tok, bHavocLHSs));

        // End by doing the assume
        builder.Add(TrAssumeCmd(s.Tok, etran.TrExpr(s.Expr)));
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
          CheckLhssDistinctness(finalRhss, s.Rhss, lhss, builder, etran, lhsObjs, lhsFields, lhsNames, s.OriginalInitialLhs);
          // Now actually perform the assignments to the LHS.
          for (int i = 0; i < lhss.Count; i++) {
            lhsBuilder[i](finalRhss[i], s.Rhss[i] is HavocRhs, builder, etran);
          }
          builder.Add(CaptureState(s));
        }

      } else if (stmt is AssignOrReturnStmt) {
        AddComment(builder, stmt, "assign-or-return statement (:-)");
        AssignOrReturnStmt s = (AssignOrReturnStmt)stmt;
        TrStmtList(s.ResolvedStatements, builder, locals, etran);

      } else if (stmt is AssignStmt) {
        AddComment(builder, stmt, "assignment statement");
        AssignStmt s = (AssignStmt)stmt;
        TrAssignment(stmt, s.Lhs.Resolved, s.Rhs, builder, locals, etran);

      } else if (stmt is CallStmt) {
        AddComment(builder, stmt, "call statement");
        TrCallStmt((CallStmt)stmt, builder, locals, etran, null);

      } else if (stmt is DividedBlockStmt) {
        var s = (DividedBlockStmt)stmt;
        AddComment(builder, stmt, "divided block before new;");
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        var tok = s.SeparatorTok ?? s.Tok;
        // a DividedBlockStmt occurs only inside a Constructor body of a class
        var cl = (ClassDecl)((Constructor)codeContext).EnclosingClass;
        var fields = Concat(cl.InheritedMembers, cl.Members).ConvertAll(member =>
          member is Field && !member.IsStatic && !member.IsInstanceIndependentConstant ? (Field)member : null);
        fields.RemoveAll(f => f == null);
        var localSurrogates = fields.ConvertAll(f => new Bpl.LocalVariable(f.tok, new TypedIdent(f.tok, SurrogateName(f), TrType(f.Type))));
        locals.AddRange(localSurrogates);
        fields.Iter(f => AddDefiniteAssignmentTrackerSurrogate(f, cl, locals));

        Contract.Assert(!inBodyInitContext);
        inBodyInitContext = true;
        TrStmtList(s.BodyInit, builder, locals, etran);
        Contract.Assert(inBodyInitContext);
        inBodyInitContext = false;

        // The "new;" translates into an allocation of "this"
        AddComment(builder, stmt, "new;");
        fields.Iter(f => CheckDefiniteAssignmentSurrogate(s.SeparatorTok ?? s.EndTok, f, true, builder));
        fields.Iter(f => RemoveDefiniteAssignmentTrackerSurrogate(f));
        var th = new ThisExpr(cl);
        var bplThis = (Bpl.IdentifierExpr)etran.TrExpr(th);
        SelectAllocateObject(tok, bplThis, th.Type, false, builder, etran);
        for (int i = 0; i < fields.Count; i++) {
          // assume $Heap[this, f] == this.f;
          var mse = new MemberSelectExpr(tok, th, fields[i]);
          Bpl.Expr surr = new Bpl.IdentifierExpr(tok, localSurrogates[i]);
          surr = CondApplyUnbox(tok, surr, fields[i].Type, mse.Type);
          builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.Eq(etran.TrExpr(mse), surr)));
        }
        CommitAllocatedObject(tok, bplThis, null, builder, etran);

        AddComment(builder, stmt, "divided block after new;");
        TrStmtList(s.BodyProper, builder, locals, etran);
        RemoveDefiniteAssignmentTrackers(s.Body, prevDefiniteAssignmentTrackerCount);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        TrStmtList(s.Body, builder, locals, etran);
        RemoveDefiniteAssignmentTrackers(s.Body, prevDefiniteAssignmentTrackerCount);
      } else if (stmt is IfStmt) {
        AddComment(builder, stmt, "if statement");
        IfStmt s = (IfStmt)stmt;
        Expression guard;
        if (s.Guard == null) {
          guard = null;
        } else {
          guard = s.IsBindingGuard ? AlphaRename((ExistsExpr)s.Guard, "eg$") : s.Guard;
          TrStmt_CheckWellformed(guard, builder, locals, etran, true);
        }
        BoogieStmtListBuilder b = new BoogieStmtListBuilder(this);
        CurrentIdGenerator.Push();
        if (s.IsBindingGuard) {
          var exists = (ExistsExpr)s.Guard;  // the original (that is, not alpha-renamed) guard
          IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, stmt.IsGhost);
        }
        Bpl.StmtList thn = TrStmt2StmtList(b, s.Thn, locals, etran);
        CurrentIdGenerator.Pop();
        Bpl.StmtList els;
        Bpl.IfCmd elsIf = null;
        b = new BoogieStmtListBuilder(this);
        if (s.IsBindingGuard) {
          b.Add(TrAssumeCmd(guard.tok, Bpl.Expr.Not(etran.TrExpr(guard))));
        }
        if (s.Els == null) {
          els = b.Collect(s.Tok);
        } else {
          els = TrStmt2StmtList(b, s.Els, locals, etran);
          if (els.BigBlocks.Count == 1) {
            Bpl.BigBlock bb = els.BigBlocks[0];
            if (bb.LabelName == null && bb.simpleCmds.Count == 0 && bb.ec is Bpl.IfCmd) {
              elsIf = (Bpl.IfCmd)bb.ec;
              els = null;
            }
          }
        }
        builder.Add(new Bpl.IfCmd(stmt.Tok, guard == null || s.IsBindingGuard ? null : etran.TrExpr(guard), thn, elsIf, els));

      } else if (stmt is AlternativeStmt) {
        AddComment(builder, stmt, "alternative statement");
        var s = (AlternativeStmt)stmt;
        var elseCase = Assert(s.Tok, Bpl.Expr.False, "alternative cases fail to cover all possibilties");
        TrAlternatives(s.Alternatives, elseCase, null, builder, locals, etran, stmt.IsGhost);

      } else if (stmt is WhileStmt) {
        AddComment(builder, stmt, "while statement");
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
        var s = (WhileStmt)stmt;
        BodyTranslator bodyTr = null;
        if (s.Body != null) {
          bodyTr = delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            CurrentIdGenerator.Push();
            TrStmt(s.Body, bld, locals, e);
            CurrentIdGenerator.Pop();
          };
        }
        TrLoop(s, s.Guard, bodyTr, builder, locals, etran);
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is AlternativeLoopStmt) {
        AddComment(builder, stmt, "alternative loop statement");
        var s = (AlternativeLoopStmt)stmt;
        var tru = new LiteralExpr(s.Tok, true);
        tru.Type = Type.Bool; // resolve here
        TrLoop(s, tru,
          delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            TrAlternatives(s.Alternatives, null, new Bpl.BreakCmd(s.Tok, null), bld, locals, e, stmt.IsGhost);
          },
          builder, locals, etran);

      } else if (stmt is ForLoopStmt) {
        var s = (ForLoopStmt)stmt;
        AddComment(builder, stmt, "for-loop statement");

        var indexVar = s.LoopIndex;
        var indexVarName = indexVar.AssignUniqueName(currentDeclaration.IdGenerator);
        var dIndex = new IdentifierExpr(indexVar.tok, indexVar);
        var bIndexVar = new Bpl.LocalVariable(indexVar.tok, new Bpl.TypedIdent(indexVar.Tok, indexVarName, TrType(indexVar.Type)));
        locals.Add(bIndexVar);
        var bIndex = new Bpl.IdentifierExpr(indexVar.tok, indexVarName);

        var lo = s.GoingUp ? s.Start : s.End;
        var hi = s.GoingUp ? s.End : s.Start;
        Expression dLo = null;
        Expression dHi = null;
        Bpl.IdentifierExpr bLo = null;
        Bpl.IdentifierExpr bHi = null;
        if (lo != null) {
          var name = indexVarName + "#lo";
          var bLoVar = new Bpl.LocalVariable(lo.tok, new Bpl.TypedIdent(lo.tok, name, Bpl.Type.Int));
          locals.Add(bLoVar);
          bLo = new Bpl.IdentifierExpr(lo.tok, name);
          CheckWellformed(lo, new WFOptions(null, false), locals, builder, etran);
          builder.Add(Bpl.Cmd.SimpleAssign(lo.tok, bLo, etran.TrExpr(lo)));
          dLo = new BoogieWrapper(bLo, lo.Type);
        }
        if (hi != null) {
          var name = indexVarName + "#hi";
          var bHiVar = new Bpl.LocalVariable(hi.tok, new Bpl.TypedIdent(hi.tok, name, Bpl.Type.Int));
          locals.Add(bHiVar);
          bHi = new Bpl.IdentifierExpr(hi.tok, name);
          CheckWellformed(hi, new WFOptions(null, false), locals, builder, etran);
          builder.Add(Bpl.Cmd.SimpleAssign(hi.tok, bHi, etran.TrExpr(hi)));
          dHi = new BoogieWrapper(bHi, hi.Type);
        }

        // check lo <= hi
        if (lo != null && hi != null) {
          builder.Add(Assert(lo.tok, Bpl.Expr.Le(bLo, bHi), "lower bound must not exceed upper bound"));
        }
        // check forall x :: lo <= x <= hi ==> Is(x, typ)
        {
          // The check, if needed, is performed like this:
          //   var x: int;
          //   havoc x;
          //   assume lo <= x <= hi;
          //   assert Is(x, typ);
          var tok = indexVar.tok;
          var name = indexVarName + "#x";
          var xVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, name, Bpl.Type.Int));
          var x = new Bpl.IdentifierExpr(tok, name);
          string msg;
          var cre = GetSubrangeCheck(x, Type.Int, indexVar.Type, out msg);
          if (cre != null) {
            locals.Add(xVar);
            builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr>() { x }));
            builder.Add(new Bpl.AssumeCmd(tok, ForLoopBounds(x, bLo, bHi)));
            builder.Add(Assert(tok, cre, "entire range must be assignable to index variable, but some " + msg));
          }
        }

        // initialize the index variable
        builder.Add(Bpl.Cmd.SimpleAssign(indexVar.tok, bIndex, s.GoingUp ? bLo : bHi));

        // build the guard expression
        Expression guard;
        if (lo == null || hi == null) {
          guard = LiteralExpr.CreateBoolLiteral(s.Tok, true);
        } else {
          guard = Expression.CreateNot(s.Tok, Expression.CreateEq(dIndex, s.GoingUp ? dHi : dLo, indexVar.Type));
        }

        // free invariant lo <= i <= hi
        var freeInvariant = ForLoopBounds(bIndex, bLo, bHi);

        BodyTranslator bodyTr = null;
        if (s.Body != null) {
          bodyTr = delegate(BoogieStmtListBuilder bld, ExpressionTranslator e) {
            CurrentIdGenerator.Push();
            if (!s.GoingUp) {
              bld.Add(Bpl.Cmd.SimpleAssign(s.Tok, bIndex, Bpl.Expr.Sub(bIndex, Bpl.Expr.Literal(1))));
            }
            TrStmt(s.Body, bld, locals, e);
            if (s.GoingUp) {
              bld.Add(Bpl.Cmd.SimpleAssign(s.Tok, bIndex, Bpl.Expr.Add(bIndex, Bpl.Expr.Literal(1))));
            }
            CurrentIdGenerator.Pop();
          };
        }

        TrLoop(s, guard, bodyTr, builder, locals, etran, freeInvariant, s.Decreases.Expressions.Count != 0);

      } else if (stmt is ModifyStmt) {
        AddComment(builder, stmt, "modify statement");
        var s = (ModifyStmt)stmt;
        // check well-formedness of the modifies clauses
        CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
        // check that the modifies is a subset
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, "modify statement may violate context's modifies clause", null);
        // cause the change of the heap according to the given frame
        var suffix = CurrentIdGenerator.FreshId("modify#");
        string modifyFrameName = "$Frame$" + suffix;
        var preModifyHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreModifyHeap$" + suffix, predef.HeapType));
        locals.Add(preModifyHeapVar);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, modifyFrameName);
        if (s.Body == null) {
          var preModifyHeap = new Bpl.IdentifierExpr(s.Tok, preModifyHeapVar);
          // preModifyHeap := $Heap;
          builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preModifyHeap, etran.HeapExpr));
          // havoc $Heap;
          builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
          // assume $HeapSucc(preModifyHeap, $Heap);   OR $HeapSuccGhost
          builder.Add(TrAssumeCmd(s.Tok, HeapSucc(preModifyHeap, etran.HeapExpr, s.IsGhost)));
          // assume nothing outside the frame was changed
          var etranPreLoop = new ExpressionTranslator(this, predef, preModifyHeap);
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          builder.Add(TrAssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
        } else {
          // do the body, but with preModifyHeapVar as the governing frame
          var updatedFrameEtran = new ExpressionTranslator(etran, modifyFrameName);
          TrStmt(s.Body, builder, locals, updatedFrameEtran);
        }
        builder.Add(CaptureState(stmt));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);

        if (s.Kind == ForallStmt.BodyKind.Assign) {
          AddComment(builder, stmt, "forall statement (assign)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (AssignStmt)s.S0;
            var definedness = new BoogieStmtListBuilder(this);
            var updater = new BoogieStmtListBuilder(this);
            DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
            TrForallAssign(s, s0, definedness, updater, locals, etran);
            // All done, so put the two pieces together
            builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, updater.Collect(s.Tok)));
            builder.Add(CaptureState(stmt));
          }

        } else if (s.Kind == ForallStmt.BodyKind.Call) {
          AddComment(builder, stmt, "forall statement (call)");
          Contract.Assert(s.Ens.Count == 0);
          if (s.BoundVars.Count == 0) {
            Contract.Assert(LiteralExpr.IsTrue(s.Range));  // follows from the invariant of ForallStmt
            TrStmt(s.Body, builder, locals, etran);
          } else {
            var s0 = (CallStmt)s.S0;
            if (Attributes.Contains(s.Attributes, "_trustWellformed")) {
              TrForallStmtCall(s.Tok, s.BoundVars, s.Bounds, s.Range, null, s.ForallExpressions, s0, null, builder, locals, etran);
            } else {
              var definedness = new BoogieStmtListBuilder(this);
              DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
              var exporter = new BoogieStmtListBuilder(this);
              TrForallStmtCall(s.Tok, s.BoundVars, s.Bounds, s.Range, null, s.ForallExpressions, s0, definedness, exporter, locals, etran);
              // All done, so put the two pieces together
              builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
            }
            builder.Add(CaptureState(stmt));
          }

        } else if (s.Kind == ForallStmt.BodyKind.Proof) {
          AddComment(builder, stmt, "forall statement (proof)");
          var definedness = new BoogieStmtListBuilder(this);
          var exporter = new BoogieStmtListBuilder(this);
          DefineFuelConstant(stmt.Tok, stmt.Attributes, definedness, etran);
          TrForallProof(s, definedness, exporter, locals, etran);
          // All done, so put the two pieces together
          builder.Add(new Bpl.IfCmd(s.Tok, null, definedness.Collect(s.Tok), null, exporter.Collect(s.Tok)));
          builder.Add(CaptureState(stmt));

        } else {
          Contract.Assert(false);  // unexpected kind
        }
        this.fuelContext = FuelSetting.PopFuelContext();
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
        this.fuelContext = FuelSetting.ExpandFuelContext(stmt.Attributes, stmt.Tok, this.fuelContext, this.reporter);
        DefineFuelConstant(stmt.Tok, stmt.Attributes, builder, etran);
        CurrentIdGenerator.Push();  // put the entire calc statement within its own sub-branch
        if (s.Lines.Count > 0) {
          Bpl.IfCmd ifCmd = null;
          BoogieStmtListBuilder b;
          // if the dangling hint is empty, do not generate anything for the dummy step
          var stepCount = s.Hints.Last().Body.Count == 0 ? s.Steps.Count - 1 : s.Steps.Count;
          // check steps:
          for (int i = stepCount; 0 <= --i; ) {
            b = new BoogieStmtListBuilder(this);
            // assume wf[line<i>]:
            AddComment(b, stmt, "assume wf[lhs]");
            CurrentIdGenerator.Push();
            assertAsAssume = true;
            TrStmt_CheckWellformed(CalcStmt.Lhs(s.Steps[i]), b, locals, etran, false);
            assertAsAssume = false;
            if (s.Steps[i] is BinaryExpr && (((BinaryExpr)s.Steps[i]).ResolvedOp == BinaryExpr.ResolvedOpcode.Imp)) {
              // assume line<i>:
              AddComment(b, stmt, "assume lhs");
              b.Add(TrAssumeCmd(s.Tok, etran.TrExpr(CalcStmt.Lhs(s.Steps[i]))));
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
                TrStmt_CheckWellformed(index, b, locals, etran, false);
                if (index.Type.IsNumericBased(Type.NumericPersuasion.Int)) {
                  b.Add(AssertNS(index.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(index)), "prefix-equality limit must be at least 0"));
                }
              }
              TrStmt_CheckWellformed(CalcStmt.Rhs(s.Steps[i]), b, locals, etran, false);
              bool splitHappened;
              var ss = TrSplitExpr(s.Steps[i], etran, true, out splitHappened);
              // assert step:
              AddComment(b, stmt, "assert line" + i.ToString() + " " + (s.StepOps[i] ?? s.Op).ToString() + " line" + (i + 1).ToString());
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
            b.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
            ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
            CurrentIdGenerator.Pop();
          }
          // check well formedness of the first line:
          b = new BoogieStmtListBuilder(this);
          AddComment(b, stmt, "assert wf[initial]");
          Contract.Assert(s.Result != null); // established by the resolver
          TrStmt_CheckWellformed(CalcStmt.Lhs(s.Result), b, locals, etran, false);
          b.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
          ifCmd = new Bpl.IfCmd(s.Tok, null, b.Collect(s.Tok), ifCmd, null);
          builder.Add(ifCmd);
          // assume result:
          if (s.Steps.Count > 1) {
            builder.Add(TrAssumeCmd(s.Tok, etran.TrExpr(s.Result)));
          }
        }
        CurrentIdGenerator.Pop();
        this.fuelContext = FuelSetting.PopFuelContext();
      } else if (stmt is ConcreteSyntaxStatement) {
        ConcreteSyntaxStatement s = (ConcreteSyntaxStatement)stmt;
        TrStmt(s.ResolvedStatement, builder, locals, etran);
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        TrStmt_CheckWellformed(s.Source, builder, locals, etran, true);
        Bpl.Expr source = etran.TrExpr(s.Source);
        var b = new BoogieStmtListBuilder(this);
        b.Add(TrAssumeCmd(stmt.Tok, Bpl.Expr.False));
        Bpl.StmtList els = b.Collect(stmt.Tok);
        Bpl.IfCmd ifCmd = null;
        foreach (var missingCtor in s.MissingCases) {
          // havoc all bound variables
          b = new BoogieStmtListBuilder(this);
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
          String missingStr = s.Context.FillHole(new IdCtx(new KeyValuePair<string, DatatypeCtor>(missingCtor.Name, missingCtor))).AbstractAllHoles().ToString();
          b.Add(Assert(s.Tok, Bpl.Expr.False, "missing case in match statement: " + missingStr));

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(s.Tok, guard, b.Collect(s.Tok), ifCmd, els);
          els = null;
        }
        for (int i = s.Cases.Count; 0 <= --i; ) {
          var mc = (MatchCaseStmt)s.Cases[i];
          CurrentIdGenerator.Push();
          // havoc all bound variables
          b = new BoogieStmtListBuilder(this);
          List<Variable> newLocals = new List<Variable>();
          Bpl.Expr r = CtorInvocation(mc, s.Source.Type, etran, newLocals, b, s.IsGhost ? NOALLOC : ISALLOC);
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
          var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
          TrStmtList(mc.Body, b, locals, etran);
          RemoveDefiniteAssignmentTrackers(mc.Body, prevDefiniteAssignmentTrackerCount);

          Bpl.Expr guard = Bpl.Expr.Eq(source, r);
          ifCmd = new Bpl.IfCmd(mc.tok, guard, b.Collect(mc.tok), ifCmd, els);
          els = null;
          CurrentIdGenerator.Pop();
        }
        Contract.Assert(ifCmd != null);  // follows from the fact that s.Cases.Count + s.MissingCases.Count != 0.
        builder.Add(ifCmd);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var newLocalIds = new List<Bpl.IdentifierExpr>();
        int i = 0;
        foreach (var local in s.Locals) {
          Bpl.Type varType = TrType(local.Type);
          Bpl.Expr wh = GetWhereClause(local.Tok,
            new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType),
            local.Type, etran, isAllocContext.Var(stmt.IsGhost, local));
          // if needed, register definite-assignment tracking for this local
          var needDefiniteAssignmentTracking = s.Update == null || s.Update is AssignSuchThatStmt;
          if (s.Update is UpdateStmt) {
            // there is an initial assignment, but we need to look out for "*" being that assignment
            var us = (UpdateStmt)s.Update;
            if (i < us.Rhss.Count && us.Rhss[i] is HavocRhs) {
              needDefiniteAssignmentTracking = true;
            }
          }
          if (needDefiniteAssignmentTracking) {
            var defassExpr = AddDefiniteAssignmentTracker(local, locals);
            if (wh != null && defassExpr != null) {
              // make the "where" expression be "defass ==> wh", because we don't want to assume anything
              // before the variable has been assigned (for a variable that needs definite-assignment tracking
              // in the first place)
              wh = BplImp(defassExpr, wh);
            }
          }
          // create the variable itself (now that "wh" may mention the definite-assignment tracker)
          Bpl.LocalVariable var = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType, wh));
          var.Attributes = etran.TrAttributes(local.Attributes, null);
          newLocalIds.Add(new Bpl.IdentifierExpr(local.Tok, var));
          locals.Add(var);
          i++;
        }
        if (s.Update == null) {
          // it is necessary to do a havoc here in order to give the variable the correct allocation state
          builder.Add(new HavocCmd(s.Tok, newLocalIds));
        }
        // processing of "assumption" variables happens after the variable is possibly havocked above
        foreach (var local in s.Locals) {
          if (Attributes.Contains(local.Attributes, "assumption")) {
            Bpl.Type varType = TrType(local.Type);
            builder.Add(new AssumeCmd(local.Tok, new Bpl.IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), varType), new QKeyValue(local.Tok, "assumption_variable_initialization", new List<object>(), null)));
          }
        }
        if (s.Update != null) {
          TrStmt(s.Update, builder, locals, etran);
        }
      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type)));
          locals.Add(bvar);
          var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
          builder.Add(new Bpl.HavocCmd(local.Tok, new List<Bpl.IdentifierExpr> { bIe }));
          Bpl.Expr wh = GetWhereClause(local.Tok, bIe, local.Type, etran, isAllocContext.Var(stmt.IsGhost, local));
          if (wh != null) {
            builder.Add(TrAssumeCmd(local.Tok, wh));
          }
        }
        var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator("let#");
        var pat = s.LHS;
        var rhs = s.RHS;
        var nm = varNameGen.FreshId(string.Format("#{0}#", 0));
        var r = new Bpl.LocalVariable(pat.tok, new Bpl.TypedIdent(pat.tok, nm, TrType(rhs.Type)));
        locals.Add(r);
        var rIe = new Bpl.IdentifierExpr(rhs.tok, r);
        CheckWellformedWithResult(rhs, new WFOptions(null, false, false), rIe, pat.Expr.Type, locals, builder, etran);
        CheckCasePatternShape(pat, rIe, rhs.tok, pat.Expr.Type, builder);
        builder.Add(TrAssumeCmd(pat.tok, Bpl.Expr.Eq(etran.TrExpr(pat.Expr), rIe)));
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
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

    private void GenerateAndCheckGuesses(IToken tok, List<BoundVar> bvars, List<ComprehensionExpr.BoundedPool> bounds, Expression expr, Trigger triggers, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(bvars != null);
      Contract.Requires(bounds != null);
      Contract.Requires(expr != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);

      List<Tuple<List<Tuple<BoundVar, Expression>>, Expression>> partialGuesses = GeneratePartialGuesses(bvars, expr);
      Bpl.Expr w = Bpl.Expr.False;
      foreach (var tup in partialGuesses) {
        var body = etran.TrExpr(tup.Item2);
        Bpl.Expr typeConstraints = Bpl.Expr.True;
        var undetermined = new List<BoundVar>();
        foreach (var be in tup.Item1) {
          if (be.Item2 == null) {
            undetermined.Add(be.Item1);
          } else {
            typeConstraints = BplAnd(typeConstraints, MkIs(etran.TrExpr(be.Item2), be.Item1.Type));
          }
        }
        body = BplAnd(typeConstraints, body);
        if (undetermined.Count != 0) {
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          var bvs = new List<Variable>();
          var typeAntecedent = etran.TrBoundVariables(undetermined, bvs, false, freeOfAlloc);
          body = new Bpl.ExistsExpr(tok, bvs, triggers, BplAnd(typeAntecedent, body));
        }
        w = BplOr(body, w);
      }
      builder.Add(Assert(tok, w, "cannot establish the existence of LHS values that satisfy the such-that predicate"));
    }

    private void IntroduceAndAssignExistentialVars(ExistsExpr exists, BoogieStmtListBuilder builder, BoogieStmtListBuilder builderOutsideIfConstruct, List<Variable> locals, ExpressionTranslator etran, bool isGhost) {
      Contract.Requires(exists != null);
      Contract.Requires(exists.Range == null);
      Contract.Requires(builder != null);
      Contract.Requires(builderOutsideIfConstruct != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      // declare and havoc the bound variables of 'exists' as local variables
      var iesForHavoc = new List<Bpl.IdentifierExpr>();
      foreach (var bv in exists.BoundVars) {
        Bpl.Type varType = TrType(bv.Type);
        Bpl.Expr wh = GetWhereClause(bv.Tok,
          new Bpl.IdentifierExpr(bv.Tok, bv.AssignUniqueName(currentDeclaration.IdGenerator), varType),
          bv.Type, etran, isAllocContext.Var(isGhost, bv));
        Bpl.Variable local = new Bpl.LocalVariable(bv.Tok, new Bpl.TypedIdent(bv.Tok, bv.AssignUniqueName(currentDeclaration.IdGenerator), varType, wh));
        locals.Add(local);
        iesForHavoc.Add(new Bpl.IdentifierExpr(local.tok, local));
      }
      builderOutsideIfConstruct.Add(new Bpl.HavocCmd(exists.tok, iesForHavoc));
      builder.Add(TrAssumeCmd(exists.tok, etran.TrExpr(exists.Term)));
    }

    void TrStmtList(List<Statement> stmts, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(stmts != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      foreach (Statement ss in stmts) {
        for (var l = ss.Labels; l != null; l = l.Next) {
          var heapAt = new Bpl.LocalVariable(ss.Tok, new Bpl.TypedIdent(ss.Tok, "$Heap_at_" + l.Data.AssignUniqueId(CurrentIdGenerator), predef.HeapType));
          locals.Add(heapAt);
          builder.Add(Bpl.Cmd.SimpleAssign(ss.Tok, new Bpl.IdentifierExpr(ss.Tok, heapAt), etran.HeapExpr));
        }
        TrStmt(ss, builder, locals, etran);
        if (ss.Labels != null) {
          builder.AddLabelCmd("after_" + ss.Labels.Data.AssignUniqueId(CurrentIdGenerator));
        }
      }
    }

    /// <summary>
    /// Returns an expression like 'exists' but where the bound variables have been renamed to have
    /// 'prefix' as a prefix to their previous names.
    /// Assumes the expression has been resolved.
    /// </summary>
    public static Expression AlphaRename(ExistsExpr exists, string prefix) {
      Contract.Requires(exists != null);
      Contract.Requires(prefix != null);

      if (exists.SplitQuantifier != null) {
        // TODO: what to do?  Substitute(exists.SplitQuantifierExpression);
      }

      var substMap = new Dictionary<IVariable, Expression>();
      var var4var = new Dictionary<BoundVar, BoundVar>();
      var bvars = new List<BoundVar>();
      foreach (var bv in exists.BoundVars) {
        var newBv = new BoundVar(bv.tok, prefix + bv.Name, bv.Type);
        bvars.Add(newBv);
        var4var.Add(bv, newBv);
        var ie = new IdentifierExpr(newBv.tok, newBv.Name);
        ie.Var = newBv;  // resolve here
        ie.Type = newBv.Type;  // resolve here
        substMap.Add(bv, ie);
      }
      var s = new Substituter(null, substMap, new Dictionary<TypeParameter, Type>());
      var range = exists.Range == null ? null : s.Substitute(exists.Range);
      var term = s.Substitute(exists.Term);
      var attrs = s.SubstAttributes(exists.Attributes);
      var ex = new ExistsExpr(exists.tok, exists.TypeArgs, bvars, range, term, attrs);
      ex.Type = Type.Bool;
      ex.Bounds = s.SubstituteBoundedPoolList(exists.Bounds);
      return ex;
    }

    /// <summary>
    /// Generate:
    ///   havoc Heap \ {this} \ _reads \ _new;
    ///   assume this.Valid();
    ///   assume YieldRequires;
    ///   $_OldIterHeap := Heap;
    /// </summary>
    void YieldHavoc(IToken tok, IteratorDecl iter, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      // havoc Heap \ {this} \ _reads \ _new;
      var th = new ThisExpr(iter);
      var rds = new MemberSelectExpr(tok, th, iter.Member_Reads);
      var nw = new MemberSelectExpr(tok, th, iter.Member_New);
      builder.Add(new Bpl.CallCmd(tok, "$YieldHavoc",
        new List<Bpl.Expr>() { etran.TrExpr(th), etran.TrExpr(rds), etran.TrExpr(nw) },
        new List<Bpl.IdentifierExpr>()));
      // assume YieldRequires;
      foreach (var p in iter.YieldRequires) {
        builder.Add(TrAssumeCmd(tok, etran.TrExpr(p.E)));
      }
      // $_OldIterHeap := Heap;
      builder.Add(Bpl.Cmd.SimpleAssign(tok, new Bpl.IdentifierExpr(tok, "$_OldIterHeap", predef.HeapType), etran.HeapExpr));
    }

    List<Tuple<List<Tuple<BoundVar, Expression>>, Expression>> GeneratePartialGuesses(List<BoundVar> bvars, Expression expression) {
      if (bvars.Count == 0) {
        var tup = new Tuple<List<Tuple<BoundVar, Expression>>, Expression>(new List<Tuple<BoundVar, Expression>>(), expression);
        return new List<Tuple<List<Tuple<BoundVar, Expression>>, Expression>>() { tup };
      }
      var result = new List<Tuple<List<Tuple<BoundVar, Expression>>, Expression>>();
      var x = bvars[0];
      var otherBvars = bvars.GetRange(1, bvars.Count - 1);
      foreach (var tup in GeneratePartialGuesses(otherBvars, expression)) {
        // in the special case that x does not even occur in expression (and we know the type has a value for x), we can just ignore x
        if (!ContainsFreeVariable(tup.Item2, false, x) && x.Type.KnownToHaveToAValue(x.IsGhost)) {
          result.Add(tup);
          continue;
        }
        // one possible result is to quantify over all the variables
        var vs = new List<Tuple<BoundVar, Expression>>() { new Tuple<BoundVar, Expression>(x, null) };
        vs.AddRange(tup.Item1);
        result.Add(new Tuple<List<Tuple<BoundVar, Expression>>, Expression>(vs, tup.Item2));
        // other possibilities involve guessing a value for x
        foreach (var guess in GuessWitnesses(x, tup.Item2)) {
          var g = Substitute(tup.Item2, x, guess);
          vs = new List<Tuple<BoundVar, Expression>>() { new Tuple<BoundVar, Expression>(x, guess) };
          AddRangeSubst(vs, tup.Item1, x, guess);
          result.Add(new Tuple<List<Tuple<BoundVar, Expression>>, Expression>(vs, g));
        }
      }
      return result;
    }

    private void AddRangeSubst(List<Tuple<BoundVar, Expression>> vs, List<Tuple<BoundVar, Expression>> aa, IVariable v, Expression e) {
      Contract.Requires(vs != null);
      Contract.Requires(aa != null);
      Contract.Requires(v != null);
      Contract.Requires(e != null);
      foreach (var be in aa) {
        if (be.Item2 == null) {
          vs.Add(be);
        } else {
          vs.Add(new Tuple<BoundVar, Expression>(be.Item1, Substitute(be.Item2, v, e)));
        }
      }
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
      } else if (xType is CharType) {
        // TODO: something could be done for character literals
      } else if (xType.IsBitVectorType) {
        // TODO: something could be done for bitvectors
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
            v.Type = xType;  // resolve here
            yield return v;
          }
        }
      } else if (xType is SetType) {
        var empty = new SetDisplayExpr(x.tok, ((SetType)xType).Finite, new List<Expression>());
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
      } else if (xType.IsNumericBased(Type.NumericPersuasion.Int)) {
        var lit = new LiteralExpr(x.tok, 0);
        lit.Type = xType;  // resolve here
        yield return lit;
      } else if (xType.IsNumericBased(Type.NumericPersuasion.Real)) {
        var lit = new LiteralExpr(x.tok, BaseTypes.BigDec.ZERO);
        lit.Type = xType;  // resolve here
        yield return lit;
      }

      var bounds = Resolver.DiscoverAllBounds_SingleVar(x, expr);
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
        } else if (bound is ComprehensionExpr.MultiSetBoundedPool) {
          var st = ((ComprehensionExpr.MultiSetBoundedPool)bound).MultiSet.Resolved;
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
        } else if (bound is ComprehensionExpr.ExactBoundedPool) {
          yield return ((ComprehensionExpr.ExactBoundedPool)bound).E;
        }
      }
    }

    /// <summary>
    /// Return a zero-equivalent value for "typ", or return null (for any reason whatsoever).
    /// </summary>
    Expression Zero(IToken tok, Type typ) {
      Contract.Requires(tok != null);
      Contract.Requires(typ != null);
      typ = typ.NormalizeExpand();
      if (typ is BoolType) {
        return Expression.CreateBoolLiteral(tok, false);
      } else if (typ is CharType) {
        var z = new CharLiteralExpr(tok, CharType.DefaultValue.ToString());
        z.Type = Type.Char;  // resolve here
        return z;
      } else if (typ.IsNumericBased(Type.NumericPersuasion.Int)) {
        return Expression.CreateIntLiteral(tok, 0);
      } else if (typ.IsNumericBased(Type.NumericPersuasion.Real)) {
        return Expression.CreateRealLiteral(tok, BaseTypes.BigDec.ZERO);
      } else if (typ.IsBigOrdinalType) {
        return Expression.CreateNatLiteral(tok, 0, Type.BigOrdinal);
      } else if (typ.IsBitVectorType) {
        var z = new LiteralExpr(tok, 0);
        z.Type = typ;
        return z;
      } else if (typ.IsRefType) {
        var z = new LiteralExpr(tok);  // null
        z.Type = typ;
        return z;
      } else if (typ.IsDatatype) {
        return null;  // this can be improved
      } else if (typ is SetType) {
        var empty = new SetDisplayExpr(tok, ((SetType)typ).Finite, new List<Expression>());
        empty.Type = typ;
        return empty;
      } else if (typ is MultiSetType) {
        var empty = new MultiSetDisplayExpr(tok, new List<Expression>());
        empty.Type = typ;
        return empty;
      } else if (typ is SeqType) {
        var empty = new SeqDisplayExpr(tok, new List<Expression>());
        empty.Type = typ;
        return empty;
      } else if (typ is MapType) {
        var empty = new MapDisplayExpr(tok, ((MapType)typ).Finite, new List<ExpressionPair>());
        empty.Type = typ;
        return empty;
      } else if (typ is ArrowType) {
        // TODO: do better than just returning null
        return null;
      } else if (typ.IsOpaqueType || typ.IsInternalTypeSynonym) {
        return null;
      } else {
        Contract.Assume(false);  // unexpected type
        return null;
      }
    }

    void TrForallAssign(ForallStmt s, AssignStmt s0,
      BoogieStmtListBuilder definedness, BoogieStmtListBuilder updater, List<Variable> locals, ExpressionTranslator etran) {
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
      //       assert E(x,y) != E(x',y') || G(x,y) == G(x',y');
      //     (b)
      //       assert !( A(x,y)==A(x',y') && I0(x,y)==I0(x',y') && I1(x,y)==I1(x',y') && ... ) || G(x,y) == G(x',y');
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
      definedness.Add(TrAssumeCmd(s.Range.tok, etran.TrExpr(range)));

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
        CheckSubrange(r.Tok, translatedRhs, rhs.Type, lhsType, definedness);
        if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          Check_NewRestrictions(fse.tok, obj, field, translatedRhs, definedness, etran);
        }
      }

      // check for duplicate LHSs
      if (s0.Rhs is ExprRhs) {  // if Rhs denotes a havoc, then no duplicate check is performed
        var substMapPrime = SetupBoundVarsAsLocals(s.BoundVars, definedness, locals, etran);
        var lhsPrime = Substitute(s0.Lhs.Resolved, null, substMapPrime);
        range = Substitute(s.Range, null, substMapPrime);
        definedness.Add(TrAssumeCmd(range.tok, etran.TrExpr(range)));
        // assume !(x == x' && y == y');
        Bpl.Expr eqs = Bpl.Expr.True;
        foreach (var bv in s.BoundVars) {
          var x = substMap[bv];
          var xPrime = substMapPrime[bv];
          // TODO: in the following line, is the term equality okay, or does it have to include things like Set#Equal sometimes too?
          eqs = BplAnd(eqs, Bpl.Expr.Eq(etran.TrExpr(x), etran.TrExpr(xPrime)));
        }
        definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.Not(eqs)));
        Bpl.Expr objPrime, FPrime;
        GetObjFieldDetails(lhsPrime, etran, out objPrime, out FPrime);
        var Rhs = ((ExprRhs)s0.Rhs).Expr;
        var rhs = etran.TrExpr(Substitute(Rhs, null, substMap));
        var rhsPrime = etran.TrExpr(Substitute(Rhs, null, substMapPrime));
        definedness.Add(Assert(s0.Tok,
          Bpl.Expr.Or(
            Bpl.Expr.Or(Bpl.Expr.Neq(obj, objPrime), Bpl.Expr.Neq(F, FPrime)),
            Bpl.Expr.Eq(rhs, rhsPrime)),
          "left-hand sides for different forall-statement bound variables may refer to the same location"));
      }

      definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the translation of the update itself

      Bpl.IdentifierExpr prevHeap = GetPrevHeapVar_IdExpr(s.Tok, locals);
      var prevEtran = new ExpressionTranslator(this, predef, prevHeap);
      updater.Add(Bpl.Cmd.SimpleAssign(s.Tok, prevHeap, etran.HeapExpr));
      updater.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { (Bpl.IdentifierExpr/*TODO: this cast is rather dubious*/)etran.HeapExpr }));
      updater.Add(TrAssumeCmd(s.Tok, HeapSucc(prevHeap, etran.HeapExpr)));

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
      List<bool> freeOfAlloc = null;
      if (FrugalHeapUseX) {
        freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(s.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
      }
      List<Variable> xBvars = new List<Variable>();
      var xBody = etran.TrBoundVariables(s.BoundVars, xBvars, false, freeOfAlloc);
      xBody = BplAnd(xBody, prevEtran.TrExpr(s.Range));
      Bpl.Expr xObj, xField;
      GetObjFieldDetails(s0.Lhs.Resolved, prevEtran, out xObj, out xField);
      xBody = BplAnd(xBody, Bpl.Expr.Eq(o, xObj));
      xBody = BplAnd(xBody, Bpl.Expr.Eq(f, xField));
      //TRIG (exists k#2: int :: (k#2 == LitInt(0 - 3) || k#2 == LitInt(4)) && $o == read($prevHeap, this, _module.MyClass.arr) && $f == MultiIndexField(IndexField(i#0), j#0))
      Bpl.Expr xObjField = new Bpl.ExistsExpr(s.Tok, xBvars, xBody);  // LL_TRIGGER
      Bpl.Expr body = Bpl.Expr.Or(Bpl.Expr.Eq(heapOF, oldHeapOF), xObjField);
      var tr = new Trigger(s.Tok, true, new List<Expr>() { heapOF });
      Bpl.Expr qq = new Bpl.ForallExpr(s.Tok, new List<TypeVariable> { alpha }, new List<Variable> { oVar, fVar }, null, tr, body);
      updater.Add(TrAssumeCmd(s.Tok, qq));

      if (s.ForallExpressions != null) {
        foreach (ForallExpr expr in s.ForallExpressions) {
          BinaryExpr term = (BinaryExpr)expr.Term;
          Contract.Assert(term != null);
          var e0 = ((BinaryExpr)term).E0.Resolved;
          var e1 = ((BinaryExpr)term).E1;
          qq = TrForall_NewValueAssumption(expr.tok, expr.BoundVars, expr.Bounds, expr.Range, e0, e1, expr.Attributes, etran, prevEtran);
          updater.Add(TrAssumeCmd(s.Tok, qq));
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
    private Bpl.Expr TrForall_NewValueAssumption(IToken tok, List<BoundVar> boundVars, List<ComprehensionExpr.BoundedPool> bounds, Expression range, Expression lhs, Expression rhs, Attributes attributes, ExpressionTranslator etran, ExpressionTranslator prevEtran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(!FrugalHeapUseX || bounds != null);
      Contract.Requires(range != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(etran != null);
      Contract.Requires(prevEtran != null);

      List<bool> freeOfAlloc = null;
      if (FrugalHeapUseX) {
        freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
      }
      var xBvars = new List<Variable>();
      Bpl.Expr xAnte = etran.TrBoundVariables(boundVars, xBvars, false, freeOfAlloc);
      xAnte = BplAnd(xAnte, prevEtran.TrExpr(range));
      var g = prevEtran.TrExpr(rhs);
      Bpl.Expr obj, field;
      GetObjFieldDetails(lhs, prevEtran, out obj, out field);
      var xHeapOF = ExpressionTranslator.ReadHeap(tok, etran.HeapExpr, obj, field);

      Type lhsType = lhs is MemberSelectExpr ? ((MemberSelectExpr)lhs).Type : null;
      g = CondApplyBox(rhs.tok, g, rhs.Type, lhsType);

      Bpl.Trigger tr = null;
      var argsEtran = etran.WithNoLits();
      foreach (var aa in attributes.AsEnumerable()) {
        if (aa.Name == "trigger") {
          List<Bpl.Expr> tt = new List<Bpl.Expr>();
          foreach (var arg in aa.Args) {
            if (arg == lhs) {
              tt.Add(xHeapOF);
            } else {
              tt.Add(argsEtran.TrExpr(arg));
            }
          }
          tr = new Bpl.Trigger(tok, true, tt, tr);
        }
      }
      return new Bpl.ForallExpr(tok, xBvars, tr, Bpl.Expr.Imp(xAnte, Bpl.Expr.Eq(xHeapOF, g)));
    }

    delegate Bpl.Expr ExpressionConverter(Dictionary<IVariable, Expression> substMap, ExpressionTranslator etran);

    void TrForallStmtCall(IToken tok, List<BoundVar> boundVars, List<ComprehensionExpr.BoundedPool> bounds, Expression range, ExpressionConverter additionalRange, List<Expression> forallExpressions, CallStmt s0,
      BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(boundVars != null);
      Contract.Requires(bounds != null);
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
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          List<Variable> bvars = new List<Variable>();
          var ante = etran.TrBoundVariables(boundVars, bvars, true, freeOfAlloc);
          locals.AddRange(bvars);
          var havocIds = new List<Bpl.IdentifierExpr>();
          foreach (Bpl.Variable bv in bvars) {
            havocIds.Add(new Bpl.IdentifierExpr(tok, bv));
          }
          definedness.Add(new Bpl.HavocCmd(tok, havocIds));
          definedness.Add(TrAssumeCmd(tok, ante));
        }
        TrStmt_CheckWellformed(range, definedness, locals, etran, false);
        definedness.Add(TrAssumeCmd(range.tok, etran.TrExpr(range)));
        if (additionalRange != null) {
          var es = additionalRange(new Dictionary<IVariable, Expression>(), etran);
          definedness.Add(TrAssumeCmd(es.tok, es));
        }

        TrStmt(s0, definedness, locals, etran);

        definedness.Add(TrAssumeCmd(tok, Bpl.Expr.False));
      }

      // Now for the other branch, where the postcondition of the call is exported.
      {
        var initHeapVar = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, CurrentIdGenerator.FreshId("$initHeapForallStmt#"), predef.HeapType));
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
            exporter.Add(TrAssumeCmd(tok, tri.Expr));
          }
        }
        if (codeContext is IteratorDecl) {
          var iter = (IteratorDecl)codeContext;
          RecordNewObjectsIn_New(tok, iter, initHeap, heapIdExpr, exporter, locals, etran);
        }

        // Note, in the following, we need to do a bit of a song and dance.  The actual arguments of the
        // call should be translated using "initEtran", whereas the method postcondition should be translated
        // using "callEtran".  To accomplish this, we translate the argument and then tuck the resulting
        // Boogie expressions into BoogieExprWrappers that are used in the DafnyExpr-to-DafnyExpr substitution.
        // TODO
        Bpl.Expr qq;
        var bvars = new List<Variable>();
        Dictionary<IVariable, Expression> substMap;
        Bpl.Trigger antitriggerBoundVarTypes;
        Bpl.Expr ante;
        var argsSubstMap = new Dictionary<IVariable, Expression>();  // maps formal arguments to actuals
        Contract.Assert(s0.Method.Ins.Count == s0.Args.Count);
        var callEtran = new ExpressionTranslator(this, predef, etran.HeapExpr, initHeap);
        Bpl.Expr post = Bpl.Expr.True;
        Bpl.Trigger tr;
        if (forallExpressions != null) {
          // tranlate based on the forallExpressions since the triggers are computed based on it already.
          QuantifierExpr expr = (QuantifierExpr)forallExpressions[0];
          while (expr.SplitQuantifier != null) {
            expr = (QuantifierExpr)expr.SplitQuantifierExpression;
          }
          boundVars = expr.BoundVars;
          ante = initEtran.TrBoundVariablesRename(boundVars, bvars, out substMap, out antitriggerBoundVarTypes);
          ante = BplAnd(ante, initEtran.TrExpr(Substitute(expr.Range, null, substMap)));
          if (additionalRange != null) {
            ante = BplAnd(ante, additionalRange(substMap, initEtran));
          }
          tr = TrTrigger(callEtran, expr.Attributes, expr.tok, bvars, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());
          post = callEtran.TrExpr(Substitute(expr.Term, null, substMap));
        } else {
          ante = initEtran.TrBoundVariablesRename(boundVars, bvars, out substMap, out antitriggerBoundVarTypes);
          for (int i = 0; i < s0.Method.Ins.Count; i++) {
            var arg = Substitute(s0.Args[i], null, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());  // substitute the renamed bound variables for the declared ones
            argsSubstMap.Add(s0.Method.Ins[i], new BoogieWrapper(initEtran.TrExpr(arg), s0.Args[i].Type));
          }
          ante = BplAnd(ante, initEtran.TrExpr(Substitute(range, null, substMap)));
          if (additionalRange != null) {
            ante = BplAnd(ante, additionalRange(substMap, initEtran));
          }
          var receiver = new BoogieWrapper(initEtran.TrExpr(Substitute(s0.Receiver, null, substMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents())), s0.Receiver.Type);
          foreach (var ens in s0.Method.Ens) {
            var p = Substitute(ens.E, receiver, argsSubstMap, s0.MethodSelect.TypeArgumentSubstitutionsWithParents());  // substitute the call's actuals for the method's formals
            post = BplAnd(post, callEtran.TrExpr(p));
          }
          tr = antitriggerBoundVarTypes;
        }

        // TRIG (forall $ih#s0#0: Seq Box :: $Is($ih#s0#0, TSeq(TChar)) && $IsAlloc($ih#s0#0, TSeq(TChar), $initHeapForallStmt#0) && Seq#Length($ih#s0#0) != 0 && Seq#Rank($ih#s0#0) < Seq#Rank(s#0) ==> (forall i#2: int :: true ==> LitInt(0) <= i#2 && i#2 < Seq#Length($ih#s0#0) ==> char#ToInt(_module.CharChar.MinChar($LS($LZ), $Heap, this, $ih#s0#0)) <= char#ToInt($Unbox(Seq#Index($ih#s0#0, i#2)): char)))
        // TRIG (forall $ih#pat0#0: Seq Box, $ih#a0#0: Seq Box :: $Is($ih#pat0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#pat0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && $Is($ih#a0#0, TSeq(_module._default.Same0$T)) && $IsAlloc($ih#a0#0, TSeq(_module._default.Same0$T), $initHeapForallStmt#0) && Seq#Length($ih#pat0#0) <= Seq#Length($ih#a0#0) && Seq#SameUntil($ih#pat0#0, $ih#a0#0, Seq#Length($ih#pat0#0)) && (Seq#Rank($ih#pat0#0) < Seq#Rank(pat#0) || (Seq#Rank($ih#pat0#0) == Seq#Rank(pat#0) && Seq#Rank($ih#a0#0) < Seq#Rank(a#0))) ==> _module.__default.IsRelaxedPrefixAux(_module._default.Same0$T, $LS($LZ), $Heap, $ih#pat0#0, $ih#a0#0, LitInt(1)))'
        // TRIG (forall $ih#m0#0: DatatypeType, $ih#n0#0: DatatypeType :: $Is($ih#m0#0, Tclass._module.Nat()) && $IsAlloc($ih#m0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && $Is($ih#n0#0, Tclass._module.Nat()) && $IsAlloc($ih#n0#0, Tclass._module.Nat(), $initHeapForallStmt#0) && Lit(true) && (DtRank($ih#m0#0) < DtRank(m#0) || (DtRank($ih#m0#0) == DtRank(m#0) && DtRank($ih#n0#0) < DtRank(n#0))) ==> _module.__default.mult($LS($LZ), $Heap, $ih#m0#0, _module.__default.plus($LS($LZ), $Heap, $ih#n0#0, $ih#n0#0)) == _module.__default.mult($LS($LZ), $Heap, _module.__default.plus($LS($LZ), $Heap, $ih#m0#0, $ih#m0#0), $ih#n0#0))
        qq = new Bpl.ForallExpr(tok, bvars, tr, Bpl.Expr.Imp(ante, post));  // TODO: Add a SMART_TRIGGER here.  If we can't find one, abort the attempt to do induction automatically
        exporter.Add(TrAssumeCmd(tok, qq));
      }
    }

    void RecordNewObjectsIn_New(IToken tok, IteratorDecl iter, Bpl.Expr initHeap, Bpl.IdentifierExpr currentHeap,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(iter != null);
      Contract.Requires(initHeap != null);
      Contract.Requires(currentHeap != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      // Add all newly allocated objects to the set this._new
      var updatedSet = new Bpl.LocalVariable(iter.tok, new Bpl.TypedIdent(iter.tok, CurrentIdGenerator.FreshId("$iter_newUpdate"), predef.SetType(iter.tok, true, predef.BoxType)));
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

    void TrForallProof(ForallStmt s, BoogieStmtListBuilder definedness, BoogieStmtListBuilder exporter, List<Variable> locals, ExpressionTranslator etran) {
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
      //     assume (forall x,y :: Range(x,y) ==> Post(x,y));
      //   }

      if (s.BoundVars.Count != 0) {
        // Note, it would be nicer (and arguably more appropriate) to do a SetupBoundVarsAsLocals
        // here (rather than a TrBoundVariables).  However, there is currently no way to apply
        // a substMap to a statement (in particular, to s.Body), so that doesn't work here.
        List<bool> freeOfAlloc = null;
        if (FrugalHeapUseX) {
          freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(s.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
        }
        var bVars = new List<Variable>();
        var typeAntecedent = etran.TrBoundVariables(s.BoundVars, bVars, true, freeOfAlloc);
        locals.AddRange(bVars);
        var havocIds = new List<Bpl.IdentifierExpr>();
        foreach (Bpl.Variable bv in bVars) {
          havocIds.Add(new Bpl.IdentifierExpr(s.Tok, bv));
        }
        definedness.Add(new Bpl.HavocCmd(s.Tok, havocIds));
        definedness.Add(TrAssumeCmd(s.Tok, typeAntecedent));
      }
      TrStmt_CheckWellformed(s.Range, definedness, locals, etran, false);
      definedness.Add(TrAssumeCmd(s.Range.tok, etran.TrExpr(s.Range)));

      if (s.Body != null) {
        TrStmt(s.Body, definedness, locals, etran);

        // check that postconditions hold
        foreach (var ens in s.Ens) {

          bool splitHappened;  // we actually don't care
          foreach (var split in TrSplitExpr(ens.E, etran, true, out splitHappened)) {
            if (split.IsChecked) {
              definedness.Add(Assert(split.E.tok, split.E, "possible violation of postcondition of forall statement"));
            }
          }
        }
      }

      definedness.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));

      // Now for the other branch, where the ensures clauses are exported.
      // If the forall body has side effect such as call to a reveal function,
      // it needs to be exported too.
      var se = s.Body == null ? Bpl.Expr.True : TrFunctionSideEffect(s.Body, etran);
      var substMap = new Dictionary<IVariable, Expression>();
      var p = Substitute(s.ForallExpressions[0], null, substMap);
      var qq = etran.TrExpr(p);
      if (s.BoundVars.Count != 0) {
        exporter.Add(TrAssumeCmd(s.Tok, BplAnd(se, qq)));
      } else {
        exporter.Add(TrAssumeCmd(s.Tok, BplAnd(se, ((Bpl.ForallExpr)qq).Body)));
      }
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
        var idx = etran.TrExpr(sel.E0);
        idx = ConvertExpression(sel.E0.tok, idx, sel.E0.Type, Type.Int);
        F = FunctionCall(sel.tok, BuiltinFunction.IndexField, null, idx);
        description = "an array element";
      } else {
        MultiSelectExpr mse = (MultiSelectExpr)lhs;
        obj = etran.TrExpr(mse.Array);
        F = etran.GetArrayIndexFieldName(mse.tok, mse.Indices);
        description = "an array element";
      }
      return description;
    }

    Bpl.AssumeCmd TrAssumeCmd(IToken tok, Bpl.Expr expr, Bpl.QKeyValue attributes = null) {
      var lit = RemoveLit(expr);
      return attributes == null ? new Bpl.AssumeCmd(tok, lit) : new Bpl.AssumeCmd(tok, lit, attributes);
    }

    Bpl.AssertCmd TrAssertCmd(IToken tok, Bpl.Expr expr, Bpl.QKeyValue attributes = null) {
      var lit = RemoveLit(expr);
      return attributes == null ? new Bpl.AssertCmd(tok, lit) : new Bpl.AssertCmd(tok, lit, attributes);
    }

    delegate void BodyTranslator(BoogieStmtListBuilder builder, ExpressionTranslator etran);


    void TrLoop(LoopStmt s, Expression Guard, BodyTranslator/*?*/ bodyTr,
                BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
                Bpl.Expr freeInvariant = null, bool includeTerminationCheck = true) {
      Contract.Requires(s != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var suffix = CurrentIdGenerator.FreshId("loop#");

      var theDecreases = s.Decreases.Expressions;

      Bpl.LocalVariable preLoopHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$PreLoopHeap$" + suffix, predef.HeapType));
      locals.Add(preLoopHeapVar);
      Bpl.IdentifierExpr preLoopHeap = new Bpl.IdentifierExpr(s.Tok, preLoopHeapVar);
      ExpressionTranslator etranPreLoop = new ExpressionTranslator(this, predef, preLoopHeap);
      ExpressionTranslator updatedFrameEtran;
      string loopFrameName = "$Frame$" + suffix;
      if (s.Mod.Expressions != null) {
        updatedFrameEtran = new ExpressionTranslator(etran, loopFrameName);
      } else {
        updatedFrameEtran = etran;
      }

      if (s.Mod.Expressions != null) { // check well-formedness and that the modifies is a subset
        CheckFrameWellFormed(new WFOptions(), s.Mod.Expressions, locals, builder, etran);
        CheckFrameSubset(s.Tok, s.Mod.Expressions, null, null, etran, builder, "loop modifies clause may violate context's modifies clause", null);
        DefineFrame(s.Tok, s.Mod.Expressions, builder, locals, loopFrameName);
      }
      builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, preLoopHeap, etran.HeapExpr));

      var daTrackersMonotonicity = new List<Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>>();
      foreach (var dat in definiteAssignmentTrackers.Values) {  // TODO: the order is non-deterministic and may change between invocations of Dafny
        var preLoopDat = new Bpl.LocalVariable(dat.tok, new Bpl.TypedIdent(dat.tok, "preLoop$" + suffix + "$" + dat.Name, dat.Type));
        locals.Add(preLoopDat);
        var ie = new Bpl.IdentifierExpr(s.Tok, preLoopDat);
        daTrackersMonotonicity.Add(new Tuple<Bpl.IdentifierExpr, Bpl.IdentifierExpr>(ie, dat));
        builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, ie, dat));
      }

      List<Bpl.Expr> initDecr = null;
      if (!Contract.Exists(theDecreases, e => e is WildcardExpr)) {
        initDecr = RecordDecreasesValue(theDecreases, builder, locals, etran, "$decr_init$" + suffix);
      }

      // The variable w is used to coordinate the definedness checking of the loop invariant.
      // It is also used for body-less loops to turn off invariant checking after the generated body.
      Bpl.LocalVariable wVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, "$w$" + suffix, Bpl.Type.Bool));
      Bpl.IdentifierExpr w = new Bpl.IdentifierExpr(s.Tok, wVar);
      locals.Add(wVar);
      // havoc w;
      builder.Add(new Bpl.HavocCmd(s.Tok, new List<Bpl.IdentifierExpr> { w }));

      List<Bpl.PredicateCmd> invariants = new List<Bpl.PredicateCmd>();
      if (freeInvariant != null) {
        invariants.Add(new Bpl.AssumeCmd(freeInvariant.tok, freeInvariant));
      }
      BoogieStmtListBuilder invDefinednessBuilder = new BoogieStmtListBuilder(this);
      foreach (AttributedExpression loopInv in s.Invariants) {
        string errorMessage = CustomErrorMessage(loopInv.Attributes);
        TrStmt_CheckWellformed(loopInv.E, invDefinednessBuilder, locals, etran, false);
        invDefinednessBuilder.Add(TrAssumeCmd(loopInv.E.tok, etran.TrExpr(loopInv.E)));

        invariants.Add(TrAssumeCmd(loopInv.E.tok, Bpl.Expr.Imp(w, CanCallAssumption(loopInv.E, etran))));
        bool splitHappened;
        var ss = TrSplitExpr(loopInv.E, etran, false, out splitHappened);
        if (!splitHappened) {
          var wInv = Bpl.Expr.Imp(w, etran.TrExpr(loopInv.E));
          invariants.Add(Assert(loopInv.E.tok, wInv, errorMessage??"loop invariant violation"));
        } else {
          foreach (var split in ss) {
            var wInv = Bpl.Expr.Binary(split.E.tok, BinaryOperator.Opcode.Imp, w, split.E);
            if (split.IsChecked) {
              invariants.Add(Assert(split.E.tok, wInv, errorMessage??"loop invariant violation"));  // TODO: it would be fine to have this use {:subsumption 0}
            } else {
              invariants.Add(TrAssumeCmd(split.E.tok, wInv));
            }
          }
        }
      }
      // check definedness of decreases clause
      foreach (Expression e in theDecreases) {
        TrStmt_CheckWellformed(e, invDefinednessBuilder, locals, etran, true);
      }
      if (codeContext is IMethodCodeContext) {
        var modifiesClause = ((IMethodCodeContext)codeContext).Modifies.Expressions;
        if (codeContext is IteratorDecl) {
          // add "this" to the explicit modifies clause
          var explicitModifies = modifiesClause;
          modifiesClause = new List<FrameExpression>();
          modifiesClause.Add(new FrameExpression(s.Tok, new ThisExpr((IteratorDecl)codeContext), null));
          modifiesClause.AddRange(explicitModifies);
        }
        // include boilerplate invariants
        foreach (BoilerplateTriple tri in GetTwoStateBoilerplate(s.Tok, modifiesClause, s.IsGhost, etranPreLoop, etran, etran.Old)) {
          if (tri.IsFree) {
            invariants.Add(TrAssumeCmd(s.Tok, tri.Expr));
          } else {
            Contract.Assert(tri.ErrorMessage != null);  // follows from BoilerplateTriple invariant
            invariants.Add(Assert(s.Tok, tri.Expr, tri.ErrorMessage));
          }
        }
        // add a free invariant which says that the heap hasn't changed outside of the modifies clause.
        invariants.Add(TrAssumeCmd(s.Tok, FrameConditionUsingDefinedFrame(s.Tok, etranPreLoop, etran, updatedFrameEtran)));
        // for iterators, add "fresh(_new)" as an invariant
        if (codeContext is IteratorDecl iter) {
          var th = new ThisExpr(iter);
          var thisDotNew = new MemberSelectExpr(s.Tok, th, iter.Member_New);
          var fr = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Fresh, thisDotNew);
          fr.Type = Type.Bool;
          invariants.Add(TrAssertCmd(s.Tok, etran.TrExpr(fr)));
        }
      }

      // include a free invariant that says that all definite-assignment trackers have only become more "true"
      foreach (var pair in daTrackersMonotonicity) {
        Bpl.Expr monotonic = Bpl.Expr.Imp(pair.Item1, pair.Item2);
        invariants.Add(TrAssumeCmd(s.Tok, monotonic));
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
        invariants.Add(TrAssumeCmd(s.Tok, decrCheck));
      }

      var loopBodyBuilder = new BoogieStmtListBuilder(this);
      loopBodyBuilder.Add(CaptureState(s.Tok, true, "after some loop iterations"));

      // As the first thing inside the loop, generate:  if (!w) { CheckWellformed(inv); assume false; }
      invDefinednessBuilder.Add(TrAssumeCmd(s.Tok, Bpl.Expr.False));
      loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, Bpl.Expr.Not(w), invDefinednessBuilder.Collect(s.Tok), null, null));

      // Generate:  CheckWellformed(guard); if (!guard) { break; }
      // but if this is a body-less loop, put all of that inside:  if (*) { ... }
      // Without this, Boogie's abstract interpreter may figure out that the loop guard is always false
      // on entry to the loop, and then Boogie wouldn't consider this a loop at all. (See also comment
      // in methods GuardAlwaysHoldsOnEntry_BodyLessLoop and GuardAlwaysHoldsOnEntry_LoopWithBody in
      // Test/dafny0/DirtyLoops.dfy.)
      var isBodyLessLoop = s is OneBodyLoopStmt && ((OneBodyLoopStmt)s).BodySurrogate != null;
      var whereToBuildLoopGuard = isBodyLessLoop ? new BoogieStmtListBuilder(this) : loopBodyBuilder;
      Bpl.Expr guard = null;
      if (Guard != null) {
        TrStmt_CheckWellformed(Guard, whereToBuildLoopGuard, locals, etran, true);
        guard = Bpl.Expr.Not(etran.TrExpr(Guard));
      }
      var guardBreak = new BoogieStmtListBuilder(this);
      guardBreak.Add(new Bpl.BreakCmd(s.Tok, null));
      whereToBuildLoopGuard.Add(new Bpl.IfCmd(s.Tok, guard, guardBreak.Collect(s.Tok), null, null));
      if (isBodyLessLoop) {
        loopBodyBuilder.Add(new Bpl.IfCmd(s.Tok, null, whereToBuildLoopGuard.Collect(s.Tok), null, null));
      }

      if (bodyTr != null) {
        // termination checking
        if (Contract.Exists(theDecreases, e => e is WildcardExpr)) {
          // omit termination checking for this loop
          bodyTr(loopBodyBuilder, updatedFrameEtran);
        } else {
          List<Bpl.Expr> oldBfs = RecordDecreasesValue(theDecreases, loopBodyBuilder, locals, etran, "$decr$" + suffix);
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
          if (includeTerminationCheck) {
            AddComment(loopBodyBuilder, s, "loop termination check");
            Bpl.Expr decrCheck = DecreasesCheck(toks, types, types, decrs, oldBfs, loopBodyBuilder, " at end of loop iteration", false, false);
            string msg;
            if (s.InferredDecreases) {
              msg = "cannot prove termination; try supplying a decreases clause for the loop";
            } else {
              msg = "decreases expression might not decrease";
            }
            loopBodyBuilder.Add(Assert(s.Tok, decrCheck, msg));
          }
        }
      } else if (isBodyLessLoop) {
        var bodySurrogate = ((OneBodyLoopStmt)s).BodySurrogate;
        // This is a body-less loop. Havoc the targets and then set w to false, to make the loop-invariant
        // maintenance check vaccuous.
        var bplTargets = bodySurrogate.LocalLoopTargets.ConvertAll(v => TrVar(s.Tok, v));
        if (bodySurrogate.UsesHeap) {
          bplTargets.Add((Bpl.IdentifierExpr /*TODO: this cast is rather dubious*/)etran.HeapExpr);
        }
        loopBodyBuilder.Add(new Bpl.HavocCmd(s.Tok, bplTargets));
        loopBodyBuilder.Add(Bpl.Cmd.SimpleAssign(s.Tok, w, Bpl.Expr.False));
      }
      // Finally, assume the well-formedness of the invariant (which has been checked once and for all above), so that the check
      // of invariant-maintenance can use the appropriate canCall predicates.
      foreach (AttributedExpression loopInv in s.Invariants) {
        loopBodyBuilder.Add(TrAssumeCmd(loopInv.E.tok, CanCallAssumption(loopInv.E, etran)));
      }
      Bpl.StmtList body = loopBodyBuilder.Collect(s.Tok);

      builder.Add(new Bpl.WhileCmd(s.Tok, Bpl.Expr.True, invariants, body));
    }

    void TrAlternatives(List<GuardedAlternative> alternatives, Bpl.Cmd elseCase0, Bpl.StructuredCmd elseCase1,
                        BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, bool isGhost) {
      Contract.Requires(alternatives != null);
      Contract.Requires((elseCase0 == null) != (elseCase1 == null));  // ugly way of doing a type union
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

      // alpha-rename any binding guards
      var guards = alternatives.ConvertAll(alt => alt.IsBindingGuard ? AlphaRename((ExistsExpr)alt.Guard, "eg$") : alt.Guard);

      // build the negation of the disjunction of all guards (that is, the conjunction of their negations)
      Bpl.Expr noGuard = Bpl.Expr.True;
      var b = new BoogieStmtListBuilder(this);
      foreach (var g in guards) {
        b.Add(TrAssumeCmd(g.tok, CanCallAssumption(g, etran)));
        noGuard = BplAnd(noGuard, Bpl.Expr.Not(etran.TrExpr(g)));
      }

      var elseTok = elseCase0 != null ? elseCase0.tok : elseCase1.tok;
      b.Add(TrAssumeCmd(elseTok, noGuard));
      if (elseCase0 != null) {
        b.Add(elseCase0);
      } else {
        b.Add(elseCase1);
      }
      Bpl.StmtList els = b.Collect(elseTok);

      Bpl.IfCmd elsIf = null;
      for (int i = alternatives.Count; 0 <= --i; ) {
        Contract.Assert(elsIf == null || els == null);  // loop invariant
        CurrentIdGenerator.Push();
        var alternative = alternatives[i];
        b = new BoogieStmtListBuilder(this);
        TrStmt_CheckWellformed(guards[i], b, locals, etran, true);
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;  // the original (that is, not alpha-renamed) guard
          IntroduceAndAssignExistentialVars(exists, b, builder, locals, etran, isGhost);
        } else {
          b.Add(new AssumeCmd(alternative.Guard.tok, etran.TrExpr(alternative.Guard)));
        }
        var prevDefiniteAssignmentTrackerCount = definiteAssignmentTrackers.Count;
        foreach (var s in alternative.Body) {
          TrStmt(s, b, locals, etran);
        }
        RemoveDefiniteAssignmentTrackers(alternative.Body, prevDefiniteAssignmentTrackerCount);
        Bpl.StmtList thn = b.Collect(alternative.Tok);
        elsIf = new Bpl.IfCmd(alternative.Tok, null, thn, elsIf, els);
        els = null;
        CurrentIdGenerator.Pop();
      }
      Contract.Assert(elsIf != null && els == null); // follows from loop invariant and the fact that there's more than one alternative
      builder.Add(elsIf);
    }

    void TrCallStmt(CallStmt s, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, Bpl.IdentifierExpr actualReceiver) {
      Contract.Requires(s != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(!(s.Method is Constructor) || (s.Lhs.Count == 0 && actualReceiver != null));

      List<AssignToLhs> lhsBuilders;
      List<Bpl.IdentifierExpr> bLhss;
      Bpl.Expr[] ignore1, ignore2;
      string[] ignore3;
      var tySubst = s.MethodSelect.TypeArgumentSubstitutionsWithParents();
      ProcessLhss(s.Lhs, true, true, builder, locals, etran, out lhsBuilders, out bLhss, out ignore1, out ignore2, out ignore3, s.OriginalInitialLhs);
      Contract.Assert(s.Lhs.Count == lhsBuilders.Count);
      Contract.Assert(s.Lhs.Count == bLhss.Count);
      var lhsTypes = new List<Type>();
      if (s.Method is Constructor) {
        lhsTypes.Add(s.Receiver.Type);
        bLhss.Add(actualReceiver);
      } else {
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          lhsTypes.Add(lhs.Type);
          builder.Add(new CommentCmd("TrCallStmt: Adding lhs with type " + lhs.Type));
          if (bLhss[i] == null) {  // (in the current implementation, the second parameter "true" to ProcessLhss implies that all bLhss[*] will be null)
            // create temporary local and assign it to bLhss[i]
            string nm = CurrentIdGenerator.FreshId("$rhs##");
            var formalOutType = Resolver.SubstType(s.Method.Outs[i].Type, tySubst);
            var ty = TrType(formalOutType);
            Bpl.Expr wh = GetWhereClause(lhs.tok, new Bpl.IdentifierExpr(lhs.tok, nm, ty), formalOutType, etran,
              isAllocContext.Var(s.IsGhost || s.Method.IsGhost, s.Method.Outs[i]));
            Bpl.LocalVariable var = new Bpl.LocalVariable(lhs.tok, new Bpl.TypedIdent(lhs.tok, nm, ty, wh));
            locals.Add(var);
            bLhss[i] = new Bpl.IdentifierExpr(lhs.tok, var.Name, ty);
          }
        }
      }
      Bpl.IdentifierExpr initHeap = null;
      if (codeContext is IteratorDecl) {
        // var initHeap := $Heap;
        var initHeapVar = new Bpl.LocalVariable(s.Tok, new Bpl.TypedIdent(s.Tok, CurrentIdGenerator.FreshId("$initHeapCallStmt#"), predef.HeapType));
        locals.Add(initHeapVar);
        initHeap = new Bpl.IdentifierExpr(s.Tok, initHeapVar);
        // initHeap := $Heap;
        builder.Add(Bpl.Cmd.SimpleAssign(s.Tok, initHeap, etran.HeapExpr));
      }
      builder.Add(new CommentCmd("TrCallStmt: Before ProcessCallStmt"));
      ProcessCallStmt(s.Tok, tySubst, GetTypeParams(s.Method), s.Receiver, actualReceiver, s.Method, s.MethodSelect.AtLabel, s.Args, bLhss, lhsTypes, builder, locals, etran);
      builder.Add(new CommentCmd("TrCallStmt: After ProcessCallStmt"));
      for (int i = 0; i < lhsBuilders.Count; i++) {
        var lhs = s.Lhs[i];
        Type lhsType, rhsTypeConstraint;
        if (lhs is IdentifierExpr) {
          var ide = (IdentifierExpr)lhs;
          lhsType = ide.Var.Type;
          rhsTypeConstraint = lhsType;
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = (Field)fse.Member;
          Contract.Assert(field != null);
          Contract.Assert(VisibleInScope(field));
          lhsType = field.Type;
          rhsTypeConstraint = Resolver.SubstType(lhsType, fse.TypeArgumentSubstitutionsWithParents());
        } else if (lhs is SeqSelectExpr) {
          var e = (SeqSelectExpr)lhs;
          lhsType = null;  // for arrays, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Seq.Type.TypeArgs[0];
        } else {
          var e = (MultiSelectExpr)lhs;
          lhsType = null;  // for arrays, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Array.Type.TypeArgs[0];
        }

        Bpl.Expr bRhs = bLhss[i];  // the RHS (bRhs) of the assignment to the actual call-LHS (lhs) was a LHS (bLhss[i]) in the Boogie call statement
        CheckSubrange(lhs.tok, bRhs, Resolver.SubstType(s.Method.Outs[i].Type, tySubst), rhsTypeConstraint, builder);
        bRhs = CondApplyBox(lhs.tok, bRhs, lhs.Type, lhsType);

        lhsBuilders[i](bRhs, false, builder, etran);
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
      Method method, Label/*?*/ atLabel, List<Expression> Args,
      List<Bpl.IdentifierExpr> Lhss, List<Type> LhsTypes,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {

      Contract.Requires(tok != null);
      Contract.Requires(dafnyReceiver != null || bReceiver != null);
      Contract.Requires(method != null);
      Contract.Requires(VisibleInScope(method));
      Contract.Requires(method is TwoStateLemma || atLabel == null);
      Contract.Requires(Args != null);
      Contract.Requires(Lhss != null);
      Contract.Requires(LhsTypes != null);
      // Note, a Dafny class constructor is declared to have no output parameters, but it is encoded in Boogie as
      // having an output parameter.
      Contract.Requires(method is Constructor || method.Outs.Count == Lhss.Count);
      Contract.Requires(method is Constructor || method.Outs.Count == LhsTypes.Count);
      Contract.Requires(!(method is Constructor) || (method.Outs.Count == 0 && Lhss.Count == 1 && LhsTypes.Count == 1));
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(tySubst != null);
      Contract.Requires(tyArgs != null);
      Contract.Requires(tyArgs.Count <= tySubst.Count);  // more precisely, the members of tyArgs are required to be keys of tySubst, but this is a cheap sanity test

      // Figure out if the call is recursive or not, which will be used below to determine the need for a
      // termination check and the need to include an implicit _k-1 argument.
      bool isRecursiveCall = false;
      // consult the call graph to figure out if this is a recursive call
      var module = method.EnclosingClass.EnclosingModuleDefinition;
      if (codeContext != null && module == currentModule) {
        // Note, prefix lemmas are not recorded in the call graph, but their corresponding greatest lemmas are.
        // Similarly, an iterator is not recorded in the call graph, but its MoveNext method is.
        ICallable cllr =
          codeContext is PrefixLemma ? ((PrefixLemma)codeContext).ExtremeLemma :
          codeContext is IteratorDecl ? ((IteratorDecl)codeContext).Member_MoveNext :
          codeContext;
        if (ModuleDefinition.InSameSCC(method, cllr)) {
          isRecursiveCall = true;
        }
      }

      MethodTranslationKind kind;
      var callee = method;
      if (method is ExtremeLemma && isRecursiveCall) {
        kind = MethodTranslationKind.CoCall;
        callee = ((ExtremeLemma)method).PrefixLemma;
      } else if (method is PrefixLemma) {
        // an explicit call to a prefix lemma is allowed only inside the SCC of the corresponding greatest lemma,
        // so we consider this to be a co-call
        kind = MethodTranslationKind.CoCall;
      } else {
        kind = MethodTranslationKind.Call;
      }


      var ins = new List<Bpl.Expr>();
      if (callee is TwoStateLemma) {
        ins.Add(etran.OldAt(atLabel).HeapExpr);
        ins.Add(etran.HeapExpr);
      }
      // Add type arguments
      ins.AddRange(trTypeArgs(tySubst, tyArgs));

      // Translate receiver argument, if any
      Expression receiver = bReceiver == null ? dafnyReceiver : new BoogieWrapper(bReceiver, dafnyReceiver.Type);
      if (!method.IsStatic && !(method is Constructor)) {
        if (bReceiver == null) {
          TrStmt_CheckWellformed(dafnyReceiver, builder, locals, etran, true);
          if (!(dafnyReceiver is ThisExpr)) {
            CheckNonNull(dafnyReceiver.tok, dafnyReceiver, builder, etran, null);
          }
        }
        ins.Add(etran.TrExpr(receiver));
      } else if (receiver is StaticReceiverExpr stexpr) {
        if (stexpr.OriginalResolved != null) {
          TrStmt_CheckWellformed(stexpr.OriginalResolved, builder, locals, etran, true);
        }
      }

      // Ideally, the modifies and decreases checks would be done after the precondition check,
      // but Boogie doesn't give us a hook for that.  So, we set up our own local variables here to
      // store the actual parameters.
      // Create a local variable for each formal parameter, and assign each actual parameter to the corresponding local
      var substMap = new Dictionary<IVariable, Expression>();
      for (int i = 0; i < callee.Ins.Count; i++) {
        var formal = callee.Ins[i];
        var local = new LocalVariable(formal.tok, formal.tok, formal.Name + "#", Resolver.SubstType(formal.Type, tySubst), formal.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        var ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(formal, ie);
        locals.Add(new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type))));

        var param = (Bpl.IdentifierExpr)etran.TrExpr(ie);  // TODO: is this cast always justified?
        Bpl.Expr bActual;
        if (i == 0 && method is ExtremeLemma && isRecursiveCall) {
          // Treat this call to M(args) as a call to the corresponding prefix lemma M#(_k - 1, args), so insert an argument here.
          var k = ((PrefixLemma)callee).K;
          var bplK = new Bpl.IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration.IdGenerator), TrType(k.Type));
          if (k.Type.IsBigOrdinalType) {
            bActual = FunctionCall(k.tok, "ORD#Minus", predef.BigOrdinalType,
              bplK,
              FunctionCall(k.tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(1)));
          } else {
            bActual = Bpl.Expr.Sub(bplK, Bpl.Expr.Literal(1));
          }
        } else {
          Expression actual;
          if (method is ExtremeLemma && isRecursiveCall) {
            actual = Args[i - 1];
          } else {
            actual = Args[i];
          }
          if (!(actual is DefaultValueExpression)) {
            TrStmt_CheckWellformed(actual, builder, locals, etran, true);
          }
          builder.Add(new CommentCmd("ProcessCallStmt: CheckSubrange"));
          // Check the subrange without boxing
          var beforeBox = etran.TrExpr(actual);
          CheckSubrange(actual.tok, beforeBox, actual.Type, Resolver.SubstType(formal.Type, tySubst), builder);
          bActual = CondApplyBox(actual.tok, beforeBox, actual.Type, Resolver.SubstType(formal.Type, tySubst));
        }
        Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(formal.tok, param, bActual);
        builder.Add(cmd);
        ins.Add(CondApplyBox(param.tok, param, Resolver.SubstType(formal.Type, tySubst), formal.Type));
      }

      // Check that every parameter is available in the state in which the method is invoked; this means checking that it has
      // the right type and is allocated.  These checks usually hold trivially, on account of that the Dafny language only gives
      // access to expressions of the appropriate type and that are allocated in the current state.  However, if the method is
      // invoked in the 'old' state or if the method invoked is a two-state lemma with a non-new parameter, then we need to
      // check that its arguments were all available at that time as well.
      if (etran.UsesOldHeap) {
        if (!method.IsStatic && !(method is Constructor)) {
          Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran, ISALLOC, true);
          if (wh != null) {
            builder.Add(Assert(receiver.tok, wh, "receiver argument must be allocated in the state in which the method is invoked"));
          }
        }
        for (int i = 0; i < Args.Count; i++) {
          Expression ee = Args[i];
          Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran, ISALLOC, true);
          if (wh != null) {
            builder.Add(Assert(ee.tok, wh, "argument must be allocated in the state in which the method is invoked"));
          }
        }
      } else if (method is TwoStateLemma) {
        if (!method.IsStatic) {
          Bpl.Expr wh = GetWhereClause(receiver.tok, etran.TrExpr(receiver), receiver.Type, etran.OldAt(atLabel), ISALLOC, true);
          if (wh != null) {
            builder.Add(Assert(receiver.tok, wh, "receiver argument must be allocated in the two-state lemma's previous state"));
          }
        }
        Contract.Assert(callee.Ins.Count == Args.Count);
        for (int i = 0; i < Args.Count; i++) {
          var formal = callee.Ins[i];
          if (formal.IsOld) {
            Expression ee = Args[i];
            Bpl.Expr wh = GetWhereClause(ee.tok, etran.TrExpr(ee), ee.Type, etran.OldAt(atLabel), ISALLOC, true);
            if (wh != null) {
              builder.Add(Assert(ee.tok, wh, string.Format("parameter{0} ('{1}') must be allocated in the two-state lemma's previous state",
                Args.Count == 1 ? "" : " " + i, formal.Name)));
            }
          }
        }
      }

      // Check modifies clause of a subcall is a subset of the current frame.
      if (codeContext is IMethodCodeContext) {
        var s = new Substituter(null, new Dictionary<IVariable, Expression>(), tySubst);
        CheckFrameSubset(tok, callee.Mod.Expressions.ConvertAll(s.SubstFrameExpr),
          receiver, substMap, etran, builder, "call may violate context's modifies clause", null);
      }

      // Check termination
      if (isRecursiveCall) {
        Contract.Assert(codeContext != null);
        if (codeContext is DatatypeDecl) {
          builder.Add(Assert(tok, Bpl.Expr.False, "default-value expression is not allowed to involve recursive or mutually recursive calls"));
        } else {
          List<Expression> contextDecreases = codeContext.Decreases.Expressions;
          List<Expression> calleeDecreases = callee.Decreases.Expressions;
          CheckCallTermination(tok, contextDecreases, calleeDecreases, null, receiver, substMap, tySubst, etran, etran.Old, builder, codeContext.InferredDecreases, null);
        }
      }

      // Create variables to hold the output parameters of the call, so that appropriate unboxes can be introduced.
      var outs = new List<Bpl.IdentifierExpr>();
      var tmpOuts = new List<Bpl.IdentifierExpr>();
      if (method is Constructor) {
        tmpOuts.Add(null);
        outs.Add(Lhss[0]);
      } else {
        for (int i = 0; i < Lhss.Count; i++) {
          var bLhs = Lhss[i];
          if (ModeledAsBoxType(callee.Outs[i].Type) && !ModeledAsBoxType(LhsTypes[i])) {
            // we need an Unbox
            Bpl.LocalVariable var = new Bpl.LocalVariable(bLhs.tok, new Bpl.TypedIdent(bLhs.tok, CurrentIdGenerator.FreshId("$tmp##"), predef.BoxType));
            locals.Add(var);
            Bpl.IdentifierExpr varIdE = new Bpl.IdentifierExpr(bLhs.tok, var.Name, predef.BoxType);
            tmpOuts.Add(varIdE);
            outs.Add(varIdE);
          } else {
            tmpOuts.Add(null);
            outs.Add(bLhs);
          }
        }
      }

      builder.Add(new CommentCmd("ProcessCallStmt: Make the call"));
      // Make the call
      AddReferencedMember(callee);
      Bpl.CallCmd call = Call(tok, MethodName(callee, kind), ins, outs);
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
          cmd = TrAssumeCmd(bLhs.tok, Bpl.Expr.Eq(bLhs, FunctionCall(bLhs.tok, BuiltinFunction.Unbox, TrType(LhsTypes[i]), tmpVarIdE)));
          builder.Add(cmd);
        }
      }
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, out Bpl.Expr typeAntecedent,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
      Dictionary<TypeParameter, Type> typeMap = null, string nameSuffix = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.ValueAtReturn(out typeAntecedent) != null);

      if (typeMap == null) {
        typeMap = new Dictionary<TypeParameter, Type>();
      }
      typeAntecedent = Bpl.Expr.True;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (BoundVar bv in boundVars) {
        LocalVariable local = new LocalVariable(bv.tok, bv.tok, nameSuffix == null ? bv.Name : bv.Name + nameSuffix, Resolver.SubstType(bv.Type, typeMap), bv.IsGhost);
        local.type = local.OptionalType;  // resolve local here
        IdentifierExpr ie = new IdentifierExpr(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator));
        ie.Var = local; ie.Type = ie.Var.Type;  // resolve ie here
        substMap.Add(bv, ie);
        Bpl.LocalVariable bvar = new Bpl.LocalVariable(local.Tok, new Bpl.TypedIdent(local.Tok, local.AssignUniqueName(currentDeclaration.IdGenerator), TrType(local.Type)));
        locals.Add(bvar);
        var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
        builder.Add(new Bpl.HavocCmd(bv.tok, new List<Bpl.IdentifierExpr> { bIe }));
        Bpl.Expr wh = GetWhereClause(bv.tok, bIe, local.Type, etran, CommonHeapUse ? IsAllocType.ISALLOC : IsAllocType.NOALLOC);
        if (wh != null) {
          typeAntecedent = BplAnd(typeAntecedent, wh);
        }
      }
      return substMap;
    }

    Dictionary<IVariable, Expression> SetupBoundVarsAsLocals(List<BoundVar> boundVars, BoogieStmtListBuilder builder,
      List<Variable> locals, ExpressionTranslator etran, Dictionary<TypeParameter, Type> typeMap = null,
      string nameSuffix = null) {
      Contract.Requires(boundVars != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);

      var substMap = SetupBoundVarsAsLocals(boundVars, out var typeAntecedent, builder, locals, etran, typeMap, nameSuffix);
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

      var local = new LocalVariable(v.Tok, v.Tok, v.Name, v.Type, v.IsGhost);
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

    List<Bpl.Expr> RecordDecreasesValue(List<Expression> decreases, BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran, string varPrefix)
    {
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
                              Expression receiverReplacement, Dictionary<IVariable,Expression> substMap,
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
                            BoogieStmtListBuilder builder, string suffixMsg, bool allowNoChange, bool includeLowerBound)
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
        Contract.Assert(t.IsTypeParameter || t.IsOpaqueType || t.IsInternalTypeSynonym);
        return false;  // don't consider any type parameters to be the same (since we have no comparison function for them anyway)
      }
    }

    Nullable<BuiltinFunction> RankFunction(Type/*!*/ ty)
    {
      Contract.Requires(ty != null);
      if (ty is SeqType) {
        return BuiltinFunction.SeqRank;
      } else if (ty.IsIndDatatype) {
        return BuiltinFunction.DtRank;
      } else {
        return null;
      }
    }

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
        atmost = FunctionCall(tok, "ge_bv" + bv.Width, Bpl.Type.Bool, e0, e1);

      } else if (ty0 is BigOrdinalType) {
        eq = Bpl.Expr.Eq(e0, e1);
        less = FunctionCall(tok, "ORD#Less", Bpl.Type.Bool, e0, e1);
        atmost = BplOr(eq, less);

      } else if (ty0.IsTypeParameter || ty0.IsOpaqueType) {
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
      builder.Add(new Bpl.CommentCmd(string.Format("----- {0} ----- {1}({2},{3})", comment, stmt.Tok.filename, stmt.Tok.line, stmt.Tok.col)));
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

      var normType = type.NormalizeExpandKeepConstraints();

      if (normType.IsTypeParameter || normType.IsOpaqueType) {
        var udt = (UserDefinedType)normType;
        return trTypeParamOrOpaqueType(udt.ResolvedClass, udt.TypeArgs);
      } else if (normType is UserDefinedType) {
        // Classes, (co-)datatypes, newtypes, subset types, ...
        var args = normType.TypeArgs.ConvertAll(TypeToTy);
        return ClassTyCon(((UserDefinedType)normType), args);
      } else if (normType is SetType) {
        bool finite = ((SetType)normType).Finite;
        return FunctionCall(Token.NoToken, finite ? "TSet" : "TISet", predef.Ty, TypeToTy(((CollectionType)normType).Arg));
      } else if (normType is MultiSetType) {
        return FunctionCall(Token.NoToken, "TMultiSet", predef.Ty, TypeToTy(((CollectionType)normType).Arg));
      } else if (normType is SeqType) {
        return FunctionCall(Token.NoToken, "TSeq", predef.Ty, TypeToTy(((CollectionType)normType).Arg));
      } else if (normType is MapType) {
        bool finite = ((MapType)normType).Finite;
        return FunctionCall(Token.NoToken, finite ? "TMap" : "TIMap", predef.Ty,
          TypeToTy(((MapType)normType).Domain),
          TypeToTy(((MapType)normType).Range));
      } else if (normType is BoolType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TBool", predef.Ty);
      } else if (normType is CharType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TChar", predef.Ty);
      } else if (normType is RealType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TReal", predef.Ty);
      } else if (normType is BitvectorType) {
        var t = (BitvectorType)normType;
        return FunctionCall(Token.NoToken, "TBitvector", predef.Ty, Bpl.Expr.Literal(t.Width));
      } else if (normType is IntType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TInt", predef.Ty);
      } else if (normType is BigOrdinalType) {
        return new Bpl.IdentifierExpr(Token.NoToken, "TORDINAL", predef.Ty);
      } else if (normType is ParamTypeProxy) {
        return trTypeParamOrOpaqueType(((ParamTypeProxy)normType).orig);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    static string nameTypeParam(TopLevelDecl x) {
      Contract.Requires(x is TypeParameter || x is OpaqueTypeDecl);
      if (x is TypeParameter tp && tp.Parent != null) {
        return tp.Parent.FullName + "$" + x.Name;
      } else {
        // This happens for builtins, like arrays, that don't have a parent
        return "#$" + x.Name;
      }
    }

    Bpl.Expr trTypeParamOrOpaqueType(TopLevelDecl x, List<Type>/*?*/ tyArguments = null) {
      Contract.Requires(x is TypeParameter || x is OpaqueTypeDecl);
      Contract.Requires(!(x is TypeParameter) || tyArguments == null || tyArguments.Count == 0);
      Contract.Requires(!(x is OpaqueTypeDecl) || tyArguments != null);
      if (x is TypeParameter tp) {
        Contract.Assert(tyArguments == null || tyArguments.Count == 0);
        var nm = nameTypeParam(tp);
        // return an identifier denoting a constant
        return new Bpl.IdentifierExpr(x.tok, nm, predef.Ty);
      } else {
        var ot = (OpaqueTypeDecl)x;
        var nm = nameTypeParam(ot);
        if (tyArguments.Count != 0) {
          List<Bpl.Expr> args = tyArguments.ConvertAll(TypeToTy);
          return FunctionCall(x.tok, nm, predef.Ty, args);
        } else {
          // return an identifier denoting a constant
          return new Bpl.IdentifierExpr(x.tok, nm, predef.Ty);
        }
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
      Contract.Requires(d is ClassDecl || d is DatatypeDecl || d is NewtypeDecl || d is ValuetypeDecl);
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
      return MkIs(x, TypeToTy(t.NormalizeExpandKeepConstraints()), true);
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


    Bpl.Expr GetWhereClause(IToken tok, Bpl.Expr x, Type type, ExpressionTranslator etran, IsAllocType alloc, bool allocatednessOnly = false) {
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
      } else if (((AlwaysUseHeap && alloc != IsAllocType.NEVERALLOC) || alloc == ISALLOC) && etran.HeapExpr != null) {
        isAlloc = MkIsAlloc(x, normType, etran.HeapExpr);
      } else {
        isAlloc = null;
      }
      if (allocatednessOnly) {
        return isAlloc;
      }

      Bpl.Expr isPred = null;
      if (normType is BoolType || normType is IntType || normType is RealType || normType is BigOrdinalType) {
        // nothing to do
      } else if (normType is BitvectorType) {
        var t = (BitvectorType)normType;
        if (t.Width == 0) {
          // type bv0 has only one value
          return Bpl.Expr.Eq(BplBvLiteralExpr(tok, BaseTypes.BigNum.ZERO, t), x);
        }
      } else if ((normType.AsTypeSynonym != null || normType.AsNewtype != null) &&
        (normType.IsNumericBased() || normType.IsBitVectorType || normType.IsBoolType)) {
        var constraint = Resolver.GetImpliedTypeConstraint(new BoogieWrapper(x, normType), normType);
        isPred = etran.TrExpr(constraint);
      } else {
        // go for the symbolic name
        isPred = MkIs(x, normType);
      }
      return isAlloc == null ? isPred : isPred == null ? isAlloc : BplAnd(isPred, isAlloc);
    }

    /// <summary>
    /// "lhs" is expected to be a resolved form of an expression, i.e., not a conrete-syntax expression.
    /// </summary>
    void TrAssignment(Statement stmt, Expression lhs, AssignmentRhs rhs,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran)
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
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(lhsBuilder != null);
      Contract.Requires(bLhss != null);
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      var finalRhss = new List<Bpl.Expr>();
      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        // the following assumes are part of the precondition, really
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

        Type lhsType, rhsTypeConstraint;
        if (lhs is IdentifierExpr) {
          var ide = (IdentifierExpr)lhs;
          lhsType = ide.Var.Type;
          rhsTypeConstraint = lhsType;
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = (Field)fse.Member;
          Contract.Assert(VisibleInScope(field));
          lhsType = field.Type;
          rhsTypeConstraint = Resolver.SubstType(lhsType, fse.TypeArgumentSubstitutionsWithParents());
        } else if (lhs is SeqSelectExpr) {
          var e = (SeqSelectExpr)lhs;
          lhsType = null;  // for an array update, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Seq.Type.NormalizeExpand().TypeArgs[0];
        } else {
          var e = (MultiSelectExpr)lhs;
          lhsType = null;  // for an array update, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Array.Type.NormalizeExpand().TypeArgs[0];
        }
        var bRhs = TrAssignmentRhs(rhss[i].Tok, bLhss[i], lhsType, rhss[i], rhsTypeConstraint, builder, locals, etran);
        if (bLhss[i] != null) {
          Contract.Assert(bRhs == bLhss[i]);  // this is what the postcondition of TrAssignmentRhs promises
          // assignment has already been done by TrAssignmentRhs
          finalRhss.Add(null);
        } else {
          Contract.Assert(bRhs != null);  // this is what the postcondition of TrAssignmentRhs promises
          finalRhss.Add(bRhs);
        }
      }
      for (int i = 0; i < lhss.Count; i++) {
        lhsBuilder[i](finalRhss[i], rhss[i] is HavocRhs, builder, etran);
      }
    }

    List<Bpl.Expr> ProcessUpdateAssignRhss(List<Expression> lhss, List<AssignmentRhs> rhss,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(builder != null);
      Contract.Requires(cce.NonNullElements(locals));
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.ForAll(Contract.Result<List<Bpl.Expr>>(), i => i != null));

      var finalRhss = new List<Bpl.Expr>();
      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        // the following assumes are part of the precondition, really
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        Contract.Assume(!(lhs is SeqSelectExpr && !((SeqSelectExpr)lhs).SelectOne));  // array-range assignments are not allowed

        Type lhsType, rhsTypeConstraint;
        if (lhs is IdentifierExpr) {
          lhsType = ((IdentifierExpr)lhs).Var.Type;
          rhsTypeConstraint = lhsType;
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = (Field)fse.Member;
          Contract.Assert(VisibleInScope(field));
          lhsType = field.Type;
          rhsTypeConstraint = Resolver.SubstType(lhsType, fse.TypeArgumentSubstitutionsWithParents());
        } else if (lhs is SeqSelectExpr) {
          var e = (SeqSelectExpr)lhs;
          lhsType = null;  // for an array update, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Seq.Type.TypeArgs[0];
        } else {
          var e = (MultiSelectExpr)lhs;
          lhsType = null;  // for an array update, always make sure the value assigned is boxed
          rhsTypeConstraint = e.Array.Type.TypeArgs[0];
        }
        var bRhs = TrAssignmentRhs(rhss[i].Tok, null, lhsType, rhss[i], rhsTypeConstraint, builder, locals, etran);
        finalRhss.Add(bRhs);
      }
      return finalRhss;
    }


    private void CheckLhssDistinctness(List<Bpl.Expr> rhs, List<AssignmentRhs> rhsOriginal, List<Expression> lhss,
      BoogieStmtListBuilder builder, ExpressionTranslator etran,
      Bpl.Expr[] objs, Bpl.Expr[] fields, string[] names, Expression originalInitialLhs = null) {
      Contract.Requires(rhs != null);
      Contract.Requires(rhsOriginal != null);
      Contract.Requires(lhss != null);
      Contract.Requires(rhs.Count == rhsOriginal.Count);
      Contract.Requires(lhss.Count == rhsOriginal.Count);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);

      for (int i = 0; i < lhss.Count; i++) {
        var lhs = lhss[i];
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        if (originalInitialLhs != null) {
          // TODO - check RHS values?
          AssertDistinctness(lhs, originalInitialLhs, builder, etran);
        }
        for (int j = 0; j < i; j++) {
          if (rhsOriginal[i] is HavocRhs || rhsOriginal[j] is HavocRhs) {
            AssertDistinctness(lhs, lhss[j], builder, etran);
          } else {
            AssertDistinctness(lhs, lhss[j], rhs[i], rhs[j], builder, etran);
          }
        }
      }
    }

    /// <summary>
    /// Note, if "rhs" is "null", then the assignment has already been done elsewhere. However, any other bookkeeping
    /// is still done.
    /// </summary>
    delegate void AssignToLhs(Bpl.Expr/*?*/ rhs, bool origRhsIsHavoc, BoogieStmtListBuilder builder, ExpressionTranslator etran);

    // Returns an expression, which, if false, means that the two LHS expressions are
    // not distinct; if null then the LHSs are trivially distinct
    Bpl.Expr CheckDistinctness(Expression lhsa, Expression lhsb, ExpressionTranslator etran) {
      {
        if (lhsa is IdentifierExpr iea && lhsb is IdentifierExpr ieb) {
          if (iea.Name != ieb.Name) return null;
          return Bpl.Expr.False;
        }
      }
      {
        if (lhsa is MemberSelectExpr iea && lhsb is MemberSelectExpr ieb) {
          if (iea.Member is Field fa && ieb.Member is Field fb) {
            if (fa != fb) return null;
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

    void AssertDistinctness(Expression lhsa, Expression lhsb, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Bpl.Expr e = CheckDistinctness(lhsa, lhsb, etran);
      if (e != null) {
        string may = e == Bpl.Expr.False ? "" : "may ";
        builder.Add(Assert(lhsa.tok, e,
          ($"left-hand sides {Printer.ExprToString(lhsa)} and {Printer.ExprToString(lhsb)} {may}refer to the same location")));
      }
    }

    void AssertDistinctness(Expression lhsa, Expression lhsb, Bpl.Expr rhsa, Bpl.Expr rhsb, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Bpl.Expr e = CheckDistinctness(lhsa, lhsb, etran);
      if (e != null) {
        e = Bpl.Expr.Or(e, Bpl.Expr.Eq(rhsa,rhsb));
        builder.Add(Assert(lhsa.tok, e,
          ($"when left-hand sides {Printer.ExprToString(lhsa)} and {Printer.ExprToString(lhsb)} refer to the same location, they must be assigned the same value")));
      }
    }

    /// <summary>
    /// Creates a list of protected Boogie LHSs for the given Dafny LHSs.  Along the way,
    /// builds code that checks that the LHSs are well-defined,
    /// and are allowed by the enclosing modifies clause.
    /// Checks that they denote different locations iff checkDistinctness is true.
    /// </summary>
    void ProcessLhss(List<Expression> lhss, bool rhsCanAffectPreviouslyKnownExpressions, bool checkDistinctness,
      BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran,
      out List<AssignToLhs> lhsBuilders, out List<Bpl.IdentifierExpr/*may be null*/> bLhss,
      out Bpl.Expr[] prevObj, out Bpl.Expr[] prevIndex, out string[] prevNames, Expression originalInitialLhs = null) {

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

      // Note, the resolver does not check for duplicate IdentifierExpr's in LHSs, so do it here.
      foreach (var lhs in lhss) {
        Contract.Assume(!(lhs is ConcreteSyntaxExpression));
        if (checkDistinctness) {
          if (originalInitialLhs != null) {
            AssertDistinctness(lhs, originalInitialLhs.Resolved, builder, etran);
          }
          for (int j = 0; j < i; j++) {
            AssertDistinctness(lhs, lhss[j], builder, etran);
          }
        }
        i++;
      }

      i = 0;
      foreach (var lhs in lhss) {
        IToken tok = lhs.tok;
        TrStmt_CheckWellformed(lhs, builder, locals, etran, true, true);

        if (lhs is IdentifierExpr) {
          var ie = (IdentifierExpr)lhs;
          prevNames[i] = ie.Name;
          var bLhs = (Bpl.IdentifierExpr)etran.TrExpr(lhs);  // TODO: is this cast always justified?
          bLhss.Add(rhsCanAffectPreviouslyKnownExpressions ? null : bLhs);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
            if (rhs != null) {
              bldr.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, rhs));
            }
            if (!origRhsIsHavoc) {
              MarkDefiniteAssignmentTracker(ie, bldr);
            }
          });

        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          var field = fse.Member as Field;
          Contract.Assert(field != null);
          Contract.Assert(VisibleInScope(field));

          var useSurrogateLocal = inBodyInitContext && Expression.AsThis(fse.Obj) != null;

          var obj = SaveInTemp(etran.TrExpr(fse.Obj), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          prevObj[i] = obj;
          if (!useSurrogateLocal) {
            // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj]);
            builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, GetField(fse)), "assignment may update an object not in the enclosing context's modifies clause"));
          }

          if (useSurrogateLocal) {
            var nm = SurrogateName(field);
            var bLhs = new Bpl.IdentifierExpr(fse.tok, nm, TrType(field.Type));
            bLhss.Add(rhsCanAffectPreviouslyKnownExpressions ? null : bLhs);
            lhsBuilders.Add(delegate(Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
              if (rhs != null) {
                bldr.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, rhs));
              }
              if (!origRhsIsHavoc) {
                MarkDefiniteAssignmentTracker(lhs.tok, nm, bldr);
              }
            });
          } else {
            bLhss.Add(null);
            lhsBuilders.Add(delegate(Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
              if (rhs != null) {
                var fseField = fse.Member as Field;
                Contract.Assert(fseField != null);
                Check_NewRestrictions(tok, obj, fseField, rhs, bldr, et);
                var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
                Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, new Bpl.IdentifierExpr(tok, GetField(fseField)), rhs));
                bldr.Add(cmd);
                // assume $IsGoodHeap($Heap);
                bldr.Add(AssumeGoodHeap(tok, et));
              }
            });
          }

        } else if (lhs is SeqSelectExpr) {
          SeqSelectExpr sel = (SeqSelectExpr)lhs;
          Contract.Assert(sel.SelectOne);  // array-range assignments are not allowed
          Contract.Assert(sel.Seq.Type != null && sel.Seq.Type.IsArrayType);
          Contract.Assert(sel.E0 != null);
          var obj = SaveInTemp(etran.TrExpr(sel.Seq), rhsCanAffectPreviouslyKnownExpressions,
            "$obj" + i, predef.RefType, builder, locals);
          var idx = etran.TrExpr(sel.E0);
          idx = ConvertExpression(sel.E0.tok, idx, sel.E0.Type, Type.Int);
          var fieldName = SaveInTemp(FunctionCall(tok, BuiltinFunction.IndexField, null, idx), rhsCanAffectPreviouslyKnownExpressions,
            "$index" + i, predef.FieldName(tok, predef.BoxType), builder, locals);
          prevObj[i] = obj;
          prevIndex[i] = fieldName;
          // check that the enclosing modifies clause allows this object to be written:  assert $_Frame[obj,index]);
          builder.Add(Assert(tok, Bpl.Expr.SelectTok(tok, etran.TheFrame(tok), obj, fieldName), "assignment may update an array element not in the enclosing context's modifies clause"));

          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
            if (rhs != null) {
              var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
              Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, fieldName, rhs));
              bldr.Add(cmd);
              // assume $IsGoodHeap($Heap);
              bldr.Add(AssumeGoodHeap(tok, et));
            }
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

          bLhss.Add(null);
          lhsBuilders.Add(delegate(Bpl.Expr rhs, bool origRhsIsHavoc, BoogieStmtListBuilder bldr, ExpressionTranslator et) {
            if (rhs != null) {
              var h = (Bpl.IdentifierExpr)et.HeapExpr;  // TODO: is this cast always justified?
              Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, h, ExpressionTranslator.UpdateHeap(tok, h, obj, fieldName, rhs));
              bldr.Add(cmd);
              // assume $IsGoodHeap($Heap);
              bldr.Add(AssumeGoodHeap(tok, etran));
            }
          });
        }

        i++;
      }
    }

    /// <summary>
    /// if "bGivenLhs" is non-null, generates an assignment of the translation of "rhs" to "bGivenLhs" and then returns "bGivenLhs".
    /// If "bGivenLhs" is null, then this method will return an expression that in a stable way denotes the translation of "rhs";
    /// this is achieved by creating a new temporary Boogie variable to hold the result and returning an expression that mentions
    /// that new temporary variable.
    ///
    /// Before the assignment, the generated code will check that "rhs" obeys any subrange requirements entailed by "rhsTypeConstraint".
    ///
    /// The purpose of "lhsType" is to determine if the expression should be boxed before doing the assignment.  It is allowed to be null,
    /// which indicates that the result should always be a box.  Note that "lhsType" may refer to a formal type parameter that is not in
    /// scope; this is okay, since the purpose of "lhsType" is just to say whether or not the result should be boxed.
    /// </summary>
    Bpl.Expr TrAssignmentRhs(IToken tok, Bpl.IdentifierExpr bGivenLhs, Type lhsType, AssignmentRhs rhs, Type rhsTypeConstraint,
                             BoogieStmtListBuilder builder, List<Variable> locals, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(rhs != null);
      Contract.Requires(rhsTypeConstraint != null);
      Contract.Requires(builder != null);
      Contract.Requires(locals != null);
      Contract.Requires(etran != null);
      Contract.Requires(predef != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      Contract.Ensures(bGivenLhs == null || Contract.Result<Bpl.Expr>() == bGivenLhs);

      Bpl.IdentifierExpr bLhs;
      if (bGivenLhs != null) {
        bLhs = bGivenLhs;
      } else {
        Type localType = rhsTypeConstraint;  // this is a type that is appropriate for capturing the value of the RHS
        var ty = TrType(localType);
        var nm = CurrentIdGenerator.FreshId("$rhs#");
        Bpl.Expr wh = GetWhereClause(tok, new Bpl.IdentifierExpr(tok, nm, ty), localType, etran, NOALLOC);
        var v = new Bpl.LocalVariable(tok, new Bpl.TypedIdent(tok, nm, ty, wh));
        locals.Add(v);
        bLhs = new Bpl.IdentifierExpr(tok, v);
      }

      if (rhs is ExprRhs) {
        var e = (ExprRhs)rhs;

        TrStmt_CheckWellformed(e.Expr, builder, locals, etran, true);

        Bpl.Expr bRhs = etran.TrExpr(e.Expr);
        CheckSubrange(tok, bRhs, e.Expr.Type, rhsTypeConstraint, builder);
        if (bGivenLhs != null) {
          Contract.Assert(bGivenLhs == bLhs);
          // box the RHS, then do the assignment
          var cmd = Bpl.Cmd.SimpleAssign(tok, bGivenLhs, CondApplyBox(tok, bRhs, e.Expr.Type, lhsType));
          builder.Add(cmd);
          return bGivenLhs;
        } else {
          // do the assignment, then box the result
          var cmd = Bpl.Cmd.SimpleAssign(tok, bLhs, bRhs);
          builder.Add(cmd);
          return CondApplyBox(tok, bLhs, e.Expr.Type, lhsType);
        }

      } else if (rhs is HavocRhs) {
        builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { bLhs }));
        return CondApplyBox(tok, bLhs, rhsTypeConstraint, lhsType);
      } else {
        // x := new Something
        Contract.Assert(rhs is TypeRhs);  // otherwise, an unexpected AssignmentRhs
        TypeRhs tRhs = (TypeRhs)rhs;

        var callsConstructor = tRhs.InitCall != null && tRhs.InitCall.Method is Constructor;

        if (tRhs.ArrayDimensions == null) {
          Contract.Assert(tRhs.ElementInit == null && tRhs.InitDisplay == null);
        } else {
          int i = 0;
          foreach (Expression dim in tRhs.ArrayDimensions) {
            CheckWellformed(dim, new WFOptions(), locals, builder, etran);
            builder.Add(Assert(dim.tok, Bpl.Expr.Le(Bpl.Expr.Literal(0), etran.TrExpr(dim)),
              tRhs.ArrayDimensions.Count == 1 ? "array size might be negative" : string.Format("array size (dimension {0}) might be negative", i)));
            i++;
          }
          if (tRhs.ElementInit != null) {
            CheckWellformed(tRhs.ElementInit, new WFOptions(), locals, builder, etran);
          } else if (tRhs.InitDisplay != null) {
            var dim = tRhs.ArrayDimensions[0];
            builder.Add(Assert(dim.tok, Bpl.Expr.Eq(etran.TrExpr(dim), Bpl.Expr.Literal(tRhs.InitDisplay.Count)),
              string.Format("given array size must agree with the number of expressions in the initializing display ({0})", tRhs.InitDisplay.Count)));
            foreach (var v in tRhs.InitDisplay) {
              CheckWellformed(v, new WFOptions(), locals, builder, etran);
            }
          } else if (DafnyOptions.O.DefiniteAssignmentLevel == 0) {
            // cool
          } else if (2 <= DafnyOptions.O.DefiniteAssignmentLevel || !tRhs.EType.HasCompilableValue) {
            // this is allowed only if the array size is such that it has no elements
            Bpl.Expr zeroSize = Bpl.Expr.False;
            foreach (Expression dim in tRhs.ArrayDimensions) {
              zeroSize = BplOr(zeroSize, Bpl.Expr.Eq(Bpl.Expr.Literal(0), etran.TrExpr(dim)));
            }
            builder.Add(Assert(tRhs.Tok, zeroSize,
              string.Format("unless an initializer is provided for the array elements, a new array of '{0}' must have empty size", tRhs.EType)));
          }
        }

        Bpl.IdentifierExpr nw = GetNewVar_IdExpr(tok, locals);
        if (!callsConstructor) {
          SelectAllocateObject(tok, nw, tRhs.Type, true, builder, etran);
          if (tRhs.ArrayDimensions != null) {
            int i = 0;
            foreach (Expression dim in tRhs.ArrayDimensions) {
              // assume Array#Length($nw, i) == arraySize;
              Bpl.Expr arrayLength = ArrayLength(tok, nw, tRhs.ArrayDimensions.Count, i);
              builder.Add(TrAssumeCmd(tok, Bpl.Expr.Eq(arrayLength, etran.TrExpr(dim))));
              i++;
            }
            if (tRhs.ElementInit != null) {
              CheckElementInit(tok, true, tRhs.ArrayDimensions, tRhs.EType, tRhs.ElementInit, nw, builder, etran, new WFOptions());
            } else if (tRhs.InitDisplay != null) {
              int ii = 0;
              foreach (var v in tRhs.InitDisplay) {
                var EE_ii = etran.TrExpr(v);
                // assert EE_ii satisfies any subset-type constraints;
                CheckSubrange(v.tok, EE_ii, v.Type, tRhs.EType, builder);
                // assume nw[ii] == EE_ii;
                var ai = ReadHeap(tok, etran.HeapExpr, nw, GetArrayIndexFieldName(tok, new List<Bpl.Expr> { Bpl.Expr.Literal(ii) }));
                builder.Add(new Bpl.AssumeCmd(tok, Bpl.Expr.Eq(UnboxIfBoxed(ai, tRhs.EType), EE_ii)));
                ii++;
              }
            }
          }
          Bpl.Cmd heapAllocationRecorder = null;
          if (codeContext is IteratorDecl) {
            var iter = (IteratorDecl)codeContext;
            // $Heap[this, _new] := Set#UnionOne<BoxType>($Heap[this, _new], $Box($nw));
            var th = new Bpl.IdentifierExpr(tok, etran.This, predef.RefType);
            var nwField = new Bpl.IdentifierExpr(tok, GetField(iter.Member_New));
            var thisDotNew = ReadHeap(tok, etran.HeapExpr, th, nwField);
            var unionOne = FunctionCall(tok, BuiltinFunction.SetUnionOne, predef.BoxType, thisDotNew, FunctionCall(tok, BuiltinFunction.Box, null, nw));
            var heapRhs = ExpressionTranslator.UpdateHeap(tok, etran.HeapExpr, th, nwField, unionOne);
            heapAllocationRecorder = Bpl.Cmd.SimpleAssign(tok, (Bpl.IdentifierExpr/*TODO: this cast is dubious*/)etran.HeapExpr, heapRhs);
          }
          CommitAllocatedObject(tok, nw, heapAllocationRecorder, builder, etran);
        }
        if (tRhs.InitCall != null) {
          AddComment(builder, tRhs.InitCall, "init call statement");
          TrCallStmt(tRhs.InitCall, builder, locals, etran, nw);
        }
        // bLhs := $nw;
        CheckSubrange(tok, nw, tRhs.Type, rhsTypeConstraint, builder);
        if (bGivenLhs != null) {
          Contract.Assert(bGivenLhs == bLhs);
          // box the RHS, then do the assignment
          builder.Add(Bpl.Cmd.SimpleAssign(tok, bGivenLhs, CondApplyBox(tok, nw, tRhs.Type, lhsType)));
          return bGivenLhs;
        } else {
          // do the assignment, then box the result
          builder.Add(Bpl.Cmd.SimpleAssign(tok, bLhs, nw));
          return CondApplyBox(tok, bLhs, tRhs.Type, lhsType);
        }
      }
    }

    /// <summary>
    /// Check that all indices are in the domain of the given function.  That is, for an array ("forArray"):
    ///     assert (forall i0,i1,i2,... :: 0 <= i0 < dims[0] && ... ==> init.requires(i0,i1,i2,...));
    /// and for a sequence ("!forArray"):
    ///     assert (forall i0 :: 0 <= i0 < dims[0] && ... ==> init.requires(i0));
    /// </summary>
    private void CheckElementInit(IToken tok, bool forArray, List<Expression> dims, Type elementType, Expression init,
      Bpl.IdentifierExpr/*?*/ nw, BoogieStmtListBuilder builder, ExpressionTranslator etran, WFOptions options) {
      Contract.Requires(tok != null);
      Contract.Requires(dims != null && dims.Count != 0);
      Contract.Requires(elementType != null);
      Contract.Requires(init != null);
      Contract.Requires(!forArray || nw != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);

      Bpl.Expr ante = Bpl.Expr.True;
      var varNameGen = CurrentIdGenerator.NestedFreshIdGenerator(forArray ? "arrayinit#" : "seqinit#");
      var bvs = new List<Bpl.Variable>();
      var indices = new List<Bpl.Expr>();
      for (var i = 0; i < dims.Count; i++) {
        var nm = varNameGen.FreshId(string.Format("#i{0}#", i));
        var bv = new Bpl.BoundVariable(tok, new Bpl.TypedIdent(tok, nm, Bpl.Type.Int));
        bvs.Add(bv);
        var ie = new Bpl.IdentifierExpr(tok, bv);
        indices.Add(ie);
        ante = BplAnd(ante, BplAnd(Bpl.Expr.Le(Bpl.Expr.Literal(0), ie), Bpl.Expr.Lt(ie, etran.TrExpr(dims[i]))));
      }

      var sourceType = init.Type.AsArrowType;
      Contract.Assert(sourceType.Args.Count == dims.Count);
      var args = Concat(
        Map(Enumerable.Range(0, dims.Count), ii => TypeToTy(sourceType.Args[ii])),
        Cons(TypeToTy(sourceType.Result),
          Cons(etran.HeapExpr,
            Cons(etran.TrExpr(init),
              indices.ConvertAll(idx => (Bpl.Expr) FunctionCall(tok, BuiltinFunction.Box, null, idx))))));
      // check precond
      var pre = FunctionCall(tok, Requires(dims.Count), Bpl.Type.Bool, args);
      var q = new Bpl.ForallExpr(tok, bvs, Bpl.Expr.Imp(ante, pre));
      builder.Add(AssertNS(tok, q, string.Format("all {0} indices must be in the domain of the initialization function", forArray ? "array" : "sequence")));
      if (!forArray && options.DoReadsChecks) {
        // check read effects
        Type objset = new SetType(true, program.BuiltIns.ObjectQ());
        Expression wrap = new BoogieWrapper(
          FunctionCall(tok, Reads(1), TrType(objset), args),
          objset);
        var reads = new FrameExpression(tok, wrap, null);
        Action<IToken, Bpl.Expr, string, Bpl.QKeyValue> maker = (t, e, s, qk) => {
          var qe = new Bpl.ForallExpr(t, bvs, Bpl.Expr.Imp(ante, e));
          options.AssertSink(this, builder)(t, qe, s, qk);
        };
        CheckFrameSubset(tok, new List<FrameExpression> { reads }, null, null,
          etran, maker,
          "insufficient reads clause to invoke the function passed as an argument to the sequence constructor",
          options.AssertKv);
      }
      // Check that the values coming out of the function satisfy any appropriate subset-type constraints
      var apply = UnboxIfBoxed(FunctionCall(tok, Apply(dims.Count), TrType(elementType), args), elementType);
      string msg;
      var cre = GetSubrangeCheck(apply, sourceType.Result, elementType, out msg);
      if (cre != null) {
        // assert (forall i0,i1,i2,... ::
        //            0 <= i0 < ... && ... ==> init.requires(i0,i1,i2,...) is Subtype);
        q = new Bpl.ForallExpr(tok, bvs, Bpl.Expr.Imp(ante, cre));
        builder.Add(AssertNS(init.tok, q, msg));
      }

      if (forArray) {
        // Assume that array elements have initial values according to the given initialization function.  That is:
        // assume (forall i0,i1,i2,... :: { nw[i0,i1,i2,...] }
        //            0 <= i0 < ... && ... ==> nw[i0,i1,i2,...] == init.requires(i0,i1,i2,...));
        var ai = ReadHeap(tok, etran.HeapExpr, nw, GetArrayIndexFieldName(tok, indices));
        var ai_prime = UnboxIfBoxed(ai, elementType);
        var tr = new Bpl.Trigger(tok, true, new List<Bpl.Expr> {ai});
        q = new Bpl.ForallExpr(tok, bvs, tr,
          Bpl.Expr.Imp(ante, Bpl.Expr.Eq(ai_prime, apply))); // TODO: use a more general Equality translation
        builder.Add(new Bpl.AssumeCmd(tok, q));
      }
    }

    private void SelectAllocateObject(IToken tok, Bpl.IdentifierExpr nw, Type type, bool includeHavoc, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(nw != null);
      Contract.Requires(type != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is NonNullTypeDecl) {
        var nnt = (NonNullTypeDecl)udt.ResolvedClass;
        type = nnt.RhsWithArgument(type.TypeArgs);
      }
      if (includeHavoc) {
        // havoc $nw;
        builder.Add(new Bpl.HavocCmd(tok, new List<Bpl.IdentifierExpr> { nw }));
        // assume $nw != null && dtype($nw) == RHS;
        var nwNotNull = Bpl.Expr.Neq(nw, predef.Null);
        var rightType = DType(nw, TypeToTy(type));
        builder.Add(TrAssumeCmd(tok, Bpl.Expr.And(nwNotNull, rightType)));
      }
      // assume !$Heap[$nw, alloc];
      var notAlloc = Bpl.Expr.Not(etran.IsAlloced(tok, nw));
      builder.Add(TrAssumeCmd(tok, notAlloc));
    }

    private void CommitAllocatedObject(IToken tok, Bpl.IdentifierExpr nw, Bpl.Cmd extraCmd, BoogieStmtListBuilder builder, ExpressionTranslator etran) {
      Contract.Requires(tok != null);
      Contract.Requires(nw != null);
      Contract.Requires(builder != null);
      Contract.Requires(etran != null);

      // $Heap[$nw, alloc] := true;
      Bpl.Expr alloc = predef.Alloc(tok);
      Bpl.IdentifierExpr heap = (Bpl.IdentifierExpr/*TODO: this cast is dubious*/)etran.HeapExpr;
      Bpl.Cmd cmd = Bpl.Cmd.SimpleAssign(tok, heap, ExpressionTranslator.UpdateHeap(tok, heap, nw, alloc, Bpl.Expr.True));
      builder.Add(cmd);
      if (extraCmd != null) {
        builder.Add(extraCmd);
      }
      // assume $IsGoodHeap($Heap);
      builder.Add(AssumeGoodHeap(tok, etran));
      // assume $IsHeapAnchor($Heap);
      builder.Add(new Bpl.AssumeCmd(tok, FunctionCall(tok, BuiltinFunction.IsHeapAnchor, null, etran.HeapExpr)));
    }

    /// <summary>
    /// Returns the name of the local variable used as a stand-in for a field in the BodyInit part of a divided
    /// constructor body.
    /// </summary>
    string SurrogateName(Field field) {
      Contract.Requires(field != null);
      return "this." + field.Name;
    }

    Bpl.Expr GetSubrangeCheck(Bpl.Expr bSource, Type sourceType, Type targetType, out string msg) {
      Contract.Requires(bSource != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(targetType != null);

      if (Type.IsSupertype(targetType, sourceType)) {
        // We should always be able to use Is, but this is an optimisation.
        msg = null;
        return null;
      }
      targetType = targetType.NormalizeExpandKeepConstraints();
      var cre = MkIs(bSource, targetType);
      var udt = targetType as UserDefinedType;
      if (udt != null && udt.IsRefType) {
        msg = string.Format("value of expression (of type '{0}') is not known to be an instance of type '{1}'", sourceType, targetType);
        var s = sourceType.NormalizeExpandKeepConstraints();
        if (s is UserDefinedType sudt && udt.ResolvedClass is NonNullTypeDecl nntd && nntd.Class == sudt.ResolvedClass) {
          var certain = udt.ResolvedClass.TypeArgs.Count == 0;
          msg += certain ? ", because it may be null" : " (possible cause: it may be null)";
        }
      } else if (udt != null && ArrowType.IsTotalArrowTypeName(udt.Name)) {
        msg = string.Format("value does not satisfy the subset constraints of '{0}' (possible cause: it may be partial or have read effects)", targetType.Normalize());
      } else if (udt != null && ArrowType.IsPartialArrowTypeName(udt.Name)) {
        msg = string.Format("value does not satisfy the subset constraints of '{0}' (possible cause: it may have read effects)", targetType.Normalize());
      } else {
        msg = string.Format("value does not satisfy the subset constraints of '{0}'", targetType.Normalize());
      }
      return cre;
    }

    void CheckSubrange(IToken tok, Bpl.Expr bSource, Type sourceType, Type targetType, BoogieStmtListBuilder builder, string errorMsgPrefix = "") {
      Contract.Requires(tok != null);
      Contract.Requires(bSource != null);
      Contract.Requires(sourceType != null);
      Contract.Requires(targetType != null);
      Contract.Requires(builder != null);

      string msg;
      var cre = GetSubrangeCheck(bSource, sourceType, targetType, out msg);
      if (cre != null) {
        builder.Add(Assert(tok, cre, errorMsgPrefix + msg));
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
        var subset = FunctionCall(tok, BuiltinFunction.SetSubset, null, rhs, ReadHeap(tok, etran.HeapExpr, obj, fId));
        builder.Add(Assert(tok, subset, "an assignment to " + f.Name + " is only allowed to shrink the set"));
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
      if (e.getTranslationDesugaring(this) == null) {
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
          e.setTranslationDesugaring(this, Substitute(d, null, expr.substMap, expr.typeMap));
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
            ComputeFreeVariables(e.RHSs[0], FVs, ref usesHeap, ref usesOldHeap, FVsHeapAt, ref usesThis);
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
          // add canCall function
          {
            Bpl.Variable resType = new Bpl.Formal(e.tok, new Bpl.TypedIdent(e.tok, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
            Bpl.Expr ante;
            List<Variable> formals = info.GAsVars(this, true, out ante, null);
            var fn = new Bpl.Function(e.tok, info.CanCallFunctionName(), formals, resType);

            if (InsertChecksums) {
              InsertChecksum(e.Body, fn);
            }

            sink.AddTopLevelDeclaration(fn);
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
            sink.AddTopLevelDeclaration(new Bpl.Axiom(e.tok, ax));
          }

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
            e.setTranslationDesugaring(this, expr);
          }
        }
      }
      return e.getTranslationDesugaring(this);
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
        FV_Exprs = template.FV_Exprs.ConvertAll(e => Translator.Substitute(e, null, substMap, typeMap));
        UsesHeap = template.UsesHeap;
        UsesOldHeap = template.UsesOldHeap;
        UsesHeapAt = template.UsesHeapAt;
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
        foreach (var heapAtLabel in UsesHeapAt) {
          Bpl.Expr ve;
          var bv = BplBoundVar("$Heap_at_" + heapAtLabel.AssignUniqueId(translator.CurrentIdGenerator), translator.predef.HeapType, out ve);
          gExprs.Add(ve);
        }
        if (ThisType != null) {
          var th = new Bpl.IdentifierExpr(Tok, etran.This);
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
        foreach (var heapAtLabel in UsesHeapAt) {
          var nv = NewVar("$Heap_at_" + heapAtLabel.AssignUniqueId(translator.CurrentIdGenerator), translator.predef.HeapType, wantFormals);
          vv.Add(nv);
          if (etran != null) {
            // TODO: It's not clear to me that $IsGoodHeap predicates are needed for these axioms. (Same comment applies above for $heap$old.)
            // But $HeapSucc relations among the various heap variables appears not needed for either soundness or completeness, since the
            // let-such-that functions will always be invoked on arguments for which these properties are known.
            var isGoodHeap = translator.FunctionCall(Tok, BuiltinFunction.IsGoodHeap, null, new Bpl.IdentifierExpr(Tok, nv));
            typeAntecedents = BplAnd(typeAntecedents, isGoodHeap);
          }
        }
        if (ThisType != null) {
          var nv = NewVar("this", translator.TrType(ThisType), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var th = new Bpl.IdentifierExpr(Tok, nv);
            typeAntecedents = BplAnd(typeAntecedents, translator.ReceiverNotNull(th));
            var wh = translator.GetWhereClause(Tok, th, ThisType, etran, NOALLOC);
            if (wh != null) {
              typeAntecedents = BplAnd(typeAntecedents, wh);
            }
          }
        }
        foreach (var v in FVs) {
          var nv = NewVar(v.Name, translator.TrType(v.Type), wantFormals);
          vv.Add(nv);
          if (etran != null) {
            var wh = translator.GetWhereClause(Tok, new Bpl.IdentifierExpr(Tok, nv), v.Type, etran, NOALLOC);
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
      public readonly List<Label> HeapAtLabels;
      public readonly List<Type> TyArgs; // Note: also has a bunch of type arguments
      public readonly List<Expression> Args;
      public BoogieFunctionCall(IToken tok, string functionName, bool usesHeap, bool usesOldHeap, List<Label> heapAtLabels, List<Expression> args, List<Type> tyArgs)
        : base(tok)
      {
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
        : base(tok, lhss, rhss, body, exact)
      {
        this.orgExpr = orgExpr;
        this.substMap = substMap;
        this.typeMap = typeMap;
        this.Constraint_Bounds = constraintBounds;
      }
    }

    internal class BoogieStmtListBuilder
    {
      public Bpl.StmtListBuilder builder;
      public Translator tran;

      public BoogieStmtListBuilder(Translator tran) {
        builder = new Bpl.StmtListBuilder();
        this.tran = tran;
      }

      public void Add(Cmd cmd) {
        builder.Add(cmd);
        if (cmd is Bpl.AssertCmd) {
          tran.assertionCount++;
        } else if (cmd is Bpl.CallCmd call) {
          // A call command may involve a precondition, but we can't tell for sure until the callee
          // procedure has been generated. Therefore, to be on the same side, we count this call
          // as a possible assertion, unless it's a procedure that's part of the translation and
          // known not to have any preconditions.
          if (call.callee == "$IterHavoc0" || call.callee == "$IterHavoc1" || call.callee == "$YieldHavoc") {
            // known not to have any preconditions
          } else {
            tran.assertionCount++;
          }
        }
      }
      public void Add(StructuredCmd scmd) { builder.Add(scmd); }
      public void Add(TransferCmd tcmd) { builder.Add(tcmd);  }
      public void AddLabelCmd(string label) { builder.AddLabelCmd(label); }
      public void AddLocalVariable(string name) { builder.AddLocalVariable(name); }

      public StmtList Collect(IToken tok) {
        return builder.Collect(tok);
      }
    }

    internal class FuelSettingPair
    {
      public int low;
      public int high;

      public FuelSettingPair(int low = (int)FuelSetting.FuelAmount.LOW, int high = (int)FuelSetting.FuelAmount.HIGH) {
        this.low = low;
        this.high = high;
      }
    }

    // C#'s version of a type alias
    internal class FuelContext : Dictionary<Function, FuelSettingPair> { }
    internal class CustomFuelSettings : Dictionary<Function, FuelSetting> {}

    internal class FuelConstant
    {
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

    internal class FuelSetting
    {
      public enum FuelAmount { NONE, LOW, HIGH };
      public static Stack<FuelContext> SavedContexts = new Stack<FuelContext>();

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
      private Translator translator;
      private CustomFuelSettings customFuelSettings;

      public FuelSetting(Translator translator, int amount, Bpl.Expr start = null, CustomFuelSettings customFuelSettings = null) {
        this.translator = translator;
        this.amount = amount;
        this.start = start;
        this.customFuelSettings = customFuelSettings;
      }

      public FuelSetting Offset(int offset) {
        return new FuelSetting(translator, this.amount + offset, start);
      }

      public FuelSetting Decrease(int offset) {
        Contract.Ensures(this.amount - offset >= 0);
        return new FuelSetting(translator, this.amount - offset, start);
      }

      public FuelSetting WithLayer(Bpl.Expr layer) {
        return new FuelSetting(translator, amount, layer);
      }

      public FuelSetting WithContext(CustomFuelSettings settings) {
        return new FuelSetting(translator, amount, start, settings);
      }

      public Bpl.Expr LayerZero() {
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$LZ", translator.predef.LayerType);
      }

      public Bpl.Expr LayerN(int n) {
        Contract.Requires(0 <= n);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return translator.LayerSucc(LayerZero(), n);
      }

      public Bpl.Expr LayerN(int n, Bpl.Expr baseLayer) {
        Contract.Requires(0 <= n);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        return translator.LayerSucc(baseLayer, n);
      }

      private Bpl.Expr ToExpr(int amount) {
        if (start == null) {
          return LayerN(amount);
        } else {
          return translator.LayerSucc(start, amount);
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
        if (customFuelSettings != null && customFuelSettings.ContainsKey(f)) {
          return customFuelSettings[f].GetFunctionFuel(f);
        }
        if (this.amount == (int)FuelAmount.NONE) {
          return this.ToExpr();
        } else {
          FuelSettingPair setting = null;
          var found = translator.fuelContext.TryGetValue(f, out setting);

          if (!found) {  // If the context doesn't define fuel for this function, check for a fuel attribute (which supplies a default value if none is found)
            setting = FuelAttrib(f, out found);
          }

          FuelConstant fuelConstant = translator.functionFuel.Find(x => x.f == f);
          if (this.amount == (int)FuelAmount.LOW) {
            return GetFunctionFuel(setting.low > 0 ? setting.low   : this.amount, found, fuelConstant);
          } else if (this.amount >= (int)FuelAmount.HIGH) {
            return GetFunctionFuel(setting.high > 0 ? setting.high : this.amount, found, fuelConstant);
          } else {
            Contract.Assert(false); // Should not reach here
            return null;
          }
        }
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
        Contract.Ensures(SavedContexts.Count == Contract.OldValue(SavedContexts.Count) + 1);
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
              reporter.Error(MessageSource.Translator, tok, "Fuel can only increase within a given scope.");
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
        SavedContexts.Push(oldFuelContext);

        return newContext;
      }

      public static FuelContext PopFuelContext() {
        Contract.Requires(SavedContexts.Count > 0);
        return SavedContexts.Pop();
      }

    }

    internal enum IsAllocType { ISALLOC, NOALLOC, NEVERALLOC };  // NEVERALLOC is like NOALLOC, but overrides AlwaysAlloc
    static IsAllocType ISALLOC { get { return IsAllocType.ISALLOC; } }
    static IsAllocType NOALLOC { get { return IsAllocType.NOALLOC; } }

    internal class IsAllocContext
    {
      internal bool allVarsGhost;

      internal IsAllocContext(bool allVarsGhost) {
        this.allVarsGhost = allVarsGhost;
      }

      internal static IsAllocType Var(bool isGhost) {
        return (CommonHeapUse || (NonGhostsUseHeap && !isGhost)) ? ISALLOC : NOALLOC;
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

    internal class ExpressionTranslator
    {
      // HeapExpr == null ==> translation of pure (no-heap) expression
      readonly Bpl.Expr _the_heap_expr;
      public Bpl.Expr HeapExpr {
        // The increment of Statistics_HeapUses in the following line is a hack and not entirely a good idea.
        // Not only does one need to be careful not to mention HeapExpr in contracts (in particular, in ObjectInvariant()
        // below), but also, the debugger may invoke HeapExpr and that will cause an increment as well.
        get { Statistics_HeapUses++; return _the_heap_expr; }
      }
      public readonly PredefinedDecls predef;
      public readonly Translator translator;
      public readonly string This;
      public readonly string modifiesFrame; // the name of the context's frame variable.
      readonly Function applyLimited_CurrentFunction;
      public readonly FuelSetting layerInterCluster;
      public readonly FuelSetting layerIntraCluster = null;  // a value of null says to do the same as for inter-cluster calls
      public int Statistics_CustomLayerFunctionCount = 0;
      public int Statistics_HeapAsQuantifierCount = 0;
      public int Statistics_HeapUses = 0;
      public readonly bool stripLits = false;
      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        // In the following line, it is important to use _the_heap_expr directly, rather than HeapExpr, because
        // the HeapExpr getter has a side effect on Statistics_HeapUses.
        Contract.Invariant(_the_heap_expr == null || _the_heap_expr is Bpl.OldExpr || _the_heap_expr is Bpl.IdentifierExpr);
        Contract.Invariant(predef != null);
        Contract.Invariant(translator != null);
        Contract.Invariant(This != null);
        Contract.Invariant(modifiesFrame != null);
        Contract.Invariant(layerInterCluster != null);
        Contract.Invariant(0 <= Statistics_CustomLayerFunctionCount);
      }

      /// <summary>
      /// This is the most general constructor.  It is private and takes all the parameters.  Whenever
      /// one ExpressionTranslator is constructed from another, unchanged parameters are just copied in.
      /// </summary>
      ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, string modifiesFrame, bool stripLits) {

        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
        Contract.Requires(modifiesFrame != null);

        this.translator = translator;
        this.predef = predef;
        this._the_heap_expr = heap;
        this.This = thisVar;
        this.applyLimited_CurrentFunction = applyLimited_CurrentFunction;
        this.layerInterCluster = layerInterCluster;
        if (layerIntraCluster == null) {
          this.layerIntraCluster = layerInterCluster;
        } else {
          this.layerIntraCluster = layerIntraCluster;
        }
        this.modifiesFrame = modifiesFrame;
        this.stripLits = stripLits;
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
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, Bpl.Expr oldHeap)
        : this(translator, predef, heap, "this") {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(oldHeap != null);

        var old = new ExpressionTranslator(translator, predef, oldHeap);
        old.oldEtran = old;
        this.oldEtran = old;
      }

      public ExpressionTranslator(Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar)
        : this(translator, predef, heap, thisVar, null, new FuelSetting(translator, 1), null, "$_Frame", false) {
        Contract.Requires(translator != null);
        Contract.Requires(predef != null);
        Contract.Requires(thisVar != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, Bpl.Expr heap)
        : this(etran.translator, etran.predef, heap, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, etran.modifiesFrame, etran.stripLits)
      {
        Contract.Requires(etran != null);
      }

      public ExpressionTranslator(ExpressionTranslator etran, string modifiesFrame)
        : this(etran.translator, etran.predef, etran.HeapExpr, etran.This, etran.applyLimited_CurrentFunction, etran.layerInterCluster, etran.layerIntraCluster, modifiesFrame, etran.stripLits) {
        Contract.Requires(etran != null);
        Contract.Requires(modifiesFrame != null);
      }

      ExpressionTranslator oldEtran;
      public ExpressionTranslator Old {
        get {
          Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

          if (oldEtran == null) {
            oldEtran = new ExpressionTranslator(translator, predef, new Bpl.OldExpr(HeapExpr.tok, HeapExpr), This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
            oldEtran.oldEtran = oldEtran;
          }
          return oldEtran;
        }
      }

      public ExpressionTranslator OldAt(Label/*?*/ label) {
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);
        if (label == null) {
          return Old;
        }
        var heapAt = new Bpl.IdentifierExpr(Token.NoToken, "$Heap_at_" + label.AssignUniqueId(translator.CurrentIdGenerator), predef.HeapType);
        return new ExpressionTranslator(translator, predef, heapAt, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
      }

      public bool UsesOldHeap {
        get {
          return HeapExpr is Bpl.OldExpr || (HeapExpr is Bpl.IdentifierExpr ide && ide.Name.StartsWith("$Heap_at_"));
        }
      }

      public ExpressionTranslator WithLayer(Bpl.Expr layerArgument)
      {
        // different layer and 0 fuel amount.
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, null, new FuelSetting(translator, 0, layerArgument), new FuelSetting(translator, 0, layerArgument), modifiesFrame, stripLits);
      }

      public ExpressionTranslator WithCustomFuelSetting(CustomFuelSettings customSettings) {
        // Use the existing layers but with some per-function customizations
        Contract.Requires(customSettings != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, null, layerInterCluster.WithContext(customSettings), layerIntraCluster.WithContext(customSettings), modifiesFrame, stripLits);
      }

      public ExpressionTranslator ReplaceLayer(Bpl.Expr layerArgument) {
        // different layer with same fuel amount.
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.WithLayer(layerArgument), layerIntraCluster.WithLayer(layerArgument), modifiesFrame, stripLits);
       }

      public ExpressionTranslator WithNoLits() {
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);
        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, true);
      }

      public ExpressionTranslator LimitedFunctions(Function applyLimited_CurrentFunction, Bpl.Expr layerArgument) {
        Contract.Requires(applyLimited_CurrentFunction != null);
        Contract.Requires(layerArgument != null);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, /* layerArgument */ layerInterCluster, new FuelSetting(translator, 0, layerArgument), modifiesFrame, stripLits);
      }

      public ExpressionTranslator LayerOffset(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Offset(offset), layerIntraCluster, modifiesFrame, stripLits);
      }

      public ExpressionTranslator DecreaseFuel(int offset) {
        Contract.Requires(0 <= offset);
        Contract.Ensures(Contract.Result<ExpressionTranslator>() != null);

        return CloneExpressionTranslator(this, translator, predef, HeapExpr, This, applyLimited_CurrentFunction, layerInterCluster.Decrease(offset), layerIntraCluster, modifiesFrame, stripLits);
      }

      private static ExpressionTranslator CloneExpressionTranslator(ExpressionTranslator orig,
        Translator translator, PredefinedDecls predef, Bpl.Expr heap, string thisVar,
        Function applyLimited_CurrentFunction, FuelSetting layerInterCluster, FuelSetting layerIntraCluster, string modifiesFrame, bool stripLits) {
        var et = new ExpressionTranslator(translator, predef, heap, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
        if (orig.oldEtran != null) {
          var etOld = new ExpressionTranslator(translator, predef, orig.Old.HeapExpr, thisVar, applyLimited_CurrentFunction, layerInterCluster, layerIntraCluster, modifiesFrame, stripLits);
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

      public Bpl.IdentifierExpr FunctionContextHeight() {
        Contract.Ensures(Contract.Result<Bpl.IdentifierExpr>().Type != null);
        return new Bpl.IdentifierExpr(Token.NoToken, "$FunctionContextHeight", Bpl.Type.Int);
      }

      public Bpl.Expr HeightContext(ICallable m)
      {
        Contract.Requires(m != null);
        // free requires fh == FunctionContextHeight;
        var module = m.EnclosingModule;
        Bpl.Expr context =
          Bpl.Expr.Eq(Bpl.Expr.Literal(module.CallGraph.GetSCCRepresentativeId(m)), FunctionContextHeight());
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
        return Translator.Substitute(e.Body, null, substMap);
      }

      public Expr MaybeLit(Expr expr, Bpl.Type type) {
        return stripLits ? expr : translator.Lit(expr, type);
      }

      public Expr MaybeLit(Expr expr) {
        return stripLits ? expr : translator.Lit(expr);
      }

      /// <summary>
      /// Translates Dafny expression "expr" into a Boogie expression.  If the type of "expr" can be a boolean, then the
      /// token (source location) of the resulting expression is filled in (it wouldn't hurt if the token were always
      /// filled in, but it is really necessary for anything that may show up in a Boogie assert, since that location may
      /// then show up in an error message).
      /// </summary>
      public Bpl.Expr TrExpr(Expression expr) {
        Contract.Requires(expr != null);
        Contract.Requires(predef != null);

        if (expr is LiteralExpr) {
          LiteralExpr e = (LiteralExpr)expr;
          if (e.Value == null) {
            return predef.Null;
          } else if (e.Value is bool) {
            return MaybeLit(new Bpl.LiteralExpr(e.tok, (bool)e.Value));
          } else if (e is CharLiteralExpr) {
            // we expect e.Value to be a string representing exactly one char
            Bpl.Expr rawElement = null;  // assignment to please compiler's definite assignment rule
            foreach (char ch in Util.UnescapedCharacters((string)e.Value, false)) {
              Contract.Assert(rawElement == null);  // we should get here only once
              rawElement = translator.FunctionCall(expr.tok, BuiltinFunction.CharFromInt, null, Bpl.Expr.Literal((int)ch));
            }
            Contract.Assert(rawElement != null);  // there should have been an iteration of the loop above
            return MaybeLit(rawElement, predef.CharType);
          } else if (e is StringLiteralExpr) {
            var str = (StringLiteralExpr)e;
            Bpl.Expr seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqEmpty, predef.BoxType);
            foreach (char ch in Util.UnescapedCharacters((string)e.Value, str.IsVerbatim)) {
              var rawElement = translator.FunctionCall(expr.tok, BuiltinFunction.CharFromInt, null, Bpl.Expr.Literal((int)ch));
              Bpl.Expr elt = BoxIfNecessary(expr.tok, rawElement, Type.Char);
              seq = translator.FunctionCall(expr.tok, BuiltinFunction.SeqBuild, predef.BoxType, seq, elt);
            }
            return MaybeLit(seq, translator.TrType(new SeqType(Type.Char)));
          } else if (e.Value is BigInteger) {
            var n = Microsoft.BaseTypes.BigNum.FromBigInt((BigInteger)e.Value);
            if (e.Type is BitvectorType) {
              return MaybeLit(translator.BplBvLiteralExpr(e.tok, n, (BitvectorType)e.Type));
            } else if (e.Type.IsBigOrdinalType) {
              var fromNat = translator.FunctionCall(expr.tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(n));
              return MaybeLit(fromNat, predef.BigOrdinalType);
            } else {
              return MaybeLit(Bpl.Expr.Literal(n));
            }
          } else if (e.Value is BaseTypes.BigDec) {
            return MaybeLit(Bpl.Expr.Literal((BaseTypes.BigDec)e.Value));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal
          }

        } else if (expr is ThisExpr) {
          return new Bpl.IdentifierExpr(expr.tok, This, translator.TrType(expr.Type));

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
          foreach (var heapAtLabel in e.HeapAtLabels) {
            Bpl.Expr ve;
            var bv = BplBoundVar("$Heap_at_" + heapAtLabel.AssignUniqueId(translator.CurrentIdGenerator), translator.predef.HeapType, out ve);
            args.Add(ve);
          }
          foreach (var arg in e.Args) {
            args.Add(TrExpr(arg));
          }
          return new Bpl.NAryExpr(e.tok, new Bpl.FunctionCall(id), args);

        } else if (expr is SetDisplayExpr) {
          SetDisplayExpr e = (SetDisplayExpr)expr;
          Bpl.Expr s = translator.FunctionCall(expr.tok, e.Finite ? BuiltinFunction.SetEmpty : BuiltinFunction.ISetEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Bpl.Expr ss = BoxIfNecessary(expr.tok, rawElement, cce.NonNull(ee.Type));
            s = translator.FunctionCall(expr.tok, e.Finite ? BuiltinFunction.SetUnionOne : BuiltinFunction.ISetUnionOne, predef.BoxType, s, ss);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the set is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MultiSetDisplayExpr) {
          MultiSetDisplayExpr e = (MultiSetDisplayExpr)expr;
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Bpl.Expr ss = BoxIfNecessary(expr.tok, rawElement, cce.NonNull(ee.Type));
            s = translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetUnionOne, predef.BoxType, s, ss);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the multiset is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is SeqDisplayExpr) {
          SeqDisplayExpr e = (SeqDisplayExpr)expr;
          // Note: a LiteralExpr(string) is really another kind of SeqDisplayExpr
          Bpl.Expr s = translator.FunctionCall(expr.tok, BuiltinFunction.SeqEmpty, predef.BoxType);
          var isLit = true;
          foreach (Expression ee in e.Elements) {
            var rawElement = TrExpr(ee);
            isLit = isLit && translator.IsLit(rawElement);
            Bpl.Expr elt = BoxIfNecessary(expr.tok, rawElement, ee.Type);
            s = translator.FunctionCall(expr.tok, BuiltinFunction.SeqBuild, predef.BoxType, s, elt);
          }
          if (isLit) {
            // Lit-lifting: All elements are lit, so the sequence is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MapDisplayExpr) {
          MapDisplayExpr e = (MapDisplayExpr)expr;
          Bpl.Type maptype = predef.MapType(expr.tok, e.Finite, predef.BoxType, predef.BoxType);
          Bpl.Expr s = translator.FunctionCall(expr.tok, e.Finite ? BuiltinFunction.MapEmpty : BuiltinFunction.IMapEmpty, predef.BoxType);
          var isLit = true;
          foreach (ExpressionPair p in e.Elements) {
            var rawA = TrExpr(p.A);
            var rawB = TrExpr(p.B);
            isLit = isLit && translator.IsLit(rawA) && translator.IsLit(rawB);
            Bpl.Expr elt = BoxIfNecessary(expr.tok, rawA, cce.NonNull(p.A.Type));
            Bpl.Expr elt2 = BoxIfNecessary(expr.tok, rawB, cce.NonNull(p.B.Type));
            s = translator.FunctionCall(expr.tok, e.Finite ? "Map#Build" : "IMap#Build", maptype, s, elt, elt2);
          }
          if (isLit) {
            // Lit-lifting: All keys and values are lit, so the map is Lit too
            s = MaybeLit(s, predef.BoxType);
          }
          return s;

        } else if (expr is MemberSelectExpr) {
          var e = (MemberSelectExpr)expr;
          return e.MemberSelectCase(
            field => {
              var useSurrogateLocal = translator.inBodyInitContext && Expression.AsThis(e.Obj) != null && !field.IsInstanceIndependentConstant;
              if (useSurrogateLocal) {
                return new Bpl.IdentifierExpr(expr.tok, translator.SurrogateName(field), translator.TrType(field.Type));
              } else if (field is ConstantField) {
                var typeMap = e.TypeArgumentSubstitutionsWithParents();
                var args = GetTypeParams(field.EnclosingClass).ConvertAll(tp => translator.TypeToTy(typeMap[tp]));
                Bpl.Expr result;
                if (field.IsStatic) {
                  result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(translator.GetReadonlyField(field)), args);
                } else {
                  Bpl.Expr obj = TrExpr(e.Obj);
                  args.Add(obj);
                  result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(translator.GetReadonlyField(field)), args);
                }
                result = translator.CondApplyUnbox(expr.tok, result, field.Type, expr.Type);
                return result;
              } else {
                Bpl.Expr obj = TrExpr(e.Obj);
                Bpl.Expr result;
                if (field.IsMutable) {
                  result = ReadHeap(expr.tok, HeapExpr, obj, new Bpl.IdentifierExpr(expr.tok, translator.GetField(field)));
                  return translator.CondApplyUnbox(expr.tok, result, field.Type, expr.Type);
                } else {
                  result = new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(translator.GetReadonlyField(field)),
                    new List<Bpl.Expr> { obj });
                  result = translator.CondApplyUnbox(expr.tok, result, field.Type, expr.Type);
                  if (translator.IsLit(obj)) {
                    result = MaybeLit(result, translator.TrType(expr.Type));
                  }
                  return result;
                }
              }
            },
            fn => {
              var typeMap = e.TypeArgumentSubstitutionsWithParents();
              var args = GetTypeParams(fn).ConvertAll(tp => translator.TypeToTy(typeMap[tp]));
              if (fn.IsFuelAware()) {
                args.Add(this.layerInterCluster.GetFunctionFuel(fn));
              }
              if (fn is TwoStateFunction) {
                args.Add(Old.HeapExpr);
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
          if (e0 != null && e.E0.Type.IsBitVectorType) {
            e0 = translator.ConvertExpression(e.E0.tok, e0, e.E0.Type, Type.Int);
          }
          Bpl.Expr e1 = e.E1 == null ? null : TrExpr(e.E1);
          if (e1 != null && e.E1.Type.IsBitVectorType) {
            e1 = translator.ConvertExpression(e.E1.tok, e1, e.E1.Type, Type.Int);
          }
          if (e.SelectOne) {
            Contract.Assert(e1 == null);
            Bpl.Expr x;
            if (seqType.IsArrayType) {
              Bpl.Expr fieldName = translator.FunctionCall(expr.tok, BuiltinFunction.IndexField, null, e0);
              x = ReadHeap(expr.tok, HeapExpr, TrExpr(e.Seq), fieldName);
            } else if (seqType is SeqType) {
              x = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.BoxType, seq, e0);
            } else if (seqType is MapType) {
              bool finite = ((MapType)seqType).Finite;
              var f = finite ? BuiltinFunction.MapElements : BuiltinFunction.IMapElements;
              x = translator.FunctionCall(expr.tok, f, predef.MapType(e.tok, finite, predef.BoxType, predef.BoxType), seq);
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
              seq = MaybeLit(seq, translator.TrType(expr.Type));
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
              index = translator.ConvertExpression(e.Index.tok, index, e.Index.Type, Type.Int);
              Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), elmtType);
              return translator.FunctionCall(expr.tok, BuiltinFunction.SeqUpdate, predef.BoxType, seq, index, val);
            }
            else if (seqType is MapType)
            {
              MapType mt = (MapType)seqType;
              Bpl.Type maptype = predef.MapType(expr.tok, mt.Finite, predef.BoxType, predef.BoxType);
              Bpl.Expr index = BoxIfNecessary(expr.tok, TrExpr(e.Index), mt.Domain);
              Bpl.Expr val = BoxIfNecessary(expr.tok, TrExpr(e.Value), mt.Range);
              return translator.FunctionCall(expr.tok, mt.Finite ? "Map#Build" : "IMap#Build", maptype, seq, index, val);
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
          var tt = e.Function.Type.AsArrowType;
          Contract.Assert(tt != null);
          Contract.Assert(tt.Arity == arity);

          {
            // optimisation: if this could have just as well been a FunctionCallExpr, call it as such!
            var con = e.Function as ConcreteSyntaxExpression;
            var recv = con == null ? e.Function : con.Resolved;
            var mem = recv as MemberSelectExpr;
            var fn = mem == null ? null : mem.Member as Function;
            if (fn != null) {
              return TrExpr(new FunctionCallExpr(e.tok, fn.Name, mem.Obj, e.tok, e.Args) {
                Function = fn,
                Type = e.Type,
                TypeApplication_AtEnclosingClass = mem.TypeApplication_AtEnclosingClass,
                TypeApplication_JustFunction = mem.TypeApplication_JustMember
              });
            }
          }

          Func<Expression, Bpl.Expr> TrArg = arg => translator.BoxIfUnboxed(TrExpr(arg), arg.Type);

          var applied = translator.FunctionCall(expr.tok, Translator.Apply(arity), predef.BoxType,
            Concat(Map(tt.TypeArgs,translator.TypeToTy),
            Cons(HeapExpr, Cons(TrExpr(e.Function), e.Args.ConvertAll(arg => TrArg(arg))))));

          return translator.UnboxIfBoxed(applied, tt.Result);

        } else if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          if (e.Function is SpecialFunction) {
            return TrExprSpecialFunctionCall(e);
          } else {
            Bpl.Expr layerArgument;
            var etran = this;
            if (e.Function.ContainsQuantifier && translator.stmtContext == StmtType.ASSUME && translator.adjustFuelForExists) {
              // we need to increase fuel functions that contain quantifier expr in the assume context.
              etran = etran.LayerOffset(1);
              translator.adjustFuelForExists = false;
            }
            if (e.Function.IsFuelAware()) {
              Statistics_CustomLayerFunctionCount++;
              ModuleDefinition module = e.Function.EnclosingClass.EnclosingModuleDefinition;
              if (etran.applyLimited_CurrentFunction != null &&
                etran.layerIntraCluster != null &&
                ModuleDefinition.InSameSCC(e.Function, applyLimited_CurrentFunction)) {
                layerArgument = etran.layerIntraCluster.GetFunctionFuel(e.Function);
              } else {
                layerArgument = etran.layerInterCluster.GetFunctionFuel(e.Function);
              }
            } else {
              layerArgument = null;
            }

            var ty = translator.TrType(e.Type);
            var id = new Bpl.IdentifierExpr(e.tok, e.Function.FullSanitizedName, ty);

            bool argsAreLit;
            var args = FunctionInvocationArguments(e, layerArgument, false, out argsAreLit);
            Expr result = new Bpl.NAryExpr(e.tok, new Bpl.FunctionCall(id), args);
            result = translator.CondApplyUnbox(e.tok, result, e.Function.ResultType, e.Type);

            bool callIsLit = argsAreLit
              && Translator.FunctionBodyIsAvailable(e.Function, translator.currentModule, translator.currentScope, true)
              && !e.Function.Reads.Any(); // Function could depend on external values
            if (callIsLit) {
              result = MaybeLit(result, ty);
            }

            return result;
          }
        } else if (expr is DatatypeValue) {
          DatatypeValue dtv = (DatatypeValue)expr;
          Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
          List<Bpl.Expr> args = new List<Bpl.Expr>();

          bool argsAreLit = true;
          for (int i = 0; i < dtv.Arguments.Count; i++) {
            Expression arg = dtv.Arguments[i];
            Type t = dtv.Ctor.Formals[i].Type;
            var bArg = TrExpr(arg);
            argsAreLit = argsAreLit && translator.IsLit(bArg);
            args.Add(translator.CondApplyBox(expr.tok, bArg, cce.NonNull(arg.Type), t));
          }
          Bpl.IdentifierExpr id = new Bpl.IdentifierExpr(dtv.tok, dtv.Ctor.FullName, predef.DatatypeType);
          Bpl.Expr ret = new Bpl.NAryExpr(dtv.tok, new Bpl.FunctionCall(id), args);
          if (argsAreLit) {
            // If all arguments are Lit, so is the whole expression
            ret = MaybeLit(ret, predef.DatatypeType);
          }
          return ret;

        } else if (expr is SeqConstructionExpr) {
          var e = (SeqConstructionExpr)expr;
          var eType = e.Type.AsSeqType.Arg.NormalizeExpand();
          return translator.FunctionCall(expr.tok, "Seq#Create", predef.SeqType(e.tok, predef.BoxType), translator.TypeToTy(eType), HeapExpr, TrExpr(e.N), TrExpr(e.Initializer));

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

        } else if (expr is OldExpr) {
          var e = (OldExpr)expr;
          return OldAt(e.AtLabel).TrExpr(e.E);

        } else if (expr is UnchangedExpr) {
          var e = (UnchangedExpr)expr;
          return translator.FrameCondition(e.tok, e.Frame, false, Resolver.FrameExpressionUse.Unchanged, OldAt(e.AtLabel), this, this, true);

        } else if (expr is UnaryOpExpr) {
          var e = (UnaryOpExpr)expr;
          Bpl.Expr arg = TrExpr(e.E);
          switch (e.Op) {
            case UnaryOpExpr.Opcode.Lit:
              return MaybeLit(arg);
            case UnaryOpExpr.Opcode.Not:
              if (expr.Type.IsBitVectorType) {
                var bvWidth = expr.Type.AsBitVectorType.Width;
                var bvType = translator.BplBvType(bvWidth);
                Bpl.Expr r = translator.FunctionCall(expr.tok, "not_bv" + bvWidth, bvType, arg);
                if (translator.IsLit(arg)) {
                  r = MaybeLit(r, bvType);
                }
                return r;
              } else {
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
              }
            case UnaryOpExpr.Opcode.Cardinality:
              var eType = e.E.Type.NormalizeExpand();
              if (eType is SeqType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.SeqLength, null, arg);
              } else if (eType is SetType && ((SetType)eType).Finite) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.SetCard, null, arg);
              } else if (eType is MultiSetType) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.MultiSetCard, null, arg);
              } else if (eType is MapType && ((MapType)eType).Finite) {
                return translator.FunctionCall(expr.tok, BuiltinFunction.MapCard, null, arg);
              } else {
                Contract.Assert(false); throw new cce.UnreachableException();  // unexpected sized type
              }
            case UnaryOpExpr.Opcode.Fresh:
              var eeType = e.E.Type.NormalizeExpand();
              if (eeType is SetType) {
                // generate:  (forall $o: ref :: { X[Box($o)] } X[Box($o)] ==> $o != null && !old($Heap)[$o,alloc])
                // OR, if X[Box($o)] is rewritten into smaller parts, use the less good trigger old($Heap)[$o,alloc]
                Bpl.Variable oVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$o", predef.RefType));
                Bpl.Expr o = new Bpl.IdentifierExpr(expr.tok, oVar);
                Bpl.Expr oNotNull = Bpl.Expr.Neq(o, predef.Null);
                bool performedInSetRewrite;
                Bpl.Expr oInSet = TrInSet(expr.tok, o, e.E, ((SetType)eeType).Arg, true, out performedInSetRewrite);
                Bpl.Expr oNotFresh = Old.IsAlloced(expr.tok, o);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(oNotFresh);
                Bpl.Expr body = Bpl.Expr.Imp(oInSet, Bpl.Expr.And(oNotNull, oIsFresh));
                var trigger = BplTrigger(performedInSetRewrite ? oNotFresh : oInSet);
                return new Bpl.ForallExpr(expr.tok, new List<Variable> { oVar }, trigger, body);
              } else if (eeType is SeqType) {
                // generate:  (forall $i: int :: 0 <= $i && $i < Seq#Length(X) ==> Unbox(Seq#Index(X,$i)) != null && !old($Heap)[Unbox(Seq#Index(X,$i)),alloc])
                Bpl.Variable iVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, "$i", Bpl.Type.Int));
                Bpl.Expr i = new Bpl.IdentifierExpr(expr.tok, iVar);
                Bpl.Expr iBounds = translator.InSeqRange(expr.tok, i, Type.Int, TrExpr(e.E), true, null, false);
                Bpl.Expr XsubI = translator.FunctionCall(expr.tok, BuiltinFunction.SeqIndex, predef.RefType, TrExpr(e.E), i);
                XsubI = translator.FunctionCall(expr.tok, BuiltinFunction.Unbox, predef.RefType, XsubI);
                Bpl.Expr oNotFresh = Old.IsAlloced(expr.tok, XsubI);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(oNotFresh);
                Bpl.Expr xsubiNotNull = Bpl.Expr.Neq(XsubI, predef.Null);
                Bpl.Expr body = Bpl.Expr.Imp(iBounds, Bpl.Expr.And(xsubiNotNull, oIsFresh));
                //TRIGGERS: Does this make sense? dafny0\SmallTests
                // BROKEN // NEW_TRIGGER
                //TRIG (forall $i: int :: 0 <= $i && $i < Seq#Length(Q#0) && $Unbox(Seq#Index(Q#0, $i)): ref != null ==> !read(old($Heap), $Unbox(Seq#Index(Q#0, $i)): ref, alloc))
                return new Bpl.ForallExpr(expr.tok, new List<Variable> { iVar }, body);
              } else {
                // generate:  x != null && !old($Heap)[x]
                Bpl.Expr oNull = Bpl.Expr.Neq(TrExpr(e.E), predef.Null);
                Bpl.Expr oIsFresh = Bpl.Expr.Not(Old.IsAlloced(expr.tok, TrExpr(e.E)));
                return Bpl.Expr.Binary(expr.tok, BinaryOperator.Opcode.And, oNull, oIsFresh);
              }
            case UnaryOpExpr.Opcode.Allocated: {
                var aType = e.E.Type.NormalizeExpand();
                return translator.MkIsAlloc(TrExpr(e.E), aType, HeapExpr);
              }
            default:
              Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
          }

        } else if (expr is ConversionExpr) {
          var e = (ConversionExpr)expr;
          return translator.ConvertExpression(e.tok, TrExpr(e.E), e.E.Type, e.ToType);

        } else if (expr is TypeTestExpr) {
          var e = (TypeTestExpr)expr;
          return translator.GetSubrangeCheck(TrExpr(e.E), e.E.Type, e.ToType, out var _) ?? Bpl.Expr.True;

        } else if (expr is BinaryExpr) {
          BinaryExpr e = (BinaryExpr)expr;
          bool isReal = e.E0.Type.IsNumericBased(Type.NumericPersuasion.Real);
          int bvWidth = e.E0.Type.IsBitVectorType ? e.E0.Type.AsBitVectorType.Width : -1;  // -1 indicates "not a bitvector type"
          Bpl.Expr e0 = TrExpr(e.E0);
          if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet) {
            bool pr;
            return TrInSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type), false, out pr);  // let TrInSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSet) {
            bool pr;
            Bpl.Expr arg = TrInSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type), false, out pr);  // let TrInSet translate e.E1
            return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InMultiSet) {
            return TrInMultiSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type), false); // let TrInMultiSet translate e.E1
          } else if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInMultiSet) {
            Bpl.Expr arg = TrInMultiSet(expr.tok, e0, e.E1, cce.NonNull(e.E0.Type), false);  // let TrInMultiSet translate e.E1
            return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, arg);
          }
          Bpl.Expr e1 = TrExpr(e.E1);
          BinaryOperator.Opcode bOpcode;
          Bpl.Type typ;
          var oe0 = e0;
          var oe1 = e1;
          var lit0 = translator.GetLit(e0);
          var lit1 = translator.GetLit(e1);
          bool liftLit = translator.IsLit(e0) && translator.IsLit(e1);
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
                return translator.CoEqualCall(cot, e0args, e1args, null, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, expr.tok);
              }
              if (e.E0.Type.IsIndDatatype) {
                return translator.TypeSpecificEqual(expr.tok, e.E0.Type, e0, e1);
              }
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Eq; break;
            case BinaryExpr.ResolvedOpcode.NeqCommon:
              var cotx = e.E0.Type.AsCoDatatype;
              if (cotx != null) {
                var e0args = e.E0.Type.NormalizeExpand().TypeArgs;
                var e1args = e.E1.Type.NormalizeExpand().TypeArgs;
                var eq = translator.CoEqualCall(cotx, e0args, e1args, null, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e0, e1, expr.tok);
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, eq);
              }
              if (e.E0.Type.IsIndDatatype) {
                var eq = translator.TypeSpecificEqual(expr.tok, e.E0.Type, e0, e1);
                return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, eq);
              }
              typ = Bpl.Type.Bool;
              bOpcode = BinaryOperator.Opcode.Neq; break;
            case BinaryExpr.ResolvedOpcode.Lt:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "lt_bv" + bvWidth, Bpl.Type.Bool, e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return translator.FunctionCall(expr.tok, "ORD#Less", Bpl.Type.Bool, e0, e1);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Bpl.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Lt;
                break;
              } else {
                return TrToFunctionCall(expr.tok, "INTERNAL_lt_boogie", Bpl.Type.Bool, e0, e1, liftLit);
              }
            case BinaryExpr.ResolvedOpcode.LessThanLimit:
              return translator.FunctionCall(expr.tok, "ORD#LessThanLimit", Bpl.Type.Bool, e0, e1);
            case BinaryExpr.ResolvedOpcode.Le:
              keepLits = true;
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "le_bv" + bvWidth, Bpl.Type.Bool, e0, e1, false);
              } else if (e.E0.Type.IsBigOrdinalType) {
                var less = translator.FunctionCall(expr.tok, "ORD#Less", Bpl.Type.Bool, e0, e1);
                var eq = Bpl.Expr.Eq(e0, e1);
                return BplOr(eq, less);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Bpl.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Le;
                break;
              } else {
                return TrToFunctionCall(expr.tok, "INTERNAL_le_boogie", Bpl.Type.Bool, e0, e1, false);
              }
            case BinaryExpr.ResolvedOpcode.Ge:
              keepLits = true;
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "ge_bv" + bvWidth, Bpl.Type.Bool, e0, e1, false);
              } else if (e.E0.Type.IsBigOrdinalType) {
                var less = translator.FunctionCall(expr.tok, "ORD#Less", Bpl.Type.Bool, e1, e0);
                var eq = Bpl.Expr.Eq(e1, e0);
                return BplOr(eq, less);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Bpl.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Ge;
                break;
              } else {
                return TrToFunctionCall(expr.tok, "INTERNAL_ge_boogie", Bpl.Type.Bool, e0, e1, false);
              }
            case BinaryExpr.ResolvedOpcode.Gt:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "gt_bv" + bvWidth, Bpl.Type.Bool, e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return translator.FunctionCall(expr.tok, "ORD#Less", Bpl.Type.Bool, e1, e0);
              } else if (isReal || !DafnyOptions.O.DisableNLarith) {
                typ = Bpl.Type.Bool;
                bOpcode = BinaryOperator.Opcode.Gt;
                break;
              } else {
                return TrToFunctionCall(expr.tok, "INTERNAL_gt_boogie", Bpl.Type.Bool, e0, e1, liftLit);
              }

            case BinaryExpr.ResolvedOpcode.Add:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "add_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return TrToFunctionCall(expr.tok, "ORD#Plus", predef.BigOrdinalType, e0, e1, liftLit);
              } else if (e.E0.Type.IsCharType) {
                return TrToFunctionCall(expr.tok, "char#Plus", predef.CharType, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(expr.tok, "INTERNAL_add_boogie", Bpl.Type.Int, e0, e1, liftLit);
              } else if (!isReal && (DafnyOptions.O.ArithMode == 2 || 5 <= DafnyOptions.O.ArithMode)) {
                return TrToFunctionCall(expr.tok, "Add", Bpl.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Add;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Sub:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "sub_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (e.E0.Type.IsBigOrdinalType) {
                return TrToFunctionCall(expr.tok, "ORD#Minus", predef.BigOrdinalType, e0, e1, liftLit);
              } else if (e.E0.Type.IsCharType) {
                return TrToFunctionCall(expr.tok, "char#Minus", predef.CharType, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(expr.tok, "INTERNAL_sub_boogie", Bpl.Type.Int, e0, e1, liftLit);
              } else if (!isReal && (DafnyOptions.O.ArithMode == 2 || 5 <= DafnyOptions.O.ArithMode)) {
                return TrToFunctionCall(expr.tok, "Sub", Bpl.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Sub;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Mul:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "mul_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith) {
                return TrToFunctionCall(expr.tok, "INTERNAL_mul_boogie", Bpl.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(expr.tok, "Mul", Bpl.Type.Int, oe0, oe1, liftLit);
              } else {
                typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Mul;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Div:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "div_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.DisableNLarith && !isReal) {
                return TrToFunctionCall(expr.tok, "INTERNAL_div_boogie", Bpl.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(expr.tok, "Div", Bpl.Type.Int, e0, oe1, liftLit);
              } else if (isReal) {
                typ = Bpl.Type.Real;
                bOpcode = BinaryOperator.Opcode.RealDiv;
                break;
              } else {
                typ = Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Div;
                break;
              }
            case BinaryExpr.ResolvedOpcode.Mod:
              if (0 <= bvWidth) {
                return TrToFunctionCall(expr.tok, "mod_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              } else if (DafnyOptions.O.DisableNLarith && !isReal) {
                return TrToFunctionCall(expr.tok, "INTERNAL_mod_boogie", Bpl.Type.Int, e0, e1, liftLit);
              } else if (!isReal && DafnyOptions.O.ArithMode != 0 && DafnyOptions.O.ArithMode != 3) {
                return TrToFunctionCall(expr.tok, "Mod", Bpl.Type.Int, e0, oe1, liftLit);
              } else {
                typ = isReal ? Bpl.Type.Real : Bpl.Type.Int;
                bOpcode = BinaryOperator.Opcode.Mod;
                break;
              }

            case BinaryExpr.ResolvedOpcode.LeftShift: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(expr.tok, "LeftShift_bv" + bvWidth, translator.BplBvType(bvWidth), e0, translator.ConvertExpression(expr.tok, e1, e.E1.Type, e.Type), liftLit);
              }
            case BinaryExpr.ResolvedOpcode.RightShift: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(expr.tok, "RightShift_bv" + bvWidth, translator.BplBvType(bvWidth), e0, translator.ConvertExpression(expr.tok, e1, e.E1.Type, e.Type), liftLit);
              }
            case BinaryExpr.ResolvedOpcode.BitwiseAnd: {
              Contract.Assert(0 <= bvWidth);
              return TrToFunctionCall(expr.tok, "and_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
            }
            case BinaryExpr.ResolvedOpcode.BitwiseOr: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(expr.tok, "or_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              }
            case BinaryExpr.ResolvedOpcode.BitwiseXor: {
                Contract.Assert(0 <= bvWidth);
                return TrToFunctionCall(expr.tok, "xor_bv" + bvWidth, translator.BplBvType(bvWidth), e0, e1, liftLit);
              }

            case BinaryExpr.ResolvedOpcode.LtChar:
            case BinaryExpr.ResolvedOpcode.LeChar:
            case BinaryExpr.ResolvedOpcode.GeChar:
            case BinaryExpr.ResolvedOpcode.GtChar: {
                // work off the original operands (that is, allow them to be lit-wrapped)
                var operand0 = translator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe0);
                var operand1 = translator.FunctionCall(e0.tok, BuiltinFunction.CharToInt, null, oe1);
                BinaryOperator.Opcode bOp;
                switch (e.ResolvedOp) {
                  case BinaryExpr.ResolvedOpcode.LtChar:  bOp = BinaryOperator.Opcode.Lt; break;
                  case BinaryExpr.ResolvedOpcode.LeChar: bOp = BinaryOperator.Opcode.Le; break;
                  case BinaryExpr.ResolvedOpcode.GeChar: bOp = BinaryOperator.Opcode.Ge; break;
                  case BinaryExpr.ResolvedOpcode.GtChar: bOp = BinaryOperator.Opcode.Gt; break;
                  default:
                    Contract.Assert(false);  // unexpected case
                    throw new cce.UnreachableException();  // to please compiler
                }
                return Bpl.Expr.Binary(expr.tok, bOp, operand0, operand1);
              }

            case BinaryExpr.ResolvedOpcode.SetEq:
            case BinaryExpr.ResolvedOpcode.MultiSetEq:
            case BinaryExpr.ResolvedOpcode.SeqEq:
            case BinaryExpr.ResolvedOpcode.MapEq:
              return translator.TypeSpecificEqual(expr.tok, e.E0.Type, e0, e1);
            case BinaryExpr.ResolvedOpcode.SetNeq:
            case BinaryExpr.ResolvedOpcode.MultiSetNeq:
            case BinaryExpr.ResolvedOpcode.SeqNeq:
            case BinaryExpr.ResolvedOpcode.MapNeq:
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, translator.TypeSpecificEqual(expr.tok, e.E0.Type, e0, e1));

            case BinaryExpr.ResolvedOpcode.ProperSubset: {
              return translator.ProperSubset(expr.tok, e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.Subset: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
              return translator.FunctionCall(expr.tok, f, null, e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.Superset: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetSubset : BuiltinFunction.ISetSubset;
              return translator.FunctionCall(expr.tok, f, null, e1, e0);
            }
            case BinaryExpr.ResolvedOpcode.ProperSuperset:
              return translator.ProperSubset(expr.tok, e1, e0);
            case BinaryExpr.ResolvedOpcode.Disjoint: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetDisjoint : BuiltinFunction.ISetDisjoint;
              return translator.FunctionCall(expr.tok, f, null, e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.InSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.NotInSet:
              Contract.Assert(false); throw new cce.UnreachableException();  // this case handled above
            case BinaryExpr.ResolvedOpcode.Union: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetUnion : BuiltinFunction.ISetUnion;
              return translator.FunctionCall(expr.tok, f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.Intersection: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetIntersection : BuiltinFunction.ISetIntersection;
              return translator.FunctionCall(expr.tok, f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.SetDifference: {
              bool finite = e.E1.Type.AsSetType.Finite;
              var f = finite ? BuiltinFunction.SetDifference : BuiltinFunction.ISetDifference;
              return translator.FunctionCall(expr.tok, f, translator.TrType(expr.Type.AsSetType.Arg), e0, e1);
            }
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
            case BinaryExpr.ResolvedOpcode.InMap: {
              bool finite = e.E1.Type.AsMapType.Finite;
              var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
              return Bpl.Expr.SelectTok(expr.tok, translator.FunctionCall(expr.tok, f, predef.MapType(e.tok, finite, predef.BoxType, predef.BoxType), e1),
                                     BoxIfNecessary(expr.tok, e0, e.E0.Type));
            }
            case BinaryExpr.ResolvedOpcode.NotInMap: {
              bool finite = e.E1.Type.AsMapType.Finite;
              var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
              Bpl.Expr inMap = Bpl.Expr.SelectTok(expr.tok, translator.FunctionCall(expr.tok, f, predef.MapType(e.tok, finite, predef.BoxType, predef.BoxType), e1),
                                     BoxIfNecessary(expr.tok, e0, e.E0.Type));
              return Bpl.Expr.Unary(expr.tok, UnaryOperator.Opcode.Not, inMap);
            }
            case BinaryExpr.ResolvedOpcode.MapMerge: {
              bool finite = e.E0.Type.AsMapType.Finite;
              var f = finite ? "Map#Merge" : "IMap#Merge";
              return translator.FunctionCall(expr.tok, f, translator.TrType(expr.Type), e0, e1);
            }
            case BinaryExpr.ResolvedOpcode.MapSubtraction: {
              bool finite = e.E0.Type.AsMapType.Finite;
              var f = finite ? "Map#Subtract" : "IMap#Subtract";
              return translator.FunctionCall(expr.tok, f, translator.TrType(expr.Type), e0, e1);
            }

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
            re = MaybeLit(re, typ);
          }
          return re;
        } else if (expr is TernaryExpr) {
          var e = (TernaryExpr)expr;
          var e0 = TrExpr(e.E0);
          if (!TernaryExpr.PrefixEqUsesNat && !e.E0.Type.IsBigOrdinalType) {
            e0 = translator.FunctionCall(e0.tok, "ORD#FromNat", predef.BigOrdinalType, e0);
          }
          var e1 = TrExpr(e.E1);
          var e2 = TrExpr(e.E2);
          switch (e.Op) {
            case TernaryExpr.Opcode.PrefixEqOp:
            case TernaryExpr.Opcode.PrefixNeqOp:
              var e1type = e.E1.Type.NormalizeExpand();
              var e2type = e.E2.Type.NormalizeExpand();
              var cot = e1type.AsCoDatatype;
              Contract.Assert(cot != null);  // the argument types of prefix equality (and prefix disequality) are codatatypes
              var r = translator.CoEqualCall(cot, e1type.TypeArgs, e2type.TypeArgs, e0, this.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), e1, e2);
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
          if (!e.Exact) {
            var d = translator.LetDesugaring(e);
            return TrExpr(d);
          } else {
            List<Bpl.Variable> lhss;
            List<Bpl.Expr> rhss;
            TrLetExprPieces(e, out lhss, out rhss);
            // in the translation of body, treat a let-bound variable as IsLit if its RHS definition is IsLit
            Contract.Assert(lhss.Count == rhss.Count);  // this is a postcondition of TrLetExprPieces
            var previousCount = translator.letBoundVariablesWithLitRHS.Count;
            for (var i = 0; i < lhss.Count; i++) {
              if (translator.IsLit(rhss[i])) {
                translator.letBoundVariablesWithLitRHS.Add(lhss[i].Name);
              }
              i++;
            }
            var body = TrExpr(e.Body);
            foreach (var v in lhss) {
              translator.letBoundVariablesWithLitRHS.Remove(v.Name);
            }
            Contract.Assert(previousCount == translator.letBoundVariablesWithLitRHS.Count);
            // in the following, use the token for Body instead of the token for the whole let expression; this gives better error locations
            return new Bpl.LetExpr(e.Body.tok, lhss, rhss, null, body);
          }
        } else if (expr is QuantifierExpr) {
          QuantifierExpr e = (QuantifierExpr)expr;

          if (e.SplitQuantifier != null) {
            return TrExpr(e.SplitQuantifierExpression);
          } else {
            List<Variable> tyvars = translator.MkTyParamBinders(e.TypeArgs);
            List<Variable> bvars = new List<Variable>();
            var bodyEtran = this;
            if (e is ExistsExpr && translator.stmtContext == StmtType.ASSERT && translator.adjustFuelForExists) {
              // assert exists need decrease fuel by 1
              bodyEtran = bodyEtran.DecreaseFuel(1);
              // set adjustFuelForExists to false so that we don't keep decrease the fuel in cases like the expr below.
              // assert exists p:int :: exists t:T :: ToInt(t) > 0;
              translator.adjustFuelForExists = false;
            } else if (e is ExistsExpr && translator.stmtContext == StmtType.ASSUME && translator.adjustFuelForExists) {
              // assume exists need increase fuel by 1
              bodyEtran = bodyEtran.LayerOffset(1);
              translator.adjustFuelForExists = false;
            }

            var initEtran = this;
            bool _scratch = true;

            Bpl.Expr antecedent = Bpl.Expr.True;

            if (Attributes.ContainsBool(e.Attributes, "layerQuantifier", ref _scratch)) {
              // If this is a layer quantifier, quantify over layers here, and use $LS(ly) layers in the translation of the body
              var ly = BplBoundVar(e.Refresh("q$ly#", translator.CurrentIdGenerator), predef.LayerType, bvars);
              bodyEtran = bodyEtran.ReplaceLayer(ly);
            }
            if (Attributes.ContainsBool(e.Attributes, "heapQuantifier", ref _scratch)) {
              var h = BplBoundVar(e.Refresh("q$heap#", translator.CurrentIdGenerator), predef.HeapType, bvars);
              bodyEtran = new ExpressionTranslator(bodyEtran, h);
              antecedent = BplAnd(new List<Bpl.Expr> {
                antecedent,
                translator.FunctionCall(e.tok, BuiltinFunction.IsGoodHeap, null, h),
                translator.HeapSameOrSucc(initEtran.HeapExpr, h)  // initHeapForAllStmt
              });
            }

            List<bool> freeOfAlloc = null;
            if (FrugalHeapUseX) {
              freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
            }
            antecedent = BplAnd(antecedent, bodyEtran.TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc)); // initHeapForAllStmt

            Bpl.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
            Bpl.Trigger tr = translator.TrTrigger(bodyEtran, e.Attributes, e.tok, bvars, null, null);

            if (e.Range != null) {
              antecedent = BplAnd(antecedent, bodyEtran.TrExpr(e.Range));
            }
            Bpl.Expr body = bodyEtran.TrExpr(e.Term);

            if (e is ForallExpr) {
              return new Bpl.ForallExpr(expr.tok, new List<TypeVariable>(), Concat(tyvars, bvars), kv, tr, Bpl.Expr.Imp(antecedent, body));
            } else {
              Contract.Assert(e is ExistsExpr);
              return new Bpl.ExistsExpr(expr.tok, new List<TypeVariable>(), Concat(tyvars, bvars), kv, tr, Bpl.Expr.And(antecedent, body));
            }
          }
        } else if (expr is SetComprehension) {
          var e = (SetComprehension)expr;
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          // Translate "set xs | R :: T" into:
          //     lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))
          // or if "T" is "xs", then:
          //     lambda y: BoxType :: CorrectType(y) && R[xs := Unbox(y)]
          var yVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, translator.CurrentIdGenerator.FreshId("$y#"), predef.BoxType));
          Bpl.Expr y = new Bpl.IdentifierExpr(expr.tok, yVar);
          Bpl.Expr lbody;
          if (e.TermIsSimple) {
            // lambda y: BoxType :: CorrectType(y) && R[xs := yUnboxed]
            var bv = e.BoundVars[0];
            Bpl.Expr typeAntecedent = translator.MkIsBox(new Bpl.IdentifierExpr(expr.tok, yVar), bv.Type);
            if (freeOfAlloc != null && !freeOfAlloc[0]) {
              var isAlloc = translator.MkIsAlloc(new Bpl.IdentifierExpr(expr.tok, yVar), bv.Type, HeapExpr);
              typeAntecedent = BplAnd(typeAntecedent, isAlloc);
            }
            var yUnboxed = translator.UnboxIfBoxed(new Bpl.IdentifierExpr(expr.tok, yVar), bv.Type);
            var range = Translator.Substitute(e.Range, bv, new BoogieWrapper(yUnboxed, bv.Type));
            lbody = BplAnd(typeAntecedent, TrExpr(range));
          } else {
            // lambda y: BoxType :: (exists xs :: CorrectType(xs) && R && y==Box(T))
            List<Variable> bvars = new List<Variable>();
            Bpl.Expr typeAntecedent = TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);

            var eq = Bpl.Expr.Eq(y, BoxIfNecessary(expr.tok, TrExpr(e.Term), e.Term.Type));
            var ebody = Bpl.Expr.And(BplAnd(typeAntecedent, TrExpr(e.Range)), eq);
            var triggers = translator.TrTrigger(this, e.Attributes, e.tok);
            lbody = new Bpl.ExistsExpr(expr.tok, bvars, triggers, ebody);
          }
          Bpl.QKeyValue kv = TrAttributes(e.Attributes, "trigger");
          return new Bpl.LambdaExpr(expr.tok, new List<TypeVariable>(), new List<Variable> { yVar }, kv, lbody);

        } else if (expr is MapComprehension) {
          var e = (MapComprehension)expr;
          // Translate "map x,y | R(x,y) :: F(x,y) := G(x,y)" into
          // Map#Glue(lambda w: BoxType :: exists x,y :: R(x,y) && unbox(w) == F(x,y),
          //          lambda w: BoxType :: G(project_x(unbox(w)), project_y(unbox(w))),
          //          type)".
          // where project_x and project_y are functions defined (elsewhere, in CanCallAssumption) by the following axiom:
          //     forall x,y :: R(x,y) ==> var x',y' := project_x(unbox(F(x,y))),project_y(unbox(F(x,y))); R(x',y') && F(x',y') == F(x,y)
          // that is (without the let expression):
          //     forall x,y :: R(x,y) ==> R(project_x(unbox(F(x,y))), project_y(unbox(F(x,y)))) && F(project_x(unbox(F(x,y))), project_y(unbox(F(x,y)))) == F(x,y)
          //
          // In the common case where F(x,y) is omitted (in which case the list of bound variables is restricted to length 1):
          // Translate "map x | R(x) :: G(x)" into
          // Map#Glue(lambda w: BoxType :: R(unbox(w)),
          //          lambda w: BoxType :: G(unbox(w)),
          //          type)".
          List<Variable> bvars = new List<Variable>();
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);

          Bpl.QKeyValue kv = TrAttributes(e.Attributes, "trigger");

          var wVar = new Bpl.BoundVariable(expr.tok, new Bpl.TypedIdent(expr.tok, translator.CurrentIdGenerator.FreshId("$w#"), predef.BoxType));

          Bpl.Expr keys, values;
          if (!e.IsGeneralMapComprehension) {
            var bv = e.BoundVars[0];
            var w = new Bpl.IdentifierExpr(expr.tok, wVar);
            Bpl.Expr unboxw = translator.UnboxIfBoxed(w, bv.Type);
            Bpl.Expr typeAntecedent = translator.MkIsBox(w, bv.Type);
            var subst = new Dictionary<IVariable,Expression>();
            subst.Add(bv, new BoogieWrapper(unboxw, bv.Type));

            var ebody = BplAnd(typeAntecedent, TrExpr(Translator.Substitute(e.Range, null, subst)));
            keys = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { wVar }, kv, ebody);
            ebody = TrExpr(Translator.Substitute(e.Term, null, subst));
            values = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { wVar }, kv, BoxIfNecessary(expr.tok, ebody, e.Term.Type));
          } else {
            var t = e.TermLeft;
            var w = new Bpl.IdentifierExpr(expr.tok, wVar);
            Bpl.Expr unboxw = translator.UnboxIfBoxed(w, t.Type);
            Bpl.Expr typeAntecedent = translator.MkIsBox(w, t.Type);
            List<Bpl.Variable> bvs;
            List<Bpl.Expr> args;
            translator.CreateBoundVariables(e.BoundVars, out bvs, out args);
            Contract.Assert(e.BoundVars.Count == bvs.Count);
            var subst = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < e.BoundVars.Count; i++) {
              subst.Add(e.BoundVars[i], new BoogieWrapper(args[i], e.BoundVars[i].Type));
            }
            var rr = TrExpr(Translator.Substitute(e.Range, null, subst));
            var ff = TrExpr(Translator.Substitute(t, null, subst));
            var exst_body = BplAnd(rr, Bpl.Expr.Eq(unboxw, ff));
            var ebody = BplAnd(typeAntecedent, new Bpl.ExistsExpr(e.tok, bvs, exst_body));
            keys = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { wVar }, kv, ebody);

            translator.CreateMapComprehensionProjectionFunctions(e);
            Contract.Assert(e.ProjectionFunctions != null && e.ProjectionFunctions.Count == e.BoundVars.Count);
            subst = new Dictionary<IVariable, Expression>();
            for (var i = 0; i < e.BoundVars.Count; i++) {
              var p = new Bpl.NAryExpr(e.tok, new Bpl.FunctionCall(e.ProjectionFunctions[i]), new List<Bpl.Expr> { unboxw });
              var prj = new BoogieWrapper(p, e.BoundVars[i].Type);
              subst.Add(e.BoundVars[i], prj);
            }
            ebody = TrExpr(Translator.Substitute(e.Term, null, subst));
            values = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), new List<Variable> { wVar }, kv, BoxIfNecessary(expr.tok, ebody, e.Term.Type));
          }

          bool finite = e.Finite;
          var f = finite ? BuiltinFunction.MapGlue : BuiltinFunction.IMapGlue;
          return translator.FunctionCall(e.tok, f, null, keys, values, translator.TypeToTy(expr.Type));

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

      public Expr TrExprSpecialFunctionCall(FunctionCallExpr expr) {
        Contract.Requires(expr.Function is SpecialFunction);
        string name = expr.Function.Name;
        if (name == "RotateLeft") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(expr.tok, "LeftRotate_bv" + w, translator.BplBvType(w), TrExpr(expr.Receiver), translator.ConvertExpression(expr.tok, TrExpr(arg), arg.Type, expr.Type), false);
        } else if (name == "RotateRight") {
          var w = expr.Type.AsBitVectorType.Width;
          Expression arg = expr.Args[0];
          return TrToFunctionCall(expr.tok, "RightRotate_bv" + w, translator.BplBvType(w), TrExpr(expr.Receiver), translator.ConvertExpression(expr.tok, TrExpr(arg), arg.Type, expr.Type), false);
        } else {
          bool argsAreLit_dummy;
          var args = FunctionInvocationArguments(expr, null, true, out argsAreLit_dummy);
          var id = new Bpl.IdentifierExpr(expr.tok, expr.Function.FullSanitizedName, translator.TrType(expr.Type));
          return new Bpl.NAryExpr(expr.tok, new Bpl.FunctionCall(id), args);
        }
      }
      public Expr TrToFunctionCall(IToken tok, string function, Bpl.Type returnType, Bpl.Expr e0, Bpl.Expr e1, bool liftLit) {
        Bpl.Expr re = translator.FunctionCall(tok, function, returnType, e0, e1);
        if (liftLit) {
          re = MaybeLit(re, returnType);
        }
        return re;
      }

      private Expr TrLambdaExpr(LambdaExpr e) {
        Contract.Requires(e != null);

        var bvars = new List<Bpl.Variable>();

        var varNameGen = translator.CurrentIdGenerator.NestedFreshIdGenerator("$l#");

        var heap = BplBoundVar(varNameGen.FreshId("#heap#"), predef.HeapType, bvars);

        var ves = (from bv in e.BoundVars select
          BplBoundVar(varNameGen.FreshId(string.Format("#{0}#", bv.Name)), predef.BoxType, bvars)).ToList();
        var subst = e.BoundVars.Zip(ves, (bv, ve) => {
          var unboxy = translator.UnboxIfBoxed(ve, bv.Type);
          return new KeyValuePair<IVariable, Expression>(bv, new BoogieWrapper(unboxy, bv.Type));
        }).ToDictionary(x => x.Key, x => x.Value);
        var su = new Substituter(null, subst, new Dictionary<TypeParameter, Type>());

        var et = new ExpressionTranslator(this, heap);
        var lvars = new List<Bpl.Variable>();
        var ly = BplBoundVar(varNameGen.FreshId("#ly#"), predef.LayerType, lvars);
        et = et.WithLayer(ly);

        var ebody = et.TrExpr(Translator.Substitute(e.Body, null, subst));
        ebody = translator.BoxIfUnboxed(ebody, e.Body.Type);

        var isBoxes = BplAnd(ves.Zip(e.BoundVars, (ve, bv) => translator.MkIsBox(ve, bv.Type)));
        var reqbody = e.Range == null
          ? isBoxes
          : BplAnd(isBoxes, et.TrExpr(Translator.Substitute(e.Range, null, subst)));

        var rdvars = new List<Bpl.Variable>();
        var o = BplBoundVar(varNameGen.FreshId("#o#"), predef.RefType, rdvars);
        Bpl.Expr rdbody = new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), rdvars, null,
          translator.InRWClause(e.tok, o, null, e.Reads.ConvertAll(su.SubstFrameExpr), et, null, null));
        rdbody = translator.FunctionCall(e.tok, "SetRef_to_SetBox", predef.SetType(e.tok, true, predef.BoxType), rdbody);

        return MaybeLit(
          translator.FunctionCall(e.tok, BuiltinFunction.AtLayer, predef.HandleType,
            new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), lvars, null,
              translator.FunctionCall(e.tok, translator.Handle(e.BoundVars.Count), predef.BoxType,
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, ebody),
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, reqbody),
                new Bpl.LambdaExpr(e.tok, new List<TypeVariable>(), bvars, null, rdbody))),
                layerIntraCluster != null ? layerIntraCluster.ToExpr() : layerInterCluster.ToExpr()),
          predef.HandleType);
      }

      public void TrLetExprPieces(LetExpr let, out List<Bpl.Variable> lhss, out List<Bpl.Expr> rhss) {
        Contract.Requires(let != null);
        var substMap = new Dictionary<IVariable, Expression>();
        for (int i = 0; i < let.LHSs.Count; i++) {
          translator.AddCasePatternVarSubstitutions(let.LHSs[i], TrExpr(let.RHSs[i]), substMap);
        }
        lhss = new List<Bpl.Variable>();
        rhss = new List<Bpl.Expr>();
        foreach (var v in let.BoundVars) {
          var rhs = substMap[v];  // this should succeed (that is, "v" is in "substMap"), because the AddCasePatternVarSubstitutions calls above should have added a mapping for each bound variable in let.BoundVars
          Bpl.Expr bvIde;  // unused
          var bv = BplBoundVar(v.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(v.Type), out bvIde);
          lhss.Add(bv);
          rhss.Add(TrExpr(rhs));
        }
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
              var dv = new MemberSelectExpr(bv.tok, e.Source, dtor);
              substMap.Add(bv, dv);
            }
            argIndex++;
          }
          var c = Translator.Substitute(mc.Body, null, substMap);
          if (r == null) {
            r = c;
          } else {
            var test = new MemberSelectExpr(mc.tok, e.Source, mc.Ctor.QueryField);
            var ite = new ITEExpr(mc.tok, false, test, c, r);
            ite.Type = e.Type;
            r = ite;
          }
        }
        return r ?? new BoogieWrapper(ArbitraryValue(e.Type), e.Type);
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars) {
        return TrBoundVariables(boundVars, bvars, false);
      }

      public Bpl.Expr TrBoundVariables(List<BoundVar/*!*/> boundVars, List<Variable> bvars, bool translateAsLocals, List<bool>/*?*/ freeOfAlloc = null) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);
        Contract.Requires(freeOfAlloc == null || freeOfAlloc.Count == boundVars.Count);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        var i = 0;
        foreach (BoundVar bv in boundVars) {
          var tid = new Bpl.TypedIdent(bv.tok, bv.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(bv.Type));
          Bpl.Variable bvar;
          if (translateAsLocals) {
            bvar = new Bpl.LocalVariable(bv.tok, tid);
          } else {
            bvar = new Bpl.BoundVariable(bv.tok, tid);
          }
          bvars.Add(bvar);
          var useAlloc = freeOfAlloc == null || freeOfAlloc[i] ? NOALLOC : ISALLOC;
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, bvar), bv.Type, this, useAlloc);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
          i++;
        }
        return typeAntecedent;
      }

      public List<Tuple<Bpl.Variable, Bpl.Expr>> TrBoundVariables_SeparateWhereClauses(List<BoundVar/*!*/> boundVars) {
        Contract.Requires(boundVars != null);
        Contract.Ensures(Contract.Result<List<Tuple<Bpl.Variable, Bpl.Expr>>>() != null);

        var varsAndAntecedents = new List<Tuple<Bpl.Variable, Bpl.Expr>>();
        foreach (BoundVar bv in boundVars) {
          var tid = new Bpl.TypedIdent(bv.tok, bv.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(bv.Type));
          var bvar = new Bpl.BoundVariable(bv.tok, tid);
          var wh = translator.GetWhereClause(bv.tok, new Bpl.IdentifierExpr(bv.tok, bvar), bv.Type, this, NOALLOC);
          varsAndAntecedents.Add(Tuple.Create<Bpl.Variable, Bpl.Expr>(bvar, wh));
        }
        return varsAndAntecedents;
      }

      public Bpl.Expr TrBoundVariablesRename(List<BoundVar> boundVars, List<Variable> bvars, out Dictionary<IVariable, Expression> substMap, out Bpl.Trigger antitriggers) {
        Contract.Requires(boundVars != null);
        Contract.Requires(bvars != null);

        substMap = new Dictionary<IVariable, Expression>();
        antitriggers = null;
        Bpl.Expr typeAntecedent = Bpl.Expr.True;
        foreach (BoundVar bv in boundVars) {
          var newBoundVar = new BoundVar(bv.tok, bv.Name, bv.Type);
          IdentifierExpr ie = new IdentifierExpr(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration.IdGenerator));
          ie.Var = newBoundVar; ie.Type = ie.Var.Type;  // resolve ie here
          substMap.Add(bv, ie);
          Bpl.Variable bvar = new Bpl.BoundVariable(newBoundVar.tok, new Bpl.TypedIdent(newBoundVar.tok, newBoundVar.AssignUniqueName(translator.currentDeclaration.IdGenerator), translator.TrType(newBoundVar.Type)));
          bvars.Add(bvar);
          var bIe = new Bpl.IdentifierExpr(bvar.tok, bvar);
          Bpl.Expr wh = translator.GetWhereClause(bv.tok, bIe, newBoundVar.Type, this, NOALLOC);
          if (wh != null) {
            typeAntecedent = BplAnd(typeAntecedent, wh);
          }
        }
        return typeAntecedent;
      }

      public List<Bpl.Expr> FunctionInvocationArguments(FunctionCallExpr e, Bpl.Expr layerArgument) {
        bool dummy;
        return FunctionInvocationArguments(e, layerArgument, false, out dummy);
      }

      public List<Bpl.Expr> FunctionInvocationArguments(FunctionCallExpr e, Bpl.Expr layerArgument, bool omitHeapArgument, out bool argsAreLit) {
        Contract.Requires(e != null);
        Contract.Ensures(Contract.Result<List<Bpl.Expr>>() != null);

        var args = new List<Bpl.Expr>();

        // first add type arguments
        var tyParams = GetTypeParams(e.Function);
        var tySubst = e.TypeArgumentSubstitutionsWithParents();
        args.AddRange(translator.trTypeArgs(tySubst, tyParams));

        if (layerArgument != null) {
          args.Add(layerArgument);
        }
        if (e.Function is TwoStateFunction) {
          args.Add(OldAt(e.AtLabel).HeapExpr);
        }
        if (!omitHeapArgument && (AlwaysUseHeap || e.Function.ReadsHeap)) {
          Contract.Assert(HeapExpr != null);
          args.Add(HeapExpr);
          // if the function doesn't use heaps, but always use heap as an argument
          // we want to quantify over the heap so that heap in the trigger can match over
          // heap modifying operations. (see Dafny4/bug144.dfy)
          bool useHeap = e.Function.ReadsHeap;
          if (!useHeap) {
            foreach (var arg in e.Function.Formals) {
              if (arg.Type.IsRefType) {
                useHeap = true;
                break;
              }
            }
          }
          if (!useHeap) {
            Statistics_HeapAsQuantifierCount++;
          }
        }
        argsAreLit = true;
        if (!e.Function.IsStatic) {
          var tr_ee = TrExpr(e.Receiver);
          argsAreLit = argsAreLit && translator.IsLit(tr_ee);
          args.Add(tr_ee);
        }
        for (int i = 0; i < e.Args.Count; i++) {
          Expression ee = e.Args[i];
          Type t = e.Function.Formals[i].Type;
          Expr tr_ee = TrExpr(ee);
          argsAreLit = argsAreLit && translator.IsLit(tr_ee);
          args.Add(translator.CondApplyBox(e.tok, tr_ee, cce.NonNull(ee.Type), t));
        }
        return args;
      }

      public Bpl.Expr GetArrayIndexFieldName(IToken tok, List<Expression> indices) {
        return translator.GetArrayIndexFieldName(tok, indices.ConvertAll(idx => {
          var e = TrExpr(idx);
          return translator.ConvertExpression(idx.tok, e, idx.Type, Type.Int);
        }));
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
      public Bpl.Expr TrInSet(IToken tok, Bpl.Expr elmt, Expression s, Type elmtType, bool aggressive, out bool performedRewrite) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        var r = TrInSet_Aux(tok, elmt, elmtBox, s, aggressive, out performedRewrite);
        Contract.Assert(performedRewrite == RewriteInExpr(s, aggressive)); // sanity check
        return r;
      }
      /// <summary>
      /// The worker routine for TrInSet.  This method takes both "elmt" and "elmtBox" as parameters,
      /// using the former when the unboxed form is needed and the latter when the boxed form is needed.
      /// This gives the caller the flexibility to pass in either "o, Box(o)" or "Unbox(bx), bx".
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Bpl.Expr TrInSet_Aux(IToken tok, Bpl.Expr elmt, Bpl.Expr elmtBox, Expression s, bool aggressive, out bool performedRewrite) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(elmtBox != null);
        Contract.Requires(s != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        performedRewrite = true;  // assume a rewrite will happen
        s = s.Resolved;
        bool pr;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Union:
              return Bpl.Expr.Or(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.Intersection:
              return Bpl.Expr.And(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr));
            case BinaryExpr.ResolvedOpcode.SetDifference:
              return Bpl.Expr.And(TrInSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive, out pr), Bpl.Expr.Not(TrInSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive, out pr)));
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
        } else if (s is SetComprehension) {
          var compr = (SetComprehension)s;
          // Translate "elmt in set xs | R :: T" into:
          //     exists xs :: CorrectType(xs) && R && elmt==T
          // or if "T" is "xs", then:
          //     CorrectType(elmt) && R[xs := elmt]
          if (compr.TermIsSimple) {
            // CorrectType(elmt) && R[xs := elmt]
            // Note, we can always use NOALLOC here.
            Bpl.Expr typeAntecedent = translator.GetWhereClause(compr.tok, elmt, compr.BoundVars[0].Type, this, NOALLOC) ?? Bpl.Expr.True;
            var range = Translator.Substitute(compr.Range, compr.BoundVars[0], new BoogieWrapper(elmt, compr.BoundVars[0].Type));
            return BplAnd(typeAntecedent, TrExpr(range));
          } else {
            // exists xs :: CorrectType(xs) && R && elmt==T
            List<bool> freeOfAlloc = null;
            if (FrugalHeapUseX) {
              freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(compr.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
            }
            var bvars = new List<Variable>();
            Bpl.Expr typeAntecedent = TrBoundVariables(compr.BoundVars, bvars, false, freeOfAlloc) ?? Bpl.Expr.True;
            var eq = Bpl.Expr.Eq(elmtBox, BoxIfNecessary(compr.tok, TrExpr(compr.Term), compr.Term.Type));
            var ebody = Bpl.Expr.And(BplAnd(typeAntecedent, TrExpr(compr.Range)), eq);
            var triggers = translator.TrTrigger(this, compr.Attributes, compr.tok);
            return new Bpl.ExistsExpr(compr.tok, bvars, triggers, ebody);
          }
        }
        performedRewrite = false;
        return Bpl.Expr.SelectTok(tok, TrExpr(s), elmtBox);
      }

      /// <summary>
      /// Translate like 0 < s[Box(elmt)], but try to avoid as many set functions as possible in the
      /// translation, because such functions can mess up triggering.
      /// Note: This method must be kept in synch with RewriteInExpr.
      /// </summary>
      public Bpl.Expr TrInMultiSet(IToken tok, Bpl.Expr elmt, Expression s, Type elmtType, bool aggressive) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtType != null);

        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
        var elmtBox = BoxIfNecessary(tok, elmt, elmtType);
        return TrInMultiSet_Aux(tok, elmt, elmtBox, s, aggressive);
      }
      public Bpl.Expr TrInMultiSet_Aux(IToken tok, Bpl.Expr elmt, Bpl.Expr elmtBox, Expression s, bool aggressive) {
        Contract.Requires(tok != null);
        Contract.Requires(elmt != null);
        Contract.Requires(s != null);
        Contract.Requires(elmtBox != null);

        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        s = s.Resolved;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
              return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Or, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return Bpl.Expr.Binary(tok, BinaryOperator.Opcode.And, TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E0, aggressive), TrInMultiSet_Aux(tok, elmt, elmtBox, bin.E1, aggressive));
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
        return Bpl.Expr.Gt(Bpl.Expr.SelectTok(tok, TrExpr(s), elmtBox), Bpl.Expr.Literal(0));
      }

      /// <summary>
      /// This method returns "true" iff TrInSet_Aux/TrInMultiSet_Aux will rewrite an expression "x in s".
      /// Note: This method must be kept in synch with TrInSet_Aux/TrInMultiSet_Aux.
      /// </summary>
      public static bool RewriteInExpr(Expression s, bool aggressive) {
        Contract.Requires(s != null);

        s = s.Resolved;
        if (s is BinaryExpr && aggressive) {
          BinaryExpr bin = (BinaryExpr)s;
          switch (bin.ResolvedOp) {
            case BinaryExpr.ResolvedOpcode.Union:
            case BinaryExpr.ResolvedOpcode.Intersection:
            case BinaryExpr.ResolvedOpcode.SetDifference:
            case BinaryExpr.ResolvedOpcode.MultiSetUnion:
            case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
              return true;
            default:
              break;
          }
        } else if (s is SetDisplayExpr || s is MultiSetDisplayExpr) {
          return true;
        } else if (s is SetComprehension) {
          return true;
        }
        return false;
      }

      public Bpl.QKeyValue TrAttributes(Attributes attrs, string skipThisAttribute) {
        Bpl.QKeyValue kv = null;
        bool hasNewTimeLimit = Attributes.Contains(attrs, "_timeLimit");
        bool hasNewRLimit = Attributes.Contains(attrs, "_rlimit");
        foreach (var attr in attrs.AsEnumerable()) {
          if (attr.Name == skipThisAttribute
           || attr.Name == "axiom"  // Dafny's axiom attribute clashes with Boogie's axiom keyword
           || attr.Name == "fuel"   // Fuel often uses function names as arguments, which adds extra axioms unnecessarily
           || (DafnyOptions.O.DisallowExterns && (attr.Name == "extern" || attr.Name == "dllimport")) // omit the extern attribute when /noExterns option is specified.
           || attr.Name == "timeLimitMultiplier"  // This is a Dafny-specific attribute
           || (attr.Name == "timeLimit" && hasNewTimeLimit)
           || (attr.Name == "rlimit" && hasNewRLimit)
             ) {
            continue;
          }
          List<object> parms = new List<object>();
          foreach (var arg in attr.Args) {
            var s = arg.AsStringLiteral();
            if (s != null) {
              // pass string literals down to Boogie as string literals, not as their expression translation
              parms.Add(s);
            } else {
              var e = TrExpr(arg);
              e = translator.RemoveLit(e);
              parms.Add(e);
            }
          }

          var name = attr.Name;
          if (name == "_timeLimit") {
            name = "timeLimit";
          } else if (name == "_rlimit") {
            name = "rlimit";
          }
          kv = new Bpl.QKeyValue(Token.NoToken, name, parms, kv);
        }
        return kv;
      }

      // --------------- help routines ---------------

      public Bpl.Expr IsAlloced(IToken tok, Bpl.Expr e) {
        Contract.Requires(HeapExpr != null);
        return translator.IsAlloced(tok, HeapExpr, e);
      }

      public Bpl.Expr GoodRef(IToken tok, Bpl.Expr e, Type type) {
        Contract.Requires(tok != null);
        Contract.Requires(e != null);
        Contract.Requires(type != null);
        Contract.Ensures(Contract.Result<Bpl.Expr>() != null);

        // Add $Is and $IsAlloc
        return translator.GetWhereClause(tok, e, type, this, ISALLOC);
      }
    }

    enum BuiltinFunction
    {
      Lit,
      LitInt,
      LitReal,
      LayerSucc,
      AsFuelBottom,
      CharFromInt,
      CharToInt,

      Is, IsBox,
      IsAlloc, IsAllocBox,

      IsTraitParent,

      SetCard,
      SetEmpty,
      SetUnionOne,
      SetUnion,
      SetIntersection,
      SetDifference,
      SetEqual,
      SetSubset,
      SetDisjoint,

      ISetEmpty,
      ISetUnionOne,
      ISetUnion,
      ISetIntersection,
      ISetDifference,
      ISetEqual,
      ISetSubset,
      ISetDisjoint,

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

      IMapEmpty,
      IMapDomain,
      IMapElements,
      IMapEqual,
      IMapGlue,

      IndexField,
      MultiIndexField,

      Box,
      Unbox,

      RealToInt,
      IntToReal,

      IsGoodHeap,
      IsHeapAnchor,
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

    readonly ISet<string> letBoundVariablesWithLitRHS = new HashSet<string>();

    bool IsLit(Bpl.Expr expr) {
      if (expr is Bpl.IdentifierExpr ie) {
        return letBoundVariablesWithLitRHS.Contains(ie.Name);
      }
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
        case BuiltinFunction.AsFuelBottom:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "AsFuelBottom", predef.LayerType, args);
        case BuiltinFunction.CharFromInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "char#FromInt", predef.CharType, args);
        case BuiltinFunction.CharToInt:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "char#ToInt", predef.CharType, args);

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

        case BuiltinFunction.IsTraitParent:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IsTraitParent", Bpl.Type.Bool, args);

        case BuiltinFunction.SetCard:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "Set#Card", Bpl.Type.Int, args);
        case BuiltinFunction.SetEmpty: {
          Contract.Assert(args.Length == 0);
          Contract.Assert(typeInstantiation != null);
          Bpl.Type resultType = predef.SetType(tok, true, typeInstantiation);
          return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "Set#Empty", resultType, args), resultType);
        }
        case BuiltinFunction.SetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#UnionOne", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Union", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Intersection", predef.SetType(tok, true, typeInstantiation), args);
        case BuiltinFunction.SetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "Set#Difference", predef.SetType(tok, true, typeInstantiation), args);
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
        case BuiltinFunction.ISetEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.SetType(tok, false, typeInstantiation);
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "ISet#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.ISetUnionOne:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#UnionOne", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetUnion:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Union", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetIntersection:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Intersection", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetDifference:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation != null);
          return FunctionCall(tok, "ISet#Difference", predef.SetType(tok, false, typeInstantiation), args);
        case BuiltinFunction.ISetEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Equal", Bpl.Type.Bool, args);
        case BuiltinFunction.ISetSubset:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Subset", Bpl.Type.Bool, args);
        case BuiltinFunction.ISetDisjoint:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "ISet#Disjoint", Bpl.Type.Bool, args);
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
            Bpl.Type resultType = predef.MapType(tok, true, typeInstantiation, typeInstantiation);  // use 'typeInstantiation' (which is really always just BoxType anyway) as both type arguments
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
          Contract.Assert(args.Length == 3);
          return FunctionCall(tok, "Map#Glue", predef.MapType(tok, true, predef.BoxType, predef.BoxType), args);
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

        case BuiltinFunction.IMapEmpty: {
            Contract.Assert(args.Length == 0);
            Contract.Assert(typeInstantiation != null);
            Bpl.Type resultType = predef.MapType(tok, false, typeInstantiation, typeInstantiation);  // use 'typeInstantiation' (which is really always just BoxType anyway) as both type arguments
            return Bpl.Expr.CoerceType(tok, FunctionCall(tok, "IMap#Empty", resultType, args), resultType);
          }
        case BuiltinFunction.IMapDomain:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "IMap#Domain", typeInstantiation, args);
        case BuiltinFunction.IMapElements:
          Contract.Assert(args.Length == 1);
          return FunctionCall(tok, "IMap#Elements", typeInstantiation, args);
        case BuiltinFunction.IMapGlue:
          Contract.Assert(args.Length == 3);
          return FunctionCall(tok, "IMap#Glue", predef.MapType(tok, false, predef.BoxType, predef.BoxType), args);
        case BuiltinFunction.IMapEqual:
          Contract.Assert(args.Length == 2);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "IMap#Equal", Bpl.Type.Bool, args);

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

        case BuiltinFunction.RealToInt:
          Contract.Assume(args.Length == 1);
          Contract.Assume(typeInstantiation == null);
          return FunctionCall(tok, "Int", Bpl.Type.Int, args);
        case BuiltinFunction.IntToReal:
          Contract.Assume(args.Length == 1);
          Contract.Assume(typeInstantiation == null);
          return FunctionCall(tok, "Real", Bpl.Type.Real, args);

        case BuiltinFunction.IsGoodHeap:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsGoodHeap", Bpl.Type.Bool, args);
        case BuiltinFunction.IsHeapAnchor:
          Contract.Assert(args.Length == 1);
          Contract.Assert(typeInstantiation == null);
          return FunctionCall(tok, "$IsHeapAnchor", Bpl.Type.Bool, args);
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
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, true, apply_induction, etran);
      return splits;
    }

    List<SplitExprInfo> TrSplitExprForMethodSpec(Expression expr, ExpressionTranslator etran, MethodTranslationKind kind)
    {
      Contract.Requires(expr != null);
      Contract.Requires(etran != null);
      Contract.Ensures(Contract.Result<List<SplitExprInfo>>() != null);

      var splits = new List<SplitExprInfo>();
      var apply_induction = true;/*kind == MethodTranslationKind.Implementation*/;
      bool splitHappened;  // we don't actually care
      splitHappened = TrSplitExpr(expr, splits, true, int.MaxValue, kind != MethodTranslationKind.Call, apply_induction, etran);
      return splits;
    }

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IToken tok, Dictionary<IVariable, Expression> substMap = null)
    {
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

    Bpl.Trigger TrTrigger(ExpressionTranslator etran, Attributes attribs, IToken tok, List<Variable> bvars, Dictionary<IVariable, Expression> substMap, Dictionary<TypeParameter, Type> typeMap)
    {
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

    /// <summary>
    /// Tries to split the expression into tactical conjuncts (if "position") or disjuncts (if "!position").
    /// If a (necessarily boolean) function call appears as a top-level conjunct, then inline the function
    /// if its body is available in the current context and its height is less than "heightLimit" (if "heightLimit" is
    /// passed in as 0, then no functions will be inlined).
    /// </summary>
    bool TrSplitExpr(Expression expr, List<SplitExprInfo/*!*/>/*!*/ splits, bool position, int heightLimit, bool inlineProtectedFunctions, bool apply_induction, ExpressionTranslator etran) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType || (expr is BoxingCastExpr && ((BoxingCastExpr)expr).E.Type.IsBoolType));
      Contract.Requires(splits != null);
      Contract.Requires(etran != null);

      if (expr is BoxingCastExpr) {
        var bce = (BoxingCastExpr)expr;
        var ss = new List<SplitExprInfo>();
        if (TrSplitExpr(bce.E, ss, position, heightLimit, inlineProtectedFunctions, apply_induction, etran)) {
          foreach (var s in ss) {
            splits.Add(new SplitExprInfo(s.Kind, CondApplyBox(s.E.tok, s.E, bce.FromType, bce.ToType)));
          }
          return true;
        }

      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return TrSplitExpr(e.ResolvedExpression, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (!e.Exact) {
          var d = LetDesugaring(e);
          return TrSplitExpr(d, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
        } else {
          var ss = new List<SplitExprInfo>();
          if (TrSplitExpr(e.Body, ss, position, heightLimit, inlineProtectedFunctions, apply_induction, etran)) {
            // We don't know where the RHSs of the let are used in the body. In particular, we don't know if a RHS
            // will end up in a spot where TrSplitExpr would like to increase the Layer offset or not. In fact, different
            // uses of the same let variable may end up needing different Layer constants. The following code will
            // always bump the Layer offset in the RHS. This seems likely to be desireable in many cases, because the
            // LetExpr sits in a position for which TrSplitExpr is invoked.
            List<Bpl.Variable> lhss;
            List<Bpl.Expr> rhss;
            etran.LayerOffset(1).TrLetExprPieces(e, out lhss, out rhss);
            foreach (var s in ss) {
              // as the source location in the following let, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.Kind, new Bpl.LetExpr(s.E.tok, lhss, rhss, null, s.E)));
            }
            return true;
          }
        }

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        if (position && e.Frame.Count > 1) {
          // split into a number of UnchangeExpr's, one for each FrameExpression
          foreach (var fe in e.Frame) {
            var tok = new NestedToken(e.tok, fe.tok);
            Expression ee = new UnchangedExpr(tok, new List<FrameExpression> { fe }, e.At) { AtLabel = e.AtLabel };
            ee.Type = Type.Bool;  // resolve here
            TrSplitExpr(ee, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          }
          return true;
        }

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        if (e.Op == UnaryOpExpr.Opcode.Not) {
          var ss = new List<SplitExprInfo>();
          if (TrSplitExpr(e.E, ss, !position, heightLimit, inlineProtectedFunctions, apply_induction, etran)) {
            foreach (var s in ss) {
              splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Unary(s.E.tok, UnaryOperator.Opcode.Not, s.E)));
            }
            return true;
          }
        }

      } else if (expr is BinaryExpr) {
        var bin = (BinaryExpr)expr;
        if (position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          return true;

        } else  if (!position && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Or) {
          TrSplitExpr(bin.E0, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          TrSplitExpr(bin.E1, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          return true;

        } else if (bin.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp) {
          // non-conditionally split these, so we get the source location to point to a subexpression
          if (position) {
            var lhs = etran.TrExpr(bin.E0);
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E1, ss, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
            foreach (var s in ss) {
              // as the source location in the following implication, use that of the translated "s"
              splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, lhs, s.E)));
            }
          } else {
            var ss = new List<SplitExprInfo>();
            TrSplitExpr(bin.E0, ss, !position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
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
          // split as shown here for possibly infinite lists:
          //   checked $PrefixEqual#Dt(k, A, B) || (k_has_successor ==> A.Nil? ==> B.Nil?)
          //   checked $PrefixEqual#Dt(k, A, B) || (k_has_successor ==> A.Cons? ==> B.Cons? && A.head == B.head && $PrefixEqual#2#Dt(k - 1, A.tail, B.tail))  // note the #2 in the recursive call, just like for user-defined predicates that are inlined by TrSplitExpr
          //   checked $PrefixEqual#Dt(k, A, B) || (k != 0 && k.IsLimit ==> $Equal#Dt(A, B))  // (*)
          //   free $PrefixEqual#Dt(k, A, B);
          // Note:  First off, (*) is used only when ORDINAL is involved. Moreover, if there's an error among the first checked
          // conditions, it seems confusing to get yet another error message.  Therefore, we add a middle disjunct to (*), namely
          // the conjunction of all the previous RHSs.
          var kAsORD = !e.E0.Type.IsBigOrdinalType && !TernaryExpr.PrefixEqUsesNat ? FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, k) : k;
          var prefixEqK = CoEqualCall(codecl, e1type.TypeArgs, e2type.TypeArgs, kAsORD, etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), A, B); // FunctionCall(expr.tok, CoPrefixName(codecl, 1), Bpl.Type.Bool, k, A, B);
          Bpl.Expr kHasSuccessor, kMinusOne;
          if (e.E0.Type.IsBigOrdinalType) {
            kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), FunctionCall(k.tok, "ORD#Offset", Bpl.Type.Int, k));
            kMinusOne = FunctionCall(k.tok, "ORD#Minus", predef.BigOrdinalType, k, FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, Bpl.Expr.Literal(1)));
          } else {
            kHasSuccessor = Bpl.Expr.Lt(Bpl.Expr.Literal(0), k);
            kMinusOne = Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
            if (!TernaryExpr.PrefixEqUsesNat) {
              kMinusOne = FunctionCall(k.tok, "ORD#FromNat", Bpl.Type.Int, kMinusOne);
            }
          }
          // for the inlining of the definition of prefix equality, translate the two main equality operands arguments with a higher offset (to obtain #2 functions)
          var etran2 = etran.LayerOffset(1);
          var A2 = etran2.TrExpr(e.E1);
          var B2 = etran2.TrExpr(e.E2);
          var needsTokenAdjust = TrSplitNeedsTokenAdjustment(expr);
          var tok = needsTokenAdjust ? new ForceCheckToken(expr.tok) : expr.tok;
          Bpl.Expr layer = etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH);
          Bpl.Expr eqComponents = Bpl.Expr.True;
          foreach (var c in CoPrefixEquality(tok, codecl, e1type.TypeArgs, e2type.TypeArgs, kMinusOne, layer, A2, B2, true)) {
            eqComponents = BplAnd(eqComponents, c);
            var p = Bpl.Expr.Binary(c.tok, BinaryOperator.Opcode.Or, prefixEqK, Bpl.Expr.Imp(kHasSuccessor, c));
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, p));
          }
          if (e.E0.Type.IsBigOrdinalType) {
            var kIsNonZeroLimit = BplAnd(
              Bpl.Expr.Neq(k, FunctionCall(k.tok, "ORD#FromNat", predef.BigOrdinalType, Bpl.Expr.Literal(0))),
              FunctionCall(k.tok, "ORD#IsLimit", Bpl.Type.Bool, k));
            var eq = CoEqualCall(codecl, e1type.TypeArgs, e2type.TypeArgs, null, etran.layerInterCluster.LayerN((int)FuelSetting.FuelAmount.HIGH), A, B);
            var p = Bpl.Expr.Binary(tok, BinaryOperator.Opcode.Or, prefixEqK, BplOr(BplImp(kHasSuccessor, eqComponents), Bpl.Expr.Imp(kIsNonZeroLimit, eq)));
            splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, p));
          }
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, prefixEqK));
          return true;
        }

      } else if (expr is ITEExpr) {
        var ite = (ITEExpr)expr;

        var ssThen = new List<SplitExprInfo>();
        var ssElse = new List<SplitExprInfo>();

        TrSplitExpr(ite.Thn, ssThen, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
        TrSplitExpr(ite.Els, ssElse, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);

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

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var ite = etran.DesugarMatchExpr(e);
        return TrSplitExpr(ite, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        // For an expression S;E in split position, the conclusion of S can be used as an assumption.  Unfortunately,
        // this assumption is not generated in non-split positions (because I don't know how.)
        // So, treat "S; E" like "SConclusion ==> E".
        if (position) {
          var conclusion = etran.TrExpr(e.GetSConclusion());
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.E, ss, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, conclusion, s.E)));
          }
        } else {
          var ss = new List<SplitExprInfo>();
          TrSplitExpr(e.GetSConclusion(), ss, !position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
          var rhs = etran.TrExpr(e.E);
          foreach (var s in ss) {
            // as the source location in the following implication, use that of the translated "s"
            splits.Add(new SplitExprInfo(s.Kind, Bpl.Expr.Binary(s.E.tok, BinaryOperator.Opcode.Imp, s.E, rhs)));
          }
        }
        return true;

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return TrSplitExpr(e.E, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran.OldAt(e.AtLabel));

      } else if (expr is FunctionCallExpr && position) {
        var fexp = (FunctionCallExpr)expr;
        var f = fexp.Function;
        Contract.Assert(f != null);  // filled in during resolution
        var module = f.EnclosingClass.EnclosingModuleDefinition;
        var functionHeight = module.CallGraph.GetSCCRepresentativeId(f);

        if (functionHeight < heightLimit && f.Body != null && RevealedInScope(f)) {
          if (RefinementToken.IsInherited(fexp.tok, currentModule) &&
              f is Predicate && ((Predicate)f).BodyOrigin == Predicate.BodyOriginKind.DelayedDefinition &&
              (codeContext == null || !codeContext.MustReverify)) {
            // The function was inherited as body-less but is now given a body. Don't inline the body (since, apparently, everything
            // that needed to be proved about the function was proved already in the previous module, even without the body definition).
          } else if (!FunctionBodyIsAvailable(f, currentModule, currentScope, inlineProtectedFunctions)) {
            // Don't inline opaque functions
          } else if (Attributes.Contains(f.Attributes, "no_inline")) {
            // User manually prevented inlining
          } else {
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

            if (!CanSafelyInline(fexp, f)) {
              // Skip inlining, as it would cause arbitrary expressions to pop up in the trigger
              // TODO this should appear at the outmost call site, not at the innermost. See SnapshotableTrees.dfy
              reporter.Info(MessageSource.Translator, fexp.tok, "Some instances of this call cannot safely be inlined.");
              // F#canCall(args) ==> F(args)
              var p = Bpl.Expr.Binary(fargs.tok, BinaryOperator.Opcode.Imp, canCall, fargs);
              splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, p));
              // F#canCall(args) && F(args)
              var fr = Bpl.Expr.And(canCall, fargs);
              splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, fr));

            } else {
              // inline this body
              var typeSpecializedBody = GetSubstitutedBody(fexp, f);
              var typeSpecializedResultType = Resolver.SubstType(f.ResultType, fexp.GetTypeArgumentSubstitutions());

              // recurse on body
              var ss = new List<SplitExprInfo>();
              TrSplitExpr(typeSpecializedBody, ss, position, functionHeight, inlineProtectedFunctions, apply_induction, etran);
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

              // allocatedness for arguments to the inlined call in body
              if (typeSpecializedBody is FunctionCallExpr) {
                FunctionCallExpr e = (FunctionCallExpr)typeSpecializedBody;
                for (int i = 0; i < e.Args.Count; i++) {
                  Expression ee = e.Args[i];
                  Type t = e.Function.Formals[i].Type;
                  Expr tr_ee = etran.TrExpr(ee);
                  Bpl.Expr wh = GetWhereClause(e.tok, tr_ee, cce.NonNull(ee.Type), etran, NOALLOC);
                  if (wh != null) { fargs = Bpl.Expr.And(fargs, wh); }
                }
              }

              // body
              var trBody = etran.TrExpr(typeSpecializedBody);
              trBody = CondApplyUnbox(trBody.tok, trBody, typeSpecializedResultType, expr.Type);
              // F#canCall(args) && F(args) && (b0 && b1 && b2)
              var fr = Bpl.Expr.And(canCall, BplAnd(fargs, trBody));
              splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, fr));
            }

            return true;
          }
        }

      } else if (expr is QuantifierExpr && ((QuantifierExpr)expr).SplitQuantifier != null) {
        return TrSplitExpr(((QuantifierExpr)expr).SplitQuantifierExpression, splits, position, heightLimit, inlineProtectedFunctions, apply_induction, etran);
      } else if (((position && expr is ForallExpr) || (!position && expr is ExistsExpr))
        /* NB: only for type arg less quantifiers for now: */
            && ((QuantifierExpr)expr).TypeArgs.Count == 0) {
        var e = (QuantifierExpr)expr;
        var inductionVariables = ApplyInduction(e.BoundVars, e.Attributes);
        if (apply_induction && inductionVariables.Count != 0) {
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
            types.Add(n.Type.NormalizeExpandKeepConstraints());
            BoundVar k = new BoundVar(n.tok, CurrentIdGenerator.FreshId(n.Name + "$ih#"), n.Type);
            kvars.Add(k);

            IdentifierExpr ieK = new IdentifierExpr(k.tok, k.AssignUniqueName(currentDeclaration.IdGenerator));
            ieK.Var = k; ieK.Type = ieK.Var.Type;  // resolve it here
            kk.Add(etran.TrExpr(ieK));

            IdentifierExpr ieN = new IdentifierExpr(n.tok, n.AssignUniqueName(currentDeclaration.IdGenerator));
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
          Bpl.Expr typeAntecedent = etran.TrBoundVariables(kvars, bvars);  // no need to use allocation antecedent here, because the well-founded less-than ordering assures kk are allocated
          Bpl.Expr ih;
          var tr = TrTrigger(etran, e.Attributes, expr.tok, substMap);
          ih = new Bpl.ForallExpr(expr.tok, bvars, tr, Bpl.Expr.Imp(typeAntecedent, ihBody));

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
          List<bool> freeOfAlloc = null;
          if (FrugalHeapUseX) {
            freeOfAlloc = ComprehensionExpr.BoundedPool.HasBounds(e.Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc);
          }
          bvars = new List<Variable>();
          typeAntecedent = etran.TrBoundVariables(e.BoundVars, bvars, false, freeOfAlloc);
          foreach (var kase in caseProduct) {
            var ante = BplAnd(BplAnd(typeAntecedent, ih), kase);
            var etranBody = etran.LayerOffset(1);
            var bdy = etranBody.TrExpr(e.LogicalBody());
            Bpl.Expr q;
            var trig = TrTrigger(etranBody, e.Attributes, expr.tok);
            if (position) {
              q = new Bpl.ForallExpr(kase.tok, bvars, trig, Bpl.Expr.Imp(ante, bdy));
            } else {
              q = new Bpl.ExistsExpr(kase.tok, bvars, trig, Bpl.Expr.And(ante, bdy));
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
      } else if (((position && expr is ExistsExpr) || (!position && expr is ForallExpr))
        /* NB: only for type arg less quantifiers for now: */
            && ((QuantifierExpr)expr).TypeArgs.Count == 0) {
        // produce two translated versions of the quantifier, one that uses #1 functions (that is, layerOffset 0)
        // for checking and one that uses #2 functions (that is, layerOffset 1) for assuming.
        adjustFuelForExists = false; // based on the above comment, we use the etran with correct fuel amount already. No need to adjust anymore.
        var etranBoost = etran.LayerOffset(1);
        var r = etran.TrExpr(expr);
        var needsTokenAdjustment = TrSplitNeedsTokenAdjustment(expr);
        if (needsTokenAdjustment) {
          r.tok = new ForceCheckToken(expr.tok);
        }
        if (etran.Statistics_CustomLayerFunctionCount == 0) {
          // apparently, doesn't use layer
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Both, r));
          return needsTokenAdjustment;
        } else {
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Checked, r));  // check the ordinary expression
          splits.Add(new SplitExprInfo(SplitExprInfo.K.Free, etranBoost.TrExpr(expr)));  // assume the boosted expression
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
      if (TrSplitNeedsTokenAdjustment(expr)) {
        translatedExpression.tok = new ForceCheckToken(expr.tok);
        splitHappened = true;
      }
      splits.Add(new SplitExprInfo(SplitExprInfo.K.Both, translatedExpression));
      return splitHappened;
    }

    private bool CanSafelyInline(FunctionCallExpr fexp, Function f) {
      if (f is PrefixPredicate prefixPred && !prefixPred.ExtremePred.KNat) {
        // A prefix predicate indexed by an ORDINAL has an implicit quantifier in its body, so don't inline it,
        // because then we may end up with arbitrary expressions in triggers
        return false;
      }

      var visitor = new TriggersExplorer();
      visitor.Visit(f);
      return LinqExtender.Zip(f.Formals, fexp.Args).All(formal_concrete => CanSafelySubstitute(visitor.TriggerVariables, formal_concrete.Item1, formal_concrete.Item2));
    }

    // Using an empty set of old expressions is ok here; the only uses of the triggersCollector will be to check for trigger killers.
    Triggers.TriggersCollector triggersCollector = new Triggers.TriggersCollector(new Dictionary<Expression, HashSet<OldExpr>>());

    private bool CanSafelySubstitute(ISet<IVariable> protectedVariables, IVariable variable, Expression substitution) {
      return !(protectedVariables.Contains(variable) && triggersCollector.IsTriggerKiller(substitution));
    }

    private class VariablesCollector: BottomUpVisitor {
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

    private class TriggersExplorer : BottomUpVisitor {
      VariablesCollector collector;

      internal ISet<IVariable> TriggerVariables { get { return collector.variables; } }

      internal TriggersExplorer() {
        collector = new VariablesCollector();
      }

      protected override void VisitOneExpr(Expression expr) {
        if (expr is QuantifierExpr) {
          var e = (QuantifierExpr)expr;
          if (e.SplitQuantifier == null) {
            foreach (var trigger in (expr as QuantifierExpr).Attributes.AsEnumerable().Where(a => a.Name == "trigger").SelectMany(a => a.Args)) {
              collector.Visit(trigger);
            }
          }
        }
      }
    }

    private Expression GetSubstitutedBody(FunctionCallExpr fexp, Function f) {
      Contract.Requires(fexp != null);
      Contract.Requires(f != null);
      var substMap = new Dictionary<IVariable, Expression>();
      Contract.Assert(fexp.Args.Count == f.Formals.Count);
      for (int i = 0; i < f.Formals.Count; i++) {
        Formal p = f.Formals[i];
        var formalType = Resolver.SubstType(p.Type, fexp.GetTypeArgumentSubstitutions());
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
      body = Substitute(body, fexp.Receiver, substMap, fexp.GetTypeArgumentSubstitutions());
      return body;
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
              Bpl.Expr wh = GetWhereClause(arg.tok, CondApplyUnbox(arg.tok, args[i], arg.Type, instantiatedArgType), instantiatedArgType, etran, NOALLOC);
              if (wh != null) {
                typeAntecedent = BplAnd(typeAntecedent, wh);
              }
              i++;
            }
            var trigger = BplTrigger(ct);  // this is probably never used, because this quantifier is not expected ever to appear in a context where it needs to be instantiated
            q = new Bpl.ExistsExpr(ctor.tok, bvs, trigger, BplAnd(typeAntecedent, q));
          }
          yield return q;
        }
      }
    }

    /// <summary>
    /// Returns true iff
    ///   (if 'v' is non-null) 'v' occurs as a free variable in 'expr' or
    ///   (if 'lookForReceiver' is true) 'this' occurs in 'expr'.
    /// </summary>
    public static bool ContainsFreeVariable(Expression expr, bool lookForReceiver, IVariable v) {
      Contract.Requires(expr != null);
      Contract.Requires(lookForReceiver || v != null);

      if (expr is ThisExpr) {
        return lookForReceiver;
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
      expr.ComponentTypes.Iter(ty => ComputeFreeTypeVariables(ty, fvs));
      expr.SubExpressions.Iter(ee => ComputeFreeTypeVariables(ee, fvs));
    }

    static void ComputeFreeTypeVariables(Type ty, ISet<TypeParameter> fvs) {
      // Add type parameters
      var tp = ty.AsTypeParameter;
      if (tp != null) {
        Contract.Assert(ty.TypeArgs.Count == 0);
        fvs.Add(tp);
      } else {
        ty.NormalizeExpandKeepConstraints().TypeArgs.Iter(tt => ComputeFreeTypeVariables(tt, fvs));
      }
    }

    static void ComputeFreeTypeVariables_All(Type ty, ISet<TypeParameter> fvs) {
      // Add type parameters
      if (ty.IsTypeParameter) {
        fvs.Add(ty.AsTypeParameter);
      }
      ty.NormalizeExpandKeepConstraints().TypeArgs.Iter(tt => ComputeFreeTypeVariables_All(tt, fvs));
    }

    public static ISet<IVariable> ComputeFreeVariables(Expression expr) {
      Contract.Requires(expr != null);
      ISet<IVariable> fvs = new HashSet<IVariable>();
      ComputeFreeVariables(expr, fvs);
      return fvs;
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare0 = false, dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(expr, fvs, ref dontCare0, ref dontCare1, dontCareHeapAt, ref dontCareT);
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs, ref bool usesHeap) {
      Contract.Requires(expr != null);
      Contract.Requires(fvs != null);
      bool dontCare1 = false;
      Type dontCareT = null;
      var dontCareHeapAt = new HashSet<Label>();
      ComputeFreeVariables(expr, fvs, ref usesHeap, ref dontCare1, dontCareHeapAt, ref dontCareT);
    }
    public static void ComputeFreeVariables(Expression expr, ISet<IVariable> fvs, ref bool usesHeap, ref bool usesOldHeap, ISet<Label> freeHeapAtVariables, ref Type usesThis) {
      Contract.Requires(expr != null);

      if (expr is ThisExpr) {
        Contract.Assert(expr.Type != null);
        usesThis = expr.Type;
        return;
      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        fvs.Add(e.Var);
        return;
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        if (e.Obj.Type.IsRefType && !(e.Member is ConstantField)) {
          usesHeap = true;
        }
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
        Function f = ((FunctionCallExpr)expr).Function;
        if (AlwaysUseHeap || f == null || f.ReadsHeap) {
          usesHeap = true;
        }
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        // Note, we don't have to look out for const fields here, because const fields
        // are not allowed in unchanged expressions.
        usesHeap = true;
        if (e.AtLabel == null) {
          usesOldHeap = true;
        } else {
          freeHeapAtVariables.Add(e.AtLabel);
        }
      } else if (expr is ApplyExpr) {
        usesHeap = true; // because the translation of an ApplyExpr always throws in the heap variable
      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr) expr;
        if (e.Op == UnaryOpExpr.Opcode.Fresh) {
          usesOldHeap = true;
        } else if (e.Op == UnaryOpExpr.Opcode.Allocated) {
          usesHeap = true;
        }
      }

      // visit subexpressions
      bool uHeap = false, uOldHeap = false;
      Type uThis = null;
      foreach(var subExpression in expr.SubExpressions) {
        ComputeFreeVariables(subExpression, fvs, ref uHeap, ref uOldHeap, freeHeapAtVariables, ref uThis);
      }
      Contract.Assert(usesThis == null || uThis == null || usesThis.Equals(uThis));
      usesThis = usesThis ?? uThis;
      var asOldExpr = expr as OldExpr;
      if (asOldExpr != null && asOldExpr.AtLabel == null) {
        usesOldHeap |= uHeap | uOldHeap;
      } else if (asOldExpr != null) {
        if (uHeap) {  // if not, then there was no real point in using an "old" expression
          freeHeapAtVariables.Add(asOldExpr.AtLabel);
        }
        usesOldHeap |= uOldHeap;
      } else {
        usesHeap |= uHeap;
        usesOldHeap |= uOldHeap;
      }

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
      } else if (expr is MatchExpr me) {
        foreach (var v in me.Cases.SelectMany(c => c.Arguments)) {
          fvs.Remove(v);
        }
      }
    }

    public static bool NonGhostsUseHeap { get { return DafnyOptions.O.Allocated == 1 || DafnyOptions.O.Allocated == 2; } }
    public static bool AlwaysUseHeap { get { return DafnyOptions.O.Allocated == 2; } }
    public static bool CommonHeapUse { get { return DafnyOptions.O.Allocated >= 2; } }
    public static bool FrugalHeapUse { get { return DafnyOptions.O.Allocated >= 3; } }
    public static bool FrugalHeapUseX { get { return DafnyOptions.O.Allocated == 4; } }

    public static bool UsesHeap(Expression expr) {
      UsesHeapVisitor visitor = new UsesHeapVisitor();
      visitor.Visit(expr);
      if (visitor.foundHeap) {
        return true;
      }
      bool usesHeap = false, usesOldHeap = false;
      var FVsHeapAt = new HashSet<Label>();
      Type usesThis = null;
      ComputeFreeVariables(expr, new HashSet<IVariable>(), ref usesHeap, ref usesOldHeap, FVsHeapAt, ref usesThis);
      return usesHeap || usesOldHeap || FVsHeapAt.Count != 0;
    }

    class UsesHeapVisitor : BottomUpVisitor
    {
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

    public static Expression Substitute(Expression expr, Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type>/*?*/ typeMap = null) {
      Contract.Requires(expr != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new Substituter(receiverReplacement, substMap, typeMap ?? new Dictionary<TypeParameter, Type>());
      return s.Substitute(expr);
    }

    public static Expression InlineLet(LetExpr letExpr) {
      Contract.Requires(letExpr.LHSs.All(p => p.Var != null));
      var substMap = new Dictionary<IVariable, Expression>();
      for (var i = 0; i < letExpr.LHSs.Count; i++) {
        substMap.Add(letExpr.LHSs[i].Var, letExpr.RHSs[i]);
      }
      return Translator.Substitute(letExpr.Body, null, substMap);
    }

    public class FunctionCallSubstituter : Substituter
    {
      public readonly Function A, B;
      public FunctionCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Function a, Function b)
        : base(receiverReplacement, substMap, new Dictionary<TypeParameter,Type>()) {
        A = a;
        B = b;
      }
      public override Expression Substitute(Expression expr) {
        if (expr is FunctionCallExpr) {
          FunctionCallExpr e = (FunctionCallExpr)expr;
          Expression receiver = Substitute(e.Receiver);
          List<Expression> newArgs = SubstituteExprList(e.Args);
          FunctionCallExpr newFce = new FunctionCallExpr(expr.tok, e.Name, receiver, e.OpenParen, newArgs, e.AtLabel);
          if (e.Function == A) {
            newFce.Function = B;
            newFce.Type = e.Type; // TODO: this may not work with type parameters.
          } else {
            newFce.Function = e.Function;
            newFce.Type = e.Type;
          }
          newFce.TypeApplication_AtEnclosingClass = e.TypeApplication_AtEnclosingClass;  // resolve here
          newFce.TypeApplication_JustFunction = e.TypeApplication_JustFunction;  // resolve here
          return newFce;
        }
        return base.Substitute(expr);
      }
    }
    public class PrefixCallSubstituter : Substituter
    {
      readonly ExtremePredicate extremePred;
      readonly Expression unrollDepth;
      readonly ModuleDefinition module;
      public PrefixCallSubstituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> tySubstMap, ExtremePredicate extremePredicate, Expression depth)
        : base(receiverReplacement, substMap, tySubstMap) {
        Contract.Requires(extremePredicate != null);
        Contract.Requires(depth != null);
        extremePred = extremePredicate;
        unrollDepth = depth;
        module = extremePredicate.EnclosingClass.EnclosingModuleDefinition;
      }
      public override Expression Substitute(Expression expr) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
          var cof = e.Function as ExtremePredicate;
          if (cof != null && ModuleDefinition.InSameSCC(cof, extremePred)) {
            expr = cof.CreatePrefixPredicateCall(e, unrollDepth);
          }
        }
        return base.Substitute(expr);
      }
    }

    public class ExprSubstituter : Substituter {
      readonly List<Tuple<Expression, IdentifierExpr>> exprSubstMap;
      List<Tuple<Expression, IdentifierExpr>> usedSubstMap;

      public ExprSubstituter(List<Tuple<Expression, IdentifierExpr>> exprSubstMap)
        : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter,Type>()) {
        this.exprSubstMap = exprSubstMap;
        this.usedSubstMap = new List<Tuple<Expression, IdentifierExpr>>();
      }

      public bool TryGetExprSubst(Expression expr, out IdentifierExpr ie) {
        var entry = usedSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
        if (entry != null) {
          ie = entry.Item2;
          return true;
        }
        entry = exprSubstMap.Find(x => Triggers.ExprExtensions.ExpressionEq(expr, x.Item1));
        if (entry != null) {
          usedSubstMap.Add(entry);
          ie = entry.Item2;
          return true;
        } else {
          ie = null;
          return false;
        }
      }

      public override Expression Substitute(Expression expr) {
        if (TryGetExprSubst(expr, out var ie)) {
          Contract.Assert(ie != null);
          return ie;
        }
        if (expr is QuantifierExpr e) {
          var newAttrs = SubstAttributes(e.Attributes);
          var newRange = e.Range == null ? null : Substitute(e.Range);
          var newTerm = Substitute(e.Term);
          var newBounds = SubstituteBoundedPoolList(e.Bounds);
          if (newAttrs == e.Attributes && newRange == e.Range && newTerm == e.Term && newBounds == e.Bounds) {
            return e;
          }

          var newBoundVars = new List<BoundVar>(e.BoundVars);
          if (newBounds == null) {
            newBounds = new List<ComprehensionExpr.BoundedPool>();
          } else if (newBounds == e.Bounds) {
            // create a new list with the same elements, since the .Add operations below would otherwise add elements to the original e.Bounds
            newBounds = new List<ComprehensionExpr.BoundedPool>(newBounds);
          }

          // conjoin all the new equalities to the range of the quantifier
          foreach (var entry in usedSubstMap) {
            var eq = new BinaryExpr(e.tok, BinaryExpr.ResolvedOpcode.EqCommon, entry.Item2, entry.Item1);
            newRange = newRange == null ? eq : new BinaryExpr(e.tok, BinaryExpr.ResolvedOpcode.And, eq, newRange);
            newBoundVars.Add((BoundVar)entry.Item2.Var);
            newBounds.Add(new ComprehensionExpr.ExactBoundedPool(entry.Item1));
          }

          QuantifierExpr newExpr;
          if (expr is ForallExpr) {
            newExpr = new ForallExpr(e.tok, e.TypeArgs, newBoundVars, newRange, newTerm, newAttrs) { Bounds = newBounds };
          } else {
            Contract.Assert(expr is ExistsExpr);
            newExpr = new ExistsExpr(e.tok, e.TypeArgs, newBoundVars, newRange, newTerm, newAttrs) { Bounds = newBounds };
          }
          usedSubstMap.Clear();

          newExpr.Type = expr.Type;
          return newExpr;
        }
        return base.Substitute(expr);
      }
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
        tt.Tr.Iter(ee => vis.Visit(ee));
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
    class VariableNameVisitor : Boogie.StandardVisitor
    {
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
        return base.VisitBinderExpr(node);
      }
    }

    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Expr body) {
      Contract.Requires(args_in != null);
      Contract.Requires(body != null);
      Contract.Ensures(Contract.Result<Bpl.Expr>() != null);
      var args = new List<Bpl.Variable>(args_in);
      if (args.Count == 0) {
        return body;
      } else {
        return new Bpl.ForallExpr(body.tok, args, body); // NO_TRIGGER
      }
    }

    // Note: if the trigger is null, makes a forall without any triggers
    static Bpl.Expr BplForall(IEnumerable<Bpl.Variable> args_in, Bpl.Trigger trg, Bpl.Expr body) {
      if (trg == null) {
        return BplForall(args_in, body); // NO_TRIGGER
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

    static Bpl.Expr BplForall(IToken tok, List<TypeVariable> typeParams,
      List<Variable> formals, QKeyValue kv, Trigger triggers, Bpl.Expr body, bool immutable = false)
    {
      return (typeParams.Count == 0 && formals.Count == 0) ? body
        : new Bpl.ForallExpr(tok, typeParams, formals, kv, triggers, body, immutable);
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

      if (a == Bpl.Expr.True || b == Bpl.Expr.True) {
        return b;
      } else if (a == Bpl.Expr.False) {
        return Bpl.Expr.True;
      } else {
        return Bpl.Expr.Imp(a, b);
      }
    }

    private static void BplIfIf(IToken tk, bool yes, Bpl.Expr guard, BoogieStmtListBuilder builder, Action<BoogieStmtListBuilder> k) {
      if (yes) {
        var newBuilder = new BoogieStmtListBuilder(builder.tran);
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
      return new Bpl.Trigger(e.tok, true, new List<Bpl.Expr> { e });
    }

    static Bpl.Trigger BplTriggerHeap(Translator translator, IToken tok, Bpl.Expr e, Bpl.Expr/*?*/ optionalHeap, Bpl.Expr/*?*/ ePrime = null) {
      Contract.Requires(translator != null);
      Contract.Requires(tok != null);
      Contract.Requires(e != null);

      var exprs = new List<Bpl.Expr> {e};
      if (ePrime != null) {
        exprs.Add(ePrime);
      }
      if (optionalHeap != null) {
        exprs.Add(translator.FunctionCall(tok, BuiltinFunction.IsGoodHeap, null, optionalHeap));
      }
      return new Bpl.Trigger(tok, true, exprs);
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
    static Bpl.Formal BplFormalVar(string/*?*/ name, Bpl.Type ty, bool incoming) {
      Bpl.Expr _scratch;
      return BplFormalVar(name, ty, incoming, out _scratch);
    }

    static Bpl.Formal BplFormalVar(string/*?*/ name, Bpl.Type ty, bool incoming, out Bpl.Expr e) {
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

    public static List<B> Map<A,B>(IEnumerable<A> xs, Func<A,B> f) {
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
