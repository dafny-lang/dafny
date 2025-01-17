using System;
using System.Collections;
using System.Collections.Generic;
using System.Collections.Specialized;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Security.Cryptography;
using System.Security.Policy;

namespace Microsoft.Dafny;

public class SystemModuleManager {
  public DafnyOptions Options { get; }
  public readonly ModuleDefinition SystemModule;
  internal readonly Dictionary<int, ClassDecl> arrayTypeDecls = new();
  public readonly Dictionary<int, ArrowTypeDecl> ArrowTypeDecls = new();
  public readonly Dictionary<int, SubsetTypeDecl> PartialArrowTypeDecls = new();  // same keys as arrowTypeDecl
  public readonly Dictionary<int, SubsetTypeDecl> TotalArrowTypeDecls = new();  // same keys as arrowTypeDecl
  readonly Dictionary<List<bool>, TupleTypeDecl> tupleTypeDecls = new(new Dafny.IEnumerableComparer<bool>());

  internal readonly ValuetypeDecl[] valuetypeDecls;

  /// <summary>
  /// PreTypeBuiltins is stored here once for the entire program, so that its ToplevelDecl's are unique across the program.
  /// It is used by the pre-type resolver, and its entries are filled in lazily by the pre-type resolver. There may be overlap
  /// between the values of PreTypeBuiltins and the values in the dictionaries above.
  /// </summary>
  public readonly Dictionary<string, TopLevelDecl> PreTypeBuiltins = new();

  public ModuleSignature systemNameInfo;

  public int MaxNonGhostTupleSizeUsed { get; private set; }
  public IOrigin MaxNonGhostTupleSizeToken { get; private set; }

  private byte[] hash;

  public byte[] MyHash {
    get {
      if (hash == null) {

        // A tuple type is defined by a list of booleans, where the size of the list determines how many elements the tuple has,
        // and the value of each boolean determines whether that value is ghost or not.
        // Here we represent the tuple type as an integer by translating each boolean to a bit and packing the bits in an int.
        var tupleInts = tupleTypeDecls.Keys.Select(tuple => {
          var vector32 = new BitVector32();
          if (tuple.Count > 32) {
            throw new Exception("Tuples of size larger than 32 are not supported");
          }
          for (var index = 0; index < tuple.Count; index++) {
            vector32[index] = tuple[index];
          }
          return vector32.Data;
        });
        var ints =
          new[] {
            arrayTypeDecls.Count, ArrowTypeDecls.Count, PartialArrowTypeDecls.Count, TotalArrowTypeDecls.Count,
            tupleTypeDecls.Count
          }.
            Concat(arrayTypeDecls.Keys.OrderBy(x => x)).
            Concat(ArrowTypeDecls.Keys.OrderBy(x => x)).
            Concat(PartialArrowTypeDecls.Keys.OrderBy(x => x)).
            Concat(TotalArrowTypeDecls.Keys.OrderBy(x => x)).
            Concat(tupleInts.OrderBy(x => x));
        var bytes = ints.SelectMany(BitConverter.GetBytes).ToArray();
        hash = SHA256.Create()!.ComputeHash(bytes);
      }

      return hash;
    }
  }

  public readonly ISet<int> Bitwidths = new HashSet<int>();
  [FilledInDuringResolution] public SpecialField ORDINAL_Offset;  // used by the translator

  public readonly SubsetTypeDecl NatDecl;
  public UserDefinedType Nat() { return new UserDefinedType(Token.NoToken, "nat", NatDecl, new List<Type>()); }
  public readonly TraitDecl ObjectDecl;
  public UserDefinedType ObjectQ() {
    Contract.Assume(ObjectDecl != null);
    return new UserDefinedType(Token.NoToken, "object?", null) { ResolvedClass = ObjectDecl };
  }
  /// <summary>
  /// Return a resolved type for "set<object?>".
  /// </summary>
  public Type ObjectSetType() {
    return new SetType(true, ObjectQ());
  }

  public SystemModuleManager(DafnyOptions options) {
    SystemModule = new(SourceOrigin.NoToken, new Name("_System"), new List<IOrigin>(),
      ModuleKindEnum.Concrete, false, null, null, null);
    this.Options = options;
    SystemModule.Height = -1;  // the system module doesn't get a height assigned later, so we set it here to something below everything else
    // create type synonym 'string'
    var str = new TypeSynonymDecl(SourceOrigin.NoToken, new Name("string"),
      new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
      new List<TypeParameter>(), SystemModule, new SeqType(new CharType()), null);
    SystemModule.SourceDecls.Add(str);
    // create subset type 'nat'
    var bvNat = new BoundVar(Token.NoToken, "x", Type.Int);
    var natConstraint = Expression.CreateAtMost(Expression.CreateIntLiteral(Token.NoToken, 0), Expression.CreateIdentExpr(bvNat));
    var ax = AxiomAttribute();
    NatDecl = new SubsetTypeDecl(SourceOrigin.NoToken, new Name("nat"),
      new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
      new List<TypeParameter>(), SystemModule, bvNat, natConstraint, SubsetTypeDecl.WKind.CompiledZero, null, ax);
    ((RedirectingTypeDecl)NatDecl).ConstraintIsCompilable = true;
    SystemModule.SourceDecls.Add(NatDecl);
    // create trait 'object'
    ObjectDecl = new TraitDecl(SourceOrigin.NoToken, new Name("object"), SystemModule, new List<TypeParameter>(), new List<MemberDecl>(), DontCompile(), false, null);
    SystemModule.SourceDecls.Add(ObjectDecl);
    // add one-dimensional arrays, since they may arise during type checking
    // Arrays of other dimensions may be added during parsing as the parser detects the need for these
    UserDefinedType tmp = ArrayType(1, Type.Int, true);
    // Arrow types of other dimensions may be added during parsing as the parser detects the need for these.  For the 0-arity
    // arrow type, the resolver adds a Valid() predicate for iterators, whose corresponding arrow type is conveniently created here.
    CreateArrowTypeDecl(0);


    // Map#Items relies on the two destructors for 2-tuples
    TupleType(Token.NoToken, 2, true);
    // Several methods and fields rely on 1-argument arrow types
    CreateArrowTypeDecl(1);

    valuetypeDecls = new[] {
      new ValuetypeDecl("bool", SystemModule, t => t.IsBoolType, typeArgs => Type.Bool),
      new ValuetypeDecl("char", SystemModule, t => t.IsCharType, typeArgs => Type.Char),
      new ValuetypeDecl("int", SystemModule, t => t.IsNumericBased(Type.NumericPersuasion.Int), typeArgs => Type.Int),
      new ValuetypeDecl("real", SystemModule, t => t.IsNumericBased(Type.NumericPersuasion.Real), typeArgs => Type.Real),
      new ValuetypeDecl("ORDINAL", SystemModule, t => t.IsBigOrdinalType, typeArgs => Type.BigOrdinal),
      new ValuetypeDecl("_bv", SystemModule, t => t.IsBitVectorType && !Options.Get(CommonOptionBag.TypeSystemRefresh),
        null), // "_bv" represents a family of classes, so no typeTester or type creator is supplied (it's used only in the legacy resolver)
      new ValuetypeDecl("set", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict },
        t => t.AsSetType is { Finite: true }, typeArgs => new SetType(true, typeArgs[0])),
      new ValuetypeDecl("iset", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Permissive },
        t => t.IsISetType, typeArgs => new SetType(false, typeArgs[0])),
      new ValuetypeDecl("seq", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict },
        t => t.AsSeqType != null, typeArgs => new SeqType(typeArgs[0])),
      new ValuetypeDecl("multiset", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>() { TypeParameter.TPVarianceSyntax.Covariant_Strict },
        t => t.AsMultiSetType != null, typeArgs => new MultiSetType(typeArgs[0])),
      new ValuetypeDecl("map", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>()
          { TypeParameter.TPVarianceSyntax.Covariant_Strict, TypeParameter.TPVarianceSyntax.Covariant_Strict },
        t => t.IsMapType, typeArgs => new MapType(true, typeArgs[0], typeArgs[1])),
      new ValuetypeDecl("imap", SystemModule,
        new List<TypeParameter.TPVarianceSyntax>()
          { TypeParameter.TPVarianceSyntax.Covariant_Permissive, TypeParameter.TPVarianceSyntax.Covariant_Strict },
        t => t.IsIMapType, typeArgs => new MapType(false, typeArgs[0], typeArgs[1]))
    };
    SystemModule.SourceDecls.AddRange(valuetypeDecls);
    // Resolution error handling relies on being able to get to the 0-tuple declaration
    TupleType(Token.NoToken, 0, true);

    // Populate the members of the basic types

    void AddMember(MemberDecl member, ValuetypeVariety valuetypeVariety) {
      var enclosingType = valuetypeDecls[(int)valuetypeVariety];
      member.EnclosingClass = enclosingType;
      member.AddVisibilityScope(SystemModule.VisibilityScope, false);
      enclosingType.Members.Add(member);
    }

    var floor = new SpecialField(SourceOrigin.NoToken, "Floor", SpecialField.ID.Floor, null, false, false, false, Type.Int, null);
    AddMember(floor, ValuetypeVariety.Real);

    var isLimit = new SpecialField(SourceOrigin.NoToken, "IsLimit", SpecialField.ID.IsLimit, null, false, false, false, Type.Bool, null);
    AddMember(isLimit, ValuetypeVariety.BigOrdinal);

    var isSucc = new SpecialField(SourceOrigin.NoToken, "IsSucc", SpecialField.ID.IsSucc, null, false, false, false, Type.Bool, null);
    AddMember(isSucc, ValuetypeVariety.BigOrdinal);

    var limitOffset = new SpecialField(SourceOrigin.NoToken, "Offset", SpecialField.ID.Offset, null, false, false, false, Type.Int, null);
    AddMember(limitOffset, ValuetypeVariety.BigOrdinal);
    ORDINAL_Offset = limitOffset;

    var isNat = new SpecialField(SourceOrigin.NoToken, "IsNat", SpecialField.ID.IsNat, null, false, false, false, Type.Bool, null);
    AddMember(isNat, ValuetypeVariety.BigOrdinal);

    // Add "Keys", "Values", and "Items" to map, imap
    foreach (var typeVariety in new[] { ValuetypeVariety.Map, ValuetypeVariety.IMap }) {
      var vtd = valuetypeDecls[(int)typeVariety];
      var isFinite = typeVariety == ValuetypeVariety.Map;

      var r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[0]));
      var keys = new SpecialField(SourceOrigin.NoToken, "Keys", SpecialField.ID.Keys, null, false, false, false, r, null);

      r = new SetType(isFinite, new UserDefinedType(vtd.TypeArgs[1]));
      var values = new SpecialField(SourceOrigin.NoToken, "Values", SpecialField.ID.Values, null, false, false, false, r, null);

      var gt = vtd.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      var dt = TupleType(Token.NoToken, 2, true);
      var tupleType = new UserDefinedType(Token.NoToken, dt.Name, dt, gt);
      r = new SetType(isFinite, tupleType);
      var items = new SpecialField(SourceOrigin.NoToken, "Items", SpecialField.ID.Items, null, false, false, false, r, null);

      foreach (var memb in new[] { keys, values, items }) {
        AddMember(memb, typeVariety);
      }
    }

    // The result type of the following bitvector methods is the type of the bitvector itself. However, we're representing all bitvector types as
    // a family of types rolled up in one ValuetypeDecl. Therefore, we use the special SelfType as the result type.
    AddRotateMember(valuetypeDecls[(int)ValuetypeVariety.Bitvector], "RotateLeft", new SelfType());
    AddRotateMember(valuetypeDecls[(int)ValuetypeVariety.Bitvector], "RotateRight", new SelfType());
  }

  public void AddRotateMember(ValuetypeDecl enclosingType, string name, Type resultType) {
    var formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null) };
    var rotateMember = new SpecialFunction(SourceOrigin.NoToken, name, SystemModule, false, false,
      new List<TypeParameter>(), formals, resultType,
      new List<AttributedExpression>(), new Specification<FrameExpression>(new List<FrameExpression>(), null), new List<AttributedExpression>(),
      new Specification<Expression>(new List<Expression>(), null), null, null, null);
    rotateMember.EnclosingClass = enclosingType;
    rotateMember.AddVisibilityScope(SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(rotateMember);
  }

  private Attributes DontCompile() {
    var flse = Expression.CreateBoolLiteral(Token.NoToken, false);
    return new Attributes("compile", new List<Expression>() { flse }, null);
  }

  public static Attributes AxiomAttribute(Attributes prev = null) {
    return new Attributes("axiom", new List<Expression>(), prev);
  }

  /// <summary>
  /// Ensures this instance contains the requested type
  /// </summary>
  public UserDefinedType ArrayType(int dims, Type arg, bool allowCreationOfNewClass) {
    Contract.Requires(1 <= dims);
    Contract.Requires(arg != null);
    var (result, mod) = ArrayType(Token.NoToken, dims, new List<Type> { arg }, allowCreationOfNewClass);
    mod(this);
    return result;
  }

  public static (UserDefinedType type, Action<SystemModuleManager> ModifyBuiltins) ArrayType(IOrigin tok, int dims, List<Type> optTypeArgs, bool allowCreationOfNewClass, bool useClassNameType = false) {
    Contract.Requires(tok != null);
    Contract.Requires(1 <= dims);
    Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // ideally, it is 1, but more will generate an error later, and null means it will be filled in automatically
    Contract.Ensures(Contract.Result<UserDefinedType>() != null);

    var arrayName = ArrayClassName(dims);
    if (useClassNameType) {
      arrayName += "?";
    }

    void ModifyBuiltins(SystemModuleManager builtIns) {
      if (!allowCreationOfNewClass || builtIns.arrayTypeDecls.ContainsKey(dims)) {
        return;
      }

      ArrayClassDecl arrayClass = new ArrayClassDecl(dims, builtIns.SystemModule, builtIns.DontCompile());
      for (int d = 0; d < dims; d++) {
        string name = dims == 1 ? "Length" : "Length" + d;
        Field len = new SpecialField(SourceOrigin.NoToken, name, SpecialField.ID.ArrayLength, dims == 1 ? null : (object)d, false, false, false, Type.Int, null);
        len.EnclosingClass = arrayClass; // resolve here
        arrayClass.Members.Add(len);
      }

      builtIns.arrayTypeDecls.Add(dims, arrayClass);
      builtIns.SystemModule.SourceDecls.Add(arrayClass);
      builtIns.CreateArrowTypeDecl(dims); // also create an arrow type with this arity, since it may be used in an initializing expression for the array
    }

    var udt = new UserDefinedType(tok, arrayName, optTypeArgs);
    return (udt, ModifyBuiltins);
  }

  public static string ArrayClassName(int dims) {
    Contract.Requires(1 <= dims);
    if (dims == 1) {
      return "array";
    } else {
      return "array" + dims;
    }
  }

  /// <summary>
  /// Idempotently add an arrow type with arity 'arity' to the system module, and along
  /// with this arrow type, the two built-in subset types based on the arrow type.
  /// </summary>
  public void CreateArrowTypeDecl(int arity) {
    Contract.Requires(0 <= arity);
    if (ArrowTypeDecls.ContainsKey(arity)) {
      // The work has already been done.
      return;
    }

    IOrigin tok = Token.NoToken;
    var tps = Util.Map(Enumerable.Range(0, arity + 1),
      x => x < arity
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TypeParameter.TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TypeParameter.TPVarianceSyntax.Covariant_Strict));
    var tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));

    Function CreateMember(string name, Type resultType, Function readsFunction = null) {
      var args = Util.Map(Enumerable.Range(0, arity), i => new Formal(tok, "x" + i, tys[i], true, false, null));
      var argExprs = args.ConvertAll(a =>
        (Expression)new IdentifierExpr(tok, a.Name) { Var = a, Type = a.Type });
      var readsIS = new FunctionCallExpr(tok, new Name("reads"), new ImplicitThisExpr(tok), tok, Token.NoToken, argExprs) {
        Type = ObjectSetType(),
      };
      var readsFrame = new List<FrameExpression> { new FrameExpression(tok, readsIS, null) };
      var function = new Function(SourceOrigin.NoToken, new Name(name), false, true, false,
        new List<TypeParameter>(), args, null, resultType,
        new List<AttributedExpression>(), new Specification<FrameExpression>(readsFrame, null), new List<AttributedExpression>(),
        new Specification<Expression>(new List<Expression>(), null),
        null, null, null, null, null);
      readsIS.Function = readsFunction ?? function; // just so we can really claim the member declarations are resolved
      readsIS.TypeApplication_AtEnclosingClass = tys; // ditto
      readsIS.TypeApplication_JustFunction = new List<Type>(); // ditto
      return function;
    }

    var reads = CreateMember("reads", ObjectSetType(), null);
    var req = CreateMember("requires", Type.Bool, reads);

    var arrowDecl = new ArrowTypeDecl(tps, req, reads, SystemModule, DontCompile());
    ArrowTypeDecls.Add(arity, arrowDecl);
    SystemModule.SourceDecls.Add(arrowDecl);

    // declaration of read-effect-free arrow-type, aka heap-independent arrow-type, aka partial-function arrow-type
    tps = Util.Map(Enumerable.Range(0, arity + 1),
      x => x < arity
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TypeParameter.TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TypeParameter.TPVarianceSyntax.Covariant_Strict));
    tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
    var id = new BoundVar(tok, "f", new ArrowType(tok, arrowDecl, tys));
    var partialArrow = new SubsetTypeDecl(SourceOrigin.NoToken, new Name(ArrowType.PartialArrowTypeName(arity)),
      new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
      id, ArrowSubtypeConstraint(tok, id, reads, tps, false), SubsetTypeDecl.WKind.Special, null, DontCompile());
    ((RedirectingTypeDecl)partialArrow).ConstraintIsCompilable = false;
    PartialArrowTypeDecls.Add(arity, partialArrow);
    SystemModule.SourceDecls.Add(partialArrow);

    // declaration of total arrow-type

    tps = Util.Map(Enumerable.Range(0, arity + 1),
      x => x < arity
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TypeParameter.TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TypeParameter.TPVarianceSyntax.Covariant_Strict));
    tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
    id = new BoundVar(tok, "f", new UserDefinedType(tok, partialArrow.Name, partialArrow, tys));
    var totalArrow = new SubsetTypeDecl(SourceOrigin.NoToken, new Name(ArrowType.TotalArrowTypeName(arity)),
      new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
      id, ArrowSubtypeConstraint(tok, id, req, tps, true), SubsetTypeDecl.WKind.Special, null, DontCompile());
    ((RedirectingTypeDecl)totalArrow).ConstraintIsCompilable = false;
    TotalArrowTypeDecls.Add(arity, totalArrow);
    SystemModule.SourceDecls.Add(totalArrow);
  }

  /// <summary>
  /// Returns an expression that is the constraint of:
  /// the built-in partial-arrow type (if "!total", in which case "member" is expected to denote the "reads" member), or
  /// the built-in total-arrow type (if "total", in which case "member" is expected to denote the "requires" member).
  /// The given "id" is expected to be already resolved.
  /// </summary>
  private Expression ArrowSubtypeConstraint(IOrigin tok, BoundVar id, Function member, List<TypeParameter> tps, bool total) {
    Contract.Requires(tok != null);
    Contract.Requires(id != null);
    Contract.Requires(member != null);
    Contract.Requires(tps != null && 1 <= tps.Count);
    var f = new IdentifierExpr(tok, id);
    // forall x0,x1,x2 :: f.reads(x0,x1,x2) == {}
    // OR
    // forall x0,x1,x2 :: f.requires(x0,x1,x2)
    var bvs = new List<BoundVar>();
    var args = new List<Expression>();
    var bounds = new List<BoundedPool>();
    for (int i = 0; i < tps.Count - 1; i++) {
      var bv = new BoundVar(tok, "x" + i, new UserDefinedType(tps[i]));
      bvs.Add(bv);
      args.Add(new IdentifierExpr(tok, bv));
      bounds.Add(new SpecialAllocIndependenceAllocatedBoundedPool());
    }
    Expression body = Expression.CreateResolvedCall(tok, f, member, args, new List<Type>(), this);
    body.Type = member.ResultType;  // resolve here
    if (!total) {
      Expression emptySet = new SetDisplayExpr(tok, true, new List<Expression>());
      emptySet.Type = member.ResultType;  // resolve here
      body = Expression.CreateEq(body, emptySet, member.ResultType);
    }
    if (tps.Count > 1) {
      body = new ForallExpr(tok, bvs, null, body, null) { Type = Type.Bool, Bounds = bounds };
    }
    return body;
  }

  Type GetTypeOfFunction(Function f, List<Type> typeArgumentsClass, List<Type> typeArgumentsMember) {
    Contract.Requires(f != null);
    Contract.Requires(f.EnclosingClass != null);
    Contract.Requires(typeArgumentsClass != null);
    Contract.Requires(typeArgumentsMember != null);
    Contract.Requires(typeArgumentsClass.Count == f.EnclosingClass.TypeArgs.Count);
    Contract.Requires(typeArgumentsMember.Count == f.TypeArgs.Count);

    var atd = ArrowTypeDecls[f.Ins.Count];

    var formals = Util.Concat(f.EnclosingClass.TypeArgs, f.TypeArgs);
    var actuals = Util.Concat(typeArgumentsClass, typeArgumentsMember);
    var typeMap = TypeParameter.SubstitutionMap(formals, actuals);
    return new ArrowType(f.Origin, atd, f.Ins.ConvertAll(arg => arg.Type.Subst(typeMap)), f.ResultType.Subst(typeMap));
  }

  public TupleTypeDecl TupleType(IOrigin tok, int dims, bool allowCreationOfNewType, List<bool> argumentGhostness = null) {
    Contract.Requires(tok != null);
    Contract.Requires(0 <= dims);
    Contract.Requires(argumentGhostness == null || argumentGhostness.Count == dims);
    Contract.Ensures(Contract.Result<TupleTypeDecl>() != null);

    argumentGhostness ??= new bool[dims].Select(_ => false).ToList();
    if (!tupleTypeDecls.TryGetValue(argumentGhostness, out var tt)) {
      Contract.Assume(allowCreationOfNewType);  // the parser should ensure that all needed tuple types exist by the time of resolution

      // A tuple type with ghost components is represented as the shorter tuple type with the ghost components erased, except
      // possibly when that shorter tuple type is a 1-tuple. Ordinarily, such a 1-tuple is optimized into its component, so
      // there's no reason to create it here; but if either the compiler doesn't support datatype wrapper erasure or if
      // the user has disabled this optimization, then we still create the 1-tuple here.
      var nonGhostDims = argumentGhostness.Count(x => !x);
      TupleTypeDecl nonGhostTupleTypeDecl = null;
      if (nonGhostDims != dims &&
          (nonGhostDims != 1 || !Options.Backend.SupportsDatatypeWrapperErasure || !Options.Get(CommonOptionBag.OptimizeErasableDatatypeWrapper))) {
        // make sure the corresponding non-ghost tuple type also exists
        nonGhostTupleTypeDecl = TupleType(tok, nonGhostDims, allowCreationOfNewType);
      }

      tt = new TupleTypeDecl(argumentGhostness, SystemModule, nonGhostTupleTypeDecl, null);
      if (tt.NonGhostDims > MaxNonGhostTupleSizeUsed) {
        MaxNonGhostTupleSizeToken = tok;
        MaxNonGhostTupleSizeUsed = tt.NonGhostDims;
      }

      tupleTypeDecls.Add(argumentGhostness, tt);
      SystemModule.SourceDecls.Add(tt);
    }
    return tt;
  }

  public static char IsGhostToChar(bool isGhost) {
    return isGhost ? 'G' : 'O';
  }

  public static bool IsGhostFromChar(char c) {
    Contract.Requires(c == 'G' || c == 'O');
    return c == 'G';
  }

  public static string ArgumentGhostnessToString(List<bool> argumentGhostness) {
    return argumentGhostness.Count + (!argumentGhostness.Contains(true)
      ? "" : String.Concat(argumentGhostness.Select(IsGhostToChar)));
  }

  public static IEnumerable<bool> ArgumentGhostnessFromString(string s, int count) {
    List<bool> argumentGhostness = new bool[count].ToList();
    if (System.Char.IsDigit(s[s.Length - 1])) {
      return argumentGhostness.Select(_ => false);
    } else {
      return argumentGhostness.Select((_, i) => IsGhostFromChar(s[s.Length - count + i]));
    }
  }

  public static string TupleTypeName(List<bool> argumentGhostness) {
    return "_tuple#" + ArgumentGhostnessToString(argumentGhostness);
  }

  public static bool IsTupleTypeName(string s) {
    Contract.Requires(s != null);
    return s.StartsWith("_tuple#");
  }
  public const string TupleTypeCtorNamePrefix = "_#Make";  // the printer wants this name prefix to be uniquely recognizable

  public static string TupleTypeCtorName(int dims) {
    Contract.Assert(0 <= dims);
    return TupleTypeCtorNamePrefix + dims;
  }

  public ValuetypeDecl AsValuetypeDecl(Type t) {
    Contract.Requires(t != null);
    foreach (var vtd in valuetypeDecls) {
      if (vtd.IsThisType(t)) {
        return vtd;
      }
    }
    return null;
  }

  public void ResolveValueTypeDecls(ProgramResolver programResolver) {
    var moduleResolver = new ModuleResolver(programResolver, programResolver.Options);
    moduleResolver.moduleInfo = systemNameInfo;
    foreach (var valueTypeDecl in valuetypeDecls) {
      foreach (var member in valueTypeDecl.Members) {
        if (member is Function function) {
          moduleResolver.ResolveFunctionSignature(function);
          CallGraphBuilder.VisitFunction(function, programResolver.Reporter);
        } else if (member is Method method) {
          moduleResolver.ResolveMethodSignature(method);
          CallGraphBuilder.VisitMethod(method, programResolver.Reporter);
        }
      }
    }
  }

  public void CheckHasAllTupleNonGhostDimsUpTo(int max) {
    var allNeededDims = Enumerable.Range(0, max + 1).ToHashSet();
    var allDeclaredDims = tupleTypeDecls.Keys
        .Select(argumentGhostness => argumentGhostness.Count(ghost => !ghost))
        .Distinct()
        .ToHashSet();
    if (!allDeclaredDims.SetEquals(allNeededDims)) {
      throw new ArgumentException(@$"Not all tuple types declared between 0 and {max}!
needed: {allNeededDims.Comma()}
declared: {allDeclaredDims.Comma()}");
    }
  }

  public void CheckHasAllArrayDimsUpTo(int max) {
    var allNeededDims = Enumerable.Range(1, max).ToHashSet();
    var allDeclaredDims = arrayTypeDecls.Keys.ToHashSet();
    if (!allDeclaredDims.SetEquals(allNeededDims)) {
      throw new ArgumentException(@$"Not all array types declared between 1 and {max}!
needed: {allNeededDims.Comma()}
declared: {allDeclaredDims.Comma()}");
    }
  }

  public void CheckHasAllArrowAritiesUpTo(int max) {
    var allNeededArities = Enumerable.Range(0, max + 1).ToHashSet();
    var allDeclaredArities = ArrowTypeDecls.Keys.ToHashSet();
    if (!allDeclaredArities.SetEquals(allNeededArities)) {
      throw new ArgumentException(@$"Not all arrow types declared between 0 and {max}
needed: {allNeededArities.Comma()}
declared: {allDeclaredArities.Comma()}");
    }
  }
}

enum ValuetypeVariety {
  Bool = 0,
  Char,
  Int,
  Real,
  BigOrdinal,
  Bitvector,
  Set,
  ISet,
  Seq,
  Multiset,
  Map,
  IMap,
  None
} // note, these are ordered, so they can be used as indices into valuetypeDecls
