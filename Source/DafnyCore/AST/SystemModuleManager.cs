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
  public readonly ISet<int> FloatWidths = new HashSet<int>();
  [FilledInDuringResolution] public SpecialField ORDINAL_Offset;  // used by the translator

  public readonly TypeSynonymDecl StringDecl;
  public readonly SubsetTypeDecl NatDecl;
  public UserDefinedType Nat() { return new UserDefinedType(Token.NoToken, "nat", NatDecl, []); }
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
    SystemModule = new(SourceOrigin.NoToken, new Name("_System"), [],
      ModuleKindEnum.Concrete, false, null, null, null);
    this.Options = options;
    SystemModule.Height = -1;  // the system module doesn't get a height assigned later, so we set it here to something below everything else
    // create type synonym 'string'
    StringDecl = new ConcreteTypeSynonymDecl(SourceOrigin.NoToken, new Name("string"),
      new TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
      [], SystemModule, new SeqType(new CharType()), null);
    SystemModule.SourceDecls.Add(StringDecl);
    // create subset type 'nat'
    var bvNat = new BoundVar(Token.NoToken, "x", Type.Int);
    var natConstraint = Expression.CreateAtMost(Expression.CreateIntLiteral(Token.NoToken, 0), Expression.CreateIdentExpr(bvNat));
    var ax = AxiomAttribute();
    NatDecl = new SubsetTypeDecl(SourceOrigin.NoToken, new Name("nat"),
      new TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, Type.AutoInitInfo.CompilableValue, false),
      [], SystemModule, bvNat, natConstraint, SubsetTypeDecl.WKind.CompiledZero, null, ax);
    ((RedirectingTypeDecl)NatDecl).ConstraintIsCompilable = true;
    SystemModule.SourceDecls.Add(NatDecl);
    // create trait 'object'
    ObjectDecl = new TraitDecl(SourceOrigin.NoToken, new Name("object"), SystemModule, [], [], DontCompile(), false, []);
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
    // 2-argument arrow types created lazily for fp64.Equal

    valuetypeDecls = [
      new ValuetypeDecl("bool", SystemModule, t => t.IsBoolType, typeArgs => Type.Bool),
      new ValuetypeDecl("char", SystemModule, t => t.IsCharType, typeArgs => Type.Char),
      new ValuetypeDecl("int", SystemModule, t => t.IsNumericBased(Type.NumericPersuasion.Int), _ => Type.Int),
      new ValuetypeDecl("real", SystemModule, t => t.IsRealType, _ => Type.Real),
      new ValuetypeDecl("fp32", SystemModule, t => t.IsFp32Type, _ => Type.Fp32),
      new ValuetypeDecl("fp64", SystemModule, t => t.IsFp64Type, _ => Type.Fp64),
      new ValuetypeDecl("ORDINAL", SystemModule, t => t.IsBigOrdinalType, typeArgs => Type.BigOrdinal),
      new ValuetypeDecl("_bv", SystemModule, t => t.IsBitVectorType && !Options.Get(CommonOptionBag.TypeSystemRefresh),
        null), // "_bv" represents a family of classes, so no typeTester or type creator is supplied (it's used only in the legacy resolver)
      new ValuetypeDecl("set", SystemModule,
        [TPVarianceSyntax.Covariant_Strict],
        t => t.AsSetType is { Finite: true }, typeArgs => new SetType(true, typeArgs[0])),
      new ValuetypeDecl("iset", SystemModule,
        [TPVarianceSyntax.Covariant_Permissive],
        t => t.IsISetType, typeArgs => new SetType(false, typeArgs[0])),
      new ValuetypeDecl("seq", SystemModule,
        [TPVarianceSyntax.Covariant_Strict],
        t => t.AsSeqType != null, typeArgs => new SeqType(typeArgs[0])),
      new ValuetypeDecl("multiset", SystemModule,
        [TPVarianceSyntax.Covariant_Strict],
        t => t.AsMultiSetType != null, typeArgs => new MultiSetType(typeArgs[0])),
      new ValuetypeDecl("map", SystemModule,
        [TPVarianceSyntax.Covariant_Strict, TPVarianceSyntax.Covariant_Strict],
        t => t.IsMapType, typeArgs => new MapType(true, typeArgs[0], typeArgs[1])),
      new ValuetypeDecl("imap", SystemModule,
        [TPVarianceSyntax.Covariant_Permissive, TPVarianceSyntax.Covariant_Strict],
        t => t.IsIMapType, typeArgs => new MapType(false, typeArgs[0], typeArgs[1]))
    ];

    // Add all valuetype decls to system module (except fp32 and fp64, which are added lazily on first use)
    SystemModule.SourceDecls.AddRange(valuetypeDecls.Where((_, i) =>
      i != (int)ValuetypeVariety.Fp32 && i != (int)ValuetypeVariety.Fp64));

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

    // Note: fp32 and fp64 members are initialized lazily on first use

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

    // Create 2-argument arrow types early to avoid circular dependency
    CreateArrowTypeDecl(2);
  }

  public void AddRotateMember(ValuetypeDecl enclosingType, string name, Type resultType) {
    var formals = new List<Formal> { new Formal(Token.NoToken, "w", Type.Nat(), true, false, null) };
    var rotateMember = new SpecialFunction(SourceOrigin.NoToken, name, SystemModule, false, false,
      [], formals, resultType,
      [], new Specification<FrameExpression>([], null), [],
      new Specification<Expression>([], null), null, null, null);
    rotateMember.EnclosingClass = enclosingType;
    rotateMember.AddVisibilityScope(SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(rotateMember);
  }

  public void AddFloatSpecialValues(ValuetypeDecl enclosingType, Type floatType) {
    AddFloatConstant(enclosingType, "NaN", SpecialField.ID.NaN, floatType);
    AddFloatConstant(enclosingType, "PositiveInfinity", SpecialField.ID.PositiveInfinity, floatType);
    AddFloatConstant(enclosingType, "NegativeInfinity", SpecialField.ID.NegativeInfinity, floatType);
    AddFloatConstant(enclosingType, "Pi", SpecialField.ID.Pi, floatType);
    AddFloatConstant(enclosingType, "E", SpecialField.ID.E, floatType);
    AddFloatConstant(enclosingType, "MaxValue", SpecialField.ID.MaxValue, floatType);
    AddFloatConstant(enclosingType, "MinValue", SpecialField.ID.MinValue, floatType);
    AddFloatConstant(enclosingType, "MinNormal", SpecialField.ID.MinNormal, floatType);
    AddFloatConstant(enclosingType, "MinSubnormal", SpecialField.ID.MinSubnormal, floatType);
    AddFloatConstant(enclosingType, "Epsilon", SpecialField.ID.Epsilon, floatType);
  }

  private void AddFloatStaticMethods(ValuetypeDecl enclosingType, Type floatType) {
    AddFloatStaticFunction(enclosingType, "Equal", [("x", floatType), ("y", floatType)], Type.Bool);
    // Unchecked arithmetic methods - no NaN or invalid operation preconditions
    // These allow testing IEEE 754 edge cases (e.g., inf/inf = NaN, nan + x = NaN)
    AddFloatStaticFunction(enclosingType, "Add", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Sub", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Mul", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Div", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Neg", [("x", floatType)], floatType);
    // Unchecked comparison methods - no NaN preconditions (always return false for NaN)
    AddFloatStaticFunction(enclosingType, "Less", [("x", floatType), ("y", floatType)], Type.Bool);
    AddFloatStaticFunction(enclosingType, "LessOrEqual", [("x", floatType), ("y", floatType)], Type.Bool);
    AddFloatStaticFunction(enclosingType, "Greater", [("x", floatType), ("y", floatType)], Type.Bool);
    AddFloatStaticFunction(enclosingType, "GreaterOrEqual", [("x", floatType), ("y", floatType)], Type.Bool);
    AddFloatMathematicalFunctions(enclosingType, floatType);
    AddFloatInexactConversionMethods(enclosingType, floatType);
  }

  private void AddFloatMathematicalFunctions(ValuetypeDecl enclosingType, Type floatType) {
    CreateArrowTypeDecl(2);
    AddFloatStaticFunction(enclosingType, "Min", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Max", [("x", floatType), ("y", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Abs", [("x", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Floor", [("x", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Ceiling", [("x", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Round", [("x", floatType)], floatType);
    AddFloatStaticFunction(enclosingType, "Sqrt", [("x", floatType)], floatType);
  }

  private void AddFloatInexactConversionMethods(ValuetypeDecl enclosingType, Type floatType) {
    AddFloatStaticFunction(enclosingType, "FromReal", [("r", Type.Real)], floatType);
    AddFloatStaticFunction(enclosingType, "ToInt", [("f", floatType)], Type.Int);

    // Cross-float conversions
    if (floatType is Fp32Type) {
      AddFloatStaticFunction(enclosingType, "FromFp64", [("f", new Fp64Type())], floatType);
    } else if (floatType is Fp64Type) {
      AddFloatStaticFunction(enclosingType, "FromFp32", [("f", new Fp32Type())], floatType);
    }
  }

  private void AddFloatStaticFunction(ValuetypeDecl enclosingType, string name, (string, Type)[] parameters, Type returnType) {
    var formals = parameters.Select(p => new Formal(Token.NoToken, p.Item1, p.Item2, true, false, null)).ToList();
    var method = new SpecialFunction(SourceOrigin.NoToken, name, SystemModule, true, false,
      [], formals, returnType,
      [], new Specification<FrameExpression>([], null), [],
      new Specification<Expression>([], null), null, null, null) {
      EnclosingClass = enclosingType
    };
    method.AddVisibilityScope(SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(method);
  }

  private Attributes DontCompile() {
    var flse = Expression.CreateBoolLiteral(Token.NoToken, false);
    return new Attributes("compile", [flse], null);
  }

  public static Attributes AxiomAttribute(Attributes prev = null) {
    return new Attributes("axiom", [], prev);
  }

  /// <summary>
  /// Ensures this instance contains the requested type
  /// </summary>
  public UserDefinedType ArrayType(int dims, Type arg, bool allowCreationOfNewClass) {
    Contract.Requires(1 <= dims);
    Contract.Requires(arg != null);
    var (result, mod) = ArrayType(Token.NoToken, dims, [arg], allowCreationOfNewClass);
    mod(this);
    return result;
  }

  // Initialize fp64 type and add to system module on first reference
  public void EnsureFloatTypesInitialized(ProgramResolver programResolver) {
    EnsureFloatTypesInitialized();

    var fp32TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp32];

    // Add fp32 to system module if not already there
    if (!SystemModule.SourceDecls.Contains(fp32TypeDecl)) {
      SystemModule.SourceDecls.Add(fp32TypeDecl);
    }

    // Register fp32 in systemNameInfo.TopLevels for name resolution
    systemNameInfo.TopLevels.TryAdd("fp32", fp32TypeDecl);

    // Add fp32 members to classMembers dictionary
    var memberDictionary = fp32TypeDecl.Members
      .GroupBy(member => member.Name)
      .ToDictionary(g => g.Key, g => g.First());
    programResolver.AddSystemClass(fp32TypeDecl, memberDictionary);
  }

  private void EnsureFloatTypesInitialized() {
    var fp32TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp32];

    // Check if already initialized by looking for "Min" member
    if (fp32TypeDecl.Members.Any(m => m.Name == "Min")) {
      return;
    }

    // Initialize both fp32 and fp64 members together (they share implementation)
    InitializeFp32Members();
    InitializeFp64Members();

    // Add both to system module
    if (!SystemModule.SourceDecls.Contains(fp32TypeDecl)) {
      SystemModule.SourceDecls.Add(fp32TypeDecl);
    }
    var fp64TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp64];
    if (!SystemModule.SourceDecls.Contains(fp64TypeDecl)) {
      SystemModule.SourceDecls.Add(fp64TypeDecl);
    }
  }

  public void EnsureFp64TypeInitialized(ProgramResolver programResolver) {
    EnsureFp64TypeInitialized();

    var fp64TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp64];

    // Register fp64 in systemNameInfo.TopLevels for name resolution
    systemNameInfo.TopLevels.TryAdd("fp64", fp64TypeDecl);

    // Add fp64 members to classMembers dictionary
    var memberDictionary = fp64TypeDecl.Members
      .GroupBy(member => member.Name)
      .ToDictionary(g => g.Key, g => g.First());
    programResolver.AddSystemClass(fp64TypeDecl, memberDictionary);
  }

  // Overload for backward compatibility (called from AsValuetypeDecl)
  private void EnsureFp64TypeInitialized() {
    var fp64TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp64];

    // Check if already initialized by looking for "Min" member
    if (fp64TypeDecl.Members.Any(m => m.Name == "Min")) {
      return;
    }

    // Initialize fp32 members
    InitializeFp32Members();

    // Initialize fp64 members
    InitializeFp64Members();

    // Add fp32 to system module
    var fp32TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp32];
    if (!SystemModule.SourceDecls.Contains(fp32TypeDecl)) {
      SystemModule.SourceDecls.Add(fp32TypeDecl);
    }

    // Add fp64 to system module
    if (!SystemModule.SourceDecls.Contains(fp64TypeDecl)) {
      SystemModule.SourceDecls.Add(fp64TypeDecl);
    }
  }

  // Helper method to add a member to a valuetype with proper initialization
  private void AddMemberToValuetype(MemberDecl member, ValuetypeVariety valuetypeVariety) {
    var enclosingType = valuetypeDecls[(int)valuetypeVariety];
    member.EnclosingClass = enclosingType;
    member.AddVisibilityScope(SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(member);
  }

  private void AddFloatInstanceMembers(ValuetypeVariety variety) {
    AddFloatInstancePredicate(variety, "IsFinite", SpecialField.ID.IsFinite);
    AddFloatInstancePredicate(variety, "IsNaN", SpecialField.ID.IsNaN);
    AddFloatInstancePredicate(variety, "IsInfinite", SpecialField.ID.IsInfinite);
    AddFloatInstancePredicate(variety, "IsNormal", SpecialField.ID.IsNormal);
    AddFloatInstancePredicate(variety, "IsSubnormal", SpecialField.ID.IsSubnormal);
    AddFloatInstancePredicate(variety, "IsZero", SpecialField.ID.IsZero);
    AddFloatInstancePredicate(variety, "IsNegative", SpecialField.ID.IsNegative);
    AddFloatInstancePredicate(variety, "IsPositive", SpecialField.ID.IsPositive);
  }

  private void AddFloatInstancePredicate(ValuetypeVariety variety, string name, SpecialField.ID id) {
    var field = new SpecialField(SourceOrigin.NoToken, name, id, null,
      false, false, false, Type.Bool, null);
    AddMemberToValuetype(field, variety);
  }

  private void InitializeFp32Members() {
    var fp32TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp32];
    var fp32Type = new Fp32Type();
    AddFloatInstanceMembers(ValuetypeVariety.Fp32);
    AddFloatSpecialValues(fp32TypeDecl, fp32Type);
    AddFloatStaticMethods(fp32TypeDecl, fp32Type);
  }

  private void InitializeFp64Members() {
    var fp64TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp64];
    var fp64Type = new Fp64Type();
    AddFloatInstanceMembers(ValuetypeVariety.Fp64);
    AddFloatSpecialValues(fp64TypeDecl, fp64Type);
    AddFloatStaticMethods(fp64TypeDecl, fp64Type);
  }

  private void AddFp64SpecialValues() {
    var fp64Type = new Fp64Type();
    var fp64TypeDecl = valuetypeDecls[(int)ValuetypeVariety.Fp64];

    AddFloatConstant(fp64TypeDecl, "NaN", SpecialField.ID.NaN, fp64Type);
    AddFloatConstant(fp64TypeDecl, "PositiveInfinity", SpecialField.ID.PositiveInfinity, fp64Type);
    AddFloatConstant(fp64TypeDecl, "NegativeInfinity", SpecialField.ID.NegativeInfinity, fp64Type);
    AddFloatConstant(fp64TypeDecl, "MaxValue", SpecialField.ID.MaxValue, fp64Type);
    AddFloatConstant(fp64TypeDecl, "MinValue", SpecialField.ID.MinValue, fp64Type);
    AddFloatConstant(fp64TypeDecl, "Epsilon", SpecialField.ID.Epsilon, fp64Type);
    AddFloatConstant(fp64TypeDecl, "MinNormal", SpecialField.ID.MinNormal, fp64Type);
    AddFloatConstant(fp64TypeDecl, "MinSubnormal", SpecialField.ID.MinSubnormal, fp64Type);
    AddFloatConstant(fp64TypeDecl, "Pi", SpecialField.ID.Pi, fp64Type);
    AddFloatConstant(fp64TypeDecl, "E", SpecialField.ID.E, fp64Type);

    AddFloatStaticFunction(fp64TypeDecl, "Equal", [("a", fp64Type), ("b", fp64Type)], Type.Bool);
    AddFloatStaticFunction(fp64TypeDecl, "Abs", [("x", fp64Type)], fp64Type);
    AddFloatStaticFunction(fp64TypeDecl, "Sqrt", [("x", fp64Type)], fp64Type);
  }

  private void AddFloatConstant(ValuetypeDecl enclosingType, string name, SpecialField.ID id, Type floatType) {
    var constant = new StaticSpecialField(SourceOrigin.NoToken, name, id, null,
      false, false, false, floatType, null) {
      EnclosingClass = enclosingType
    };
    constant.AddVisibilityScope(SystemModule.VisibilityScope, false);
    enclosingType.Members.Add(constant);
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
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TPVarianceSyntax.Covariant_Strict));
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
        [], args, null, resultType,
        [], new Specification<FrameExpression>(readsFrame, null), [],
        new Specification<Expression>([], null),
        null, null, null, null, null);
      readsIS.Function = readsFunction ?? function; // just so we can really claim the member declarations are resolved
      readsIS.TypeApplication_AtEnclosingClass = tys; // ditto
      readsIS.TypeApplication_JustFunction = []; // ditto
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
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TPVarianceSyntax.Covariant_Strict));
    tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
    var id = new BoundVar(tok, "f", new ArrowType(tok, arrowDecl, tys));
    var partialArrow = new SubsetTypeDecl(SourceOrigin.NoToken, new Name(ArrowType.PartialArrowTypeName(arity)),
      TypeParameterCharacteristics.Default(), tps, SystemModule,
      id, ArrowSubtypeConstraint(tok, id, reads, tps, false), SubsetTypeDecl.WKind.Special, null, DontCompile());
    ((RedirectingTypeDecl)partialArrow).ConstraintIsCompilable = false;
    PartialArrowTypeDecls.Add(arity, partialArrow);
    SystemModule.SourceDecls.Add(partialArrow);

    // declaration of total arrow-type

    tps = Util.Map(Enumerable.Range(0, arity + 1),
      x => x < arity
        ? new TypeParameter(SourceOrigin.NoToken, new Name("T" + x), TPVarianceSyntax.Contravariance)
        : new TypeParameter(SourceOrigin.NoToken, new Name("R"), TPVarianceSyntax.Covariant_Strict));
    tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
    id = new BoundVar(tok, "f", new UserDefinedType(tok, partialArrow.Name, partialArrow, tys));
    var totalArrow = new SubsetTypeDecl(SourceOrigin.NoToken, new Name(ArrowType.TotalArrowTypeName(arity)),
      TypeParameterCharacteristics.Default(), tps, SystemModule,
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
    f.Type = id.Type;
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
    Expression body = Expression.CreateResolvedCall(tok, f, member, args, [], this);
    body.Type = member.ResultType;  // resolve here
    if (!total) {
      Expression emptySet = new SetDisplayExpr(tok, true, []);
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
    if (t.IsFp32Type) {
      EnsureFloatTypesInitialized();
    }
    if (t.IsFp64Type) {
      EnsureFp64TypeInitialized();
    }

    return valuetypeDecls.FirstOrDefault(vtd => vtd.IsThisType(t));
  }

  public void ResolveValueTypeDecls(ProgramResolver programResolver) {
    var moduleResolver = new ModuleResolver(programResolver, programResolver.Options);
    moduleResolver.moduleInfo = systemNameInfo;
    foreach (var valueTypeDecl in valuetypeDecls) {
      foreach (var member in valueTypeDecl.Members) {
        if (member is Function function) {
          moduleResolver.ResolveFunctionSignature(function);
          CallGraphBuilder.VisitFunction(function, programResolver.Reporter);
        } else if (member is MethodOrConstructor method) {
          moduleResolver.ResolveMethodSignature(method);
          CallGraphBuilder.VisitMethod(method, programResolver.Reporter);
        }
      }

      // Add ValuetypeDecl members to the classMembers dictionary for member resolution
      var memberDictionary = valueTypeDecl.Members.ToDictionary(member => member.Name, member => member);
      programResolver.AddSystemClass(valueTypeDecl, memberDictionary);
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

// Custom static special field class for fp64 constants
public class StaticSpecialField : SpecialField {
  public override bool HasStaticKeyword => true;

  public StaticSpecialField(IOrigin origin, string name, ID specialId, object idParam,
    bool isGhost, bool isMutable, bool isUserMutable, Type explicitType, Attributes attributes)
    : base(origin, name, specialId, idParam, isGhost, isMutable, isUserMutable, explicitType, attributes) {
  }
}

enum ValuetypeVariety {
  Bool = 0,
  Char,
  Int,
  Real,
  Fp32,
  Fp64,
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
