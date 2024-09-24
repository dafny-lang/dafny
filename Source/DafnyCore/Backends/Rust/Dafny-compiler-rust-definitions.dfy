
module {:extern "Defs"} DafnyToRustCompilerDefinitions {
  import FactorPathsOptimization
  import ExpressionOptimization

  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  import opened DafnyCompilerRustUtils

  const IND := R.IND
  type Type = DAST.Type
  type Formal = DAST.Formal

  // List taken from https://doc.rust-lang.org/book/appendix-01-keywords.html
  const reserved_rust := {
    "as","async","await","break","const","continue",
    "crate","dyn","else","enum","extern","false","fn","for","if","impl",
    "in","let","loop","match","mod","move","mut","pub","ref","return",
    "static","struct","super","trait","true","type","union",
    "unsafe","use","where","while","Keywords","The","abstract","become",
    "box","do","final","macro","override","priv","try","typeof","unsized",
    "virtual","yield"}

  const reserved_vars := { "None", "hash" }

  const reserved_rust_need_prefix := {"u8", "u16", "u32", "u64", "u128","i8", "i16", "i32", "i64", "i128"}

  const AttributeOwned := Attribute("owned", [])

  predicate is_tuple_numeric(i: string) {
    |i| >= 2 && i[0] == '_' &&
    i[1] in "0123456789" &&
    (|i| == 2 ||
     (|i| == 3 && i[2] in "0123456789"))
  }

  predicate has_special(i: string) {
    if |i| == 0 then false
    else if i[0] == '.' then true
    else if i[0] == '#' then true // otherwise "escapeName("r#") becomes "r#""
    else if i[0] == '_' then
      if 2 <= |i| then
        if i[1] != '_' then true
        else has_special(i[2..])
      else
        true
    else
      has_special(i[1..])
  }

  function idiomatic_rust(i: string): string
    requires !has_special(i)
  {
    if |i| == 0 then ""
    else if i[0] == '_' then
      assert 2 <= |i| && i[1] == '_';
      "_" + idiomatic_rust(i[2..])
    else
      [i[0]] + idiomatic_rust(i[1..])
  }

  function replaceDots(i: string): string {
    if |i| == 0 then
      ""
    else if i[0] == '.' then
      "_d" + replaceDots(i[1..])
    else
      [i[0]] + replaceDots(i[1..])
  }

  predicate is_tuple_builder(i: string)
    // A tuple builder identifier looks like ___hMake0 to ___hMake99
  {
    && |i| >= 9
    && i[..8] == "___hMake"
    && i[8] in "0123456789"
    && (|i| == 9 || (|i| == 10 && i[9] in "0123456789"))
  }

  function better_tuple_builder_name(i: string): string
    requires is_tuple_builder(i)
  {
    "_T" + i[8..]
  }

  predicate is_dafny_generated_id(i: string) {
    && |i| > 0 && i[0] == '_' && !has_special(i[1..])
    && (|i| >= 2 ==> i[1] != 'T') // To avoid conflict with tuple builders _T<digits>
  }

  predicate is_idiomatic_rust_id(i: string) {
    0 < |i| && !has_special(i) && i !in reserved_rust && i !in reserved_rust_need_prefix
  }
  // To be used when escaping class names, datatype constructors, externs, paths, function/method names, etc.
  // Datatype destructors, variable names and field names all use escapeVar()
  function escapeName(n: Name): string {
    escapeIdent(n.dafny_name)
  }

  function escapeIdent(i: string): string {
    if is_tuple_numeric(i) then
      i
    else if is_tuple_builder(i) then
      better_tuple_builder_name(i)
    else if i == "self" || i == "Self" then
      "r#_" + i
    else if i in reserved_rust then
      "r#" + i
    else if is_idiomatic_rust_id(i) then
      idiomatic_rust(i)
    else if is_dafny_generated_id(i) then
      i // Dafny-generated identifiers like "_module", cannot be written in Dafny itself
    else
      var r := replaceDots(i);
      "r#_" + r
  }

  // To be used when escaping variables
  function escapeVar(f: VarName): string {
    var r := f.dafny_name;
    if r in reserved_vars then
      "_" + r
    else
      escapeIdent(f.dafny_name)
  }

  datatype Ownership =
    | OwnershipOwned
    | OwnershipOwnedBox
    | OwnershipBorrowed
    | OwnershipBorrowedMut
    | OwnershipAutoBorrowed

  // types stores the Rust type per Rust name.
  // fn Test<T>(i: T) is map["i" := R.RawType("T")]
  // fn Test(i: &T) is map["i" := R.Borrowed(...)]
  // fn Test(i: &mut T) is map["i" := R.BorrowedMut(...)]
  datatype Environment = Environment(
    names: seq<string>,                 // All variable names, after escape, in Rust
    types: map<string, R.Type>
  ) {
    function ToOwned(): Environment {
      this.(types :=
      map k <- types :: k := types[k].ToOwned())
    }
    static function Empty(): Environment {
      Environment([], map[])
    }
    opaque predicate CanReadWithoutClone(name: string) {
      name in types && types[name].CanReadWithoutClone()
    }
    opaque predicate HasCloneSemantics(name: string) {
      !CanReadWithoutClone(name)
    }
    function GetType(name: string): Option<R.Type> {
      if name in types then Some(types[name]) else None
    }
    predicate IsBorrowed(name: string) {
      name in types && types[name].Borrowed?
    }
    predicate IsBorrowedMut(name: string) {
      name in types && types[name].BorrowedMut?
    }
    function AddAssigned(name: string, tpe: R.Type): Environment
      // If we know for sure the type of name extends the Copy trait
    {
      Environment(names + [name], types[name := tpe])
    }
    function merge(other: Environment): Environment
    {
      Environment(
        names + other.names,
        types + other.types
      )
    }
    function RemoveAssigned(name: string): Environment
      requires name in names
    {
      var indexInEnv := Std.Collections.Seq.IndexOf(names, name);
      Environment(
        names[0..indexInEnv] + names[indexInEnv + 1..],
        types - {name}
      )
    }
  }

  const ASSIGNED_PREFIX := "_set"

  function AddAssignedPrefix(rustName: string): string {
    if |rustName| >= 2 && rustName[0..2] == "r#" then
      ASSIGNED_PREFIX + rustName[2..]
    else
      ASSIGNED_PREFIX + "_" + rustName
  }

  datatype PointerType = Raw | RcMut
  datatype CharType = UTF16 | UTF32
  datatype RootType = RootCrate | RootPath(moduleName: string)

  datatype GenTypeContext =
    GenTypeContext(forTraitParents: bool)
  {
    static function ForTraitParents(): GenTypeContext {
      GenTypeContext(true)
    }
    static function default(): GenTypeContext {
      GenTypeContext(false)
    }
  }

  // Returns the first trait type that has dafnyName as a proper method
  // Resolution guarantees it's the only one.
  function TraitTypeContainingMethodAux(rs: seq<Type>, dafnyName: string): Option<ResolvedType> {
    if |rs| == 0 then None
    else
      var res := match rs[0] {
        case UserDefined(resolvedType) =>
          TraitTypeContainingMethod(resolvedType, dafnyName)
        case _ =>
          None
      };
      match res {
        case Some(_) => res
        case None => TraitTypeContainingMethodAux(rs[1..], dafnyName)
      }
  }

  function TraitTypeContainingMethod(r: ResolvedType, dafnyName: string): Option<ResolvedType> {
    var ResolvedType(
        path,
        typeArgs,
        kind,
        attributes,
        properMethods,
        extendedTypes) := r;
    if Name(dafnyName) in properMethods then
      Some(r)
    else
      TraitTypeContainingMethodAux(extendedTypes, dafnyName)
  }

  /* Which variable is representing the current "this" context and how it's represented
  if NoSelf? then // static context
  else if IsSelf() then For object: &Self or &mut Self, for datatypes &Rc<Self>
  else // For objects: &Object<Self>, for datatypes &Rc<Self>
  */
  datatype SelfInfo =
    | NoSelf
    | ThisTyped(rSelfName: string, dafnyType: Type)
  {
    predicate IsSelf() {
      ThisTyped? && rSelfName == "self"
    }
  }

  datatype ExternAttribute =
    | NoExtern()
    | SimpleExtern(overrideName: string)
    | AdvancedExtern(enclosingModule: seq<string>, overrideName: string)
    | UnsupportedExtern(reason: string)

  opaque function OptExtern(attr: Attribute, dafnyName: Name): Option<ExternAttribute> {
    if attr.name == "extern" then
      Some(
        if |attr.args| == 0 then SimpleExtern(escapeName(dafnyName)) else
        if |attr.args| == 1 then SimpleExtern(attr.args[0]) else
        if |attr.args| == 2 then AdvancedExtern(SplitRustPathElement(ReplaceDotByDoubleColon(attr.args[0])), attr.args[1]) else
        UnsupportedExtern("{:extern} supports only 0, 1 or 2 attributes, got " + Std.Strings.OfNat(|attr.args|))
      )
    else
      None
  }

  // Dots are not valid identifier characters in Rust, so we replace them by double colons.
  // We don't perform this replacement after any space occurs in an extern string
  // because normally spaces don't occur in paths, so any use of space indicates something different.
  function ReplaceDotByDoubleColon(s: string): string {
    if |s| == 0 then "" else
    if s[0] == ' ' then s else
    (if s[0] == '.' then "::" else [s[0]]) + ReplaceDotByDoubleColon(s[1..])
  }

  function SplitRustPathElement(s: string, result: seq<string> := [], acc: string := ""): seq<string> {
    if |s| == 0 then
      if acc == "" then result else result + [acc]
    else
    if |s| >= 2 && s[0..2] =="::" then
      SplitRustPathElement(s[2..], result + [acc], "")
    else
      SplitRustPathElement(s[1..], result, acc + [s[0]])
  }

  function ExtractExtern(attributes: seq<Attribute>, dafnyName: Name): (res: ExternAttribute) {
    if |attributes| == 0 then NoExtern()
    else
      var attr := OptExtern(attributes[0], dafnyName);
      match attr
      case Some(n) => n
      case None =>
        ExtractExtern(attributes[1..], dafnyName)
  } by method {
    for i := 0 to |attributes|
      invariant ExtractExtern(attributes, dafnyName) == ExtractExtern(attributes[i..], dafnyName)
    {
      var attr := OptExtern(attributes[i], dafnyName);
      assert attributes[i] == attributes[i..][0];
      match attr {
        case Some(n) =>
          res := n;
          return;
        case _ =>
      }
      assert attributes[i..][1..] == attributes[i+1..];
    }
    res := NoExtern();
  }

  function ExtractExternMod(mod: Module): ExternAttribute {
    ExtractExtern(mod.attributes, mod.name)
  }

  const TailRecursionPrefix := "_r"

  const DAFNY_EXTERN_MODULE := "_dafny_externs"

  function ContainingPathToRust(containingPath: seq<Ident>): seq<string> {
    Std.Collections.Seq.Map((i: Ident) => escapeName(i.id), containingPath)
  }

  const OpTable: map<BinOp, string> :=
    map[
      Mod() := "%",
      And() := "&&",
      Or() := "||",
      Div() := "/",
      Lt() := "<",
      LtChar() := "<",
      Plus() := "+",
      Minus() := "-",
      Times() := "*",
      BitwiseAnd() := "&",
      BitwiseOr() := "|",
      BitwiseXor() := "^",
      BitwiseShiftRight() := ">>",
      BitwiseShiftLeft() := "<<"
    ]

  function NewtypeRangeToRustType(range: NewtypeRange)
    : Option<R.Type> {
    match range {
      case NoRange() => None
      case U8() => Some(R.Type.U8)
      case U16() => Some(R.Type.U16)
      case U32() => Some(R.Type.U32)
      case U64() => Some(R.Type.U64)
      case U128() => Some(R.Type.U128)
      case I8() => Some(R.Type.I8)
      case I16() => Some(R.Type.I16)
      case I32() => Some(R.Type.I32)
      case I64() => Some(R.Type.I64)
      case I128() => Some(R.Type.I128)
      case USIZE() => Some(R.Type.USIZE)
      case _ => None
    }
  }

  predicate OwnershipGuarantee(expectedOwnership: Ownership, resultingOwnership: Ownership) {
    && (expectedOwnership != OwnershipAutoBorrowed ==>
          resultingOwnership == expectedOwnership)
    && resultingOwnership != OwnershipAutoBorrowed // We know what's going on
  }

  predicate BecomesLeftCallsRight(op: BinOp) {
    match op {
      case SetMerge()
        | SetSubtraction()
        | SetIntersection()
        | SetDisjoint()
        | MapMerge()
        | MapSubtraction()
        | MultisetMerge()
        | MultisetSubtraction()
        | MultisetIntersection()
        | MultisetDisjoint()
        | Concat()
        => true
      case _ => false
    }
  }

  predicate BecomesRightCallsLeft(op: BinOp) {
    match op {
      case In() => true
      case _ => false
    }
  }

  lemma BecomesExclusive(op: BinOp)
    ensures BecomesCallLeftRight(op) ==> !BecomesRightCallsLeft(op) && !BecomesLeftCallsRight(op)
    ensures BecomesRightCallsLeft(op) ==> !BecomesCallLeftRight(op) && !BecomesLeftCallsRight(op)
    ensures BecomesLeftCallsRight(op) ==> !BecomesCallLeftRight(op) && !BecomesRightCallsLeft(op)
  {}

  predicate BecomesCallLeftRight(op: BinOp) {
    match op {
      case EuclidianDiv()
        | EuclidianMod()
        => true
      case _ => false
    }
  }

  function UnreachablePanicIfVerified(pointerType: PointerType, optText: string := ""): R.Expr {
    if pointerType.Raw? then
      R.Unsafe(R.Block(R.std.MSel("hint").AsExpr().FSel("unreachable_unchecked").Apply0()))
    else if optText == "" then
      R.Identifier("panic!").Apply0()
    else
      R.Identifier("panic!").Apply1(R.LiteralString(optText, binary := false, verbatim := false))
  }

  function DebugImpl(rTypeParamsDecls: seq<R.TypeParamDecl>, datatypeType: R.Type, rTypeParams: seq<R.Type>): R.ModDecl {
    R.ImplDecl(
      R.ImplFor(
        rTypeParamsDecls,
        R.std.MSel("fmt").MSel("Debug").AsType(),
        datatypeType,
        "",
        [
          R.FnDecl(
            R.PRIV,
            R.Fn(
              "fmt", [],
              [R.Formal.selfBorrowed,
               R.Formal("f", R.BorrowedMut(R.std.MSel("fmt").MSel("Formatter").AsType()))],
              Some(R.std.MSel("fmt").MSel("Result").AsType()),
              "",
              Some(R.dafny_runtime
                   .MSel("DafnyPrint")
                   .AsExpr()
                   .FSel("fmt_print")
                   .Apply(
                     [ R.self,
                       R.Identifier("f"),
                       R.LiteralBool(true)
                     ])))
          )
        ]
      ))
  }

  function PrintImpl(rTypeParamsDecls: seq<R.TypeParamDecl>, datatypeType: R.Type, rTypeParams: seq<R.Type>, printImplBody: R.Expr): R.ModDecl {
    R.ImplDecl(
      R.ImplFor(
        rTypeParamsDecls,
        R.DafnyPrint,
        datatypeType,
        "",
        [R.FnDecl(
           R.PRIV,
           R.Fn(
             "fmt_print", [],
             [R.Formal.selfBorrowed,
              R.Formal("_formatter", R.BorrowedMut(R.std.MSel("fmt").MSel("Formatter").AsType())),
              R.Formal("_in_seq", R.Type.Bool)],
             Some(R.RawType("std::fmt::Result")),
             "",
             Some(printImplBody)))]
      ))
  }

  function CoerceImpl(
    rTypeParamsDecls: seq<R.TypeParamDecl>,
    datatypeName: string,
    datatypeType: R.Type,
    rCoerceTypeParams: seq<R.TypeParamDecl>,
    coerceArguments: seq<R.Formal>,
    coerceTypes: seq<R.Type>,
    coerceImplBody: R.Expr
  ): R.ModDecl {

    R.ImplDecl(
      R.Impl(
        rTypeParamsDecls,
        datatypeType,
        "",
        [R.FnDecl(
           R.PUB,
           R.Fn(
             "coerce", rCoerceTypeParams,
             coerceArguments,
             Some(
               R.Rc(
                 R.ImplType(
                   R.FnType(
                     [datatypeType],
                     R.TypeApp(R.TIdentifier(datatypeName), coerceTypes))))),
             "",
             Some(
               R.RcNew(R.Lambda([R.Formal("this", R.SelfOwned)],
                                Some(R.TypeApp(R.TIdentifier(datatypeName), coerceTypes)),
                                coerceImplBody)))))]
      ))
  }

  function SingletonsImpl(
    rTypeParamsDecls: seq<R.TypeParamDecl>,
    datatypeType: R.Type,
    instantiationType: R.Type,
    singletonConstructors: seq<R.Expr>): R.ModDecl {
    R.ImplDecl(
      R.Impl(
        rTypeParamsDecls,
        datatypeType,
        "",
        [R.FnDecl(
           R.PUB,
           R.Fn(
             "_AllSingletonConstructors", [],
             [],
             Some(R.dafny_runtime.MSel("SequenceIter").AsType().Apply([instantiationType])),
             "",
             Some(R.dafny_runtime.MSel("seq!").AsExpr().Apply(singletonConstructors).Sel("iter").Apply0())
           )
         )]))
  }
}