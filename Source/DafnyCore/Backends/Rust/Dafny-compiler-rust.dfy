include "../Dafny/AST.dfy"
  // Dafny to Rust compilation tenets:
  // - The Compiled Dafny AST should be minimal
  // - The generated code should look idiomatic and close to the original Dafny file if possible

// Rust AST
module RAST
  // All ToString methods should produce well-formed Rust code
{
  import opened Std.Wrappers
  import Std
  import opened DAST.Format
  import Strings = Std.Strings

  // Rust tuples support some traits like Default only till arity 12
  // Past that, we use Dafny system tuples (see https://www.reddit.com/r/rust/comments/11gvkda/why_rust_std_only_provides_trait_implementation/)
  const MAX_TUPLE_SIZE := 12

  // Default Indentation
  const IND := "  "

  opaque function FoldLeft<A(!new), T>(f: (A, T) --> A, init: A, xs: seq<T>): A
    requires forall t: T <- xs, a: A :: f.requires(a, t)
  {
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  datatype Mod =
      // Rust modules
    | Mod(name: string, body: seq<ModDecl>)
    | ExternMod(name: string)
  {
    function Fold<T(!new)>(acc: T, accBuilder: (T, ModDecl) --> T): T
      requires Mod? ==> forall modDecl: ModDecl <- body, t: T :: accBuilder.requires(t, modDecl)
    {
      if ExternMod? then acc else
      FoldLeft(accBuilder, acc, body)
    }
    function ToString(ind: string): string
      decreases this
    {
      match this {
        case ExternMod(name) =>
          "pub mod " + name + ";"
        case Mod(name, body) =>
          /* If the module does not start with "use", just separate declarations by one blank line
             If the module starts with "use", add blank lines only after use declarations */
          var startWithUse := |body| > 0 && body[0].UseDecl?;
          var prefixIfNotUseDecl := if startWithUse then "\n" + ind + IND else "";
          var prefixIfUseDecl := if startWithUse then ind + IND else "";
          var infixDecl := if startWithUse then "\n" else "\n\n" + ind + IND;
          var initialIdent := if startWithUse then "" else ind + IND;
          "pub mod " + name + " {" + "\n" + initialIdent +
          SeqToString(
            body,
            (modDecl: ModDecl) requires modDecl < this =>
              (if modDecl.UseDecl? then prefixIfUseDecl else prefixIfNotUseDecl) +
              modDecl.ToString(ind + IND), infixDecl)
          + "\n" + ind + "}"
      }
    }
  }
  function SeqToString<T>(s: seq<T>, f: T --> string, separator: string := ""): string
    requires forall t <- s :: f.requires(t)
  {
    if |s| == 0 then "" else
    f(s[0]) + (if |s| > 1 then separator + SeqToString(s[1..], f, separator) else "")
  }
  datatype ModDecl =
    | ModDecl(mod: Mod)
    | StructDecl(struct: Struct)
    | TypeDecl(tpe: TypeSynonym)
    | ConstDecl(c: Constant)
    | EnumDecl(enum: Enum)
    | ImplDecl(impl: Impl)
    | TraitDecl(tr: Trait)
    | TopFnDecl(fn: TopFnDecl)
    | UseDecl(use: Use)
  {
    function ToString(ind: string): string
      decreases this
    {
      if ModDecl? then mod.ToString(ind)
      else if StructDecl? then struct.ToString(ind)
      else if ImplDecl? then impl.ToString(ind)
      else if EnumDecl? then enum.ToString(ind)
      else if TypeDecl? then tpe.ToString(ind)
      else if ConstDecl? then c.ToString(ind)
      else if TraitDecl? then tr.ToString(ind)
      else if TopFnDecl? then fn.ToString(ind)
      else assert UseDecl?; use.ToString(ind)
    }
  }
  datatype Use = Use(visibility: Visibility, path: Path) {
    function ToString(ind: string): string {
      visibility.ToString() + "use " + path.ToString() + ";"
    }
  }
  datatype TopFnDecl = TopFn(attributes: seq<Attribute>, visibility: Visibility, fn: Fn) {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      visibility.ToString() + fn.ToString(ind)
    }
  }
  datatype Attribute = RawAttribute(content: string) {
    static function ToStringMultiple(attributes: seq<Attribute>, ind: string): string {
      SeqToString(
        attributes,
        (attribute: Attribute) => attribute.content + "\n" + ind)
    }
  }

  datatype Struct =
    Struct(attributes: seq<Attribute>,
           name: string, typeParams: seq<TypeParamDecl>, fields: Fields)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub struct " + name +
      TypeParamDecl.ToStringMultiple(typeParams, ind) +
      fields.ToString(ind, fields.NamedFields?) +
      (if fields.NamelessFields? then ";" else "")
    }
  }

  datatype TypeSynonym =
    TypeSynonym(attributes: seq<Attribute>,
                name: string, typeParams: seq<TypeParamDecl>, tpe: Type)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub type " + name +
      TypeParamDecl.ToStringMultiple(typeParams, ind) + " = " +
      tpe.ToString(ind) + ";"
    }
  }

  datatype Constant =
    Constant(attributes: seq<Attribute>,
             name: string, tpe: Type, value: Expr)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub const " + name + ": " + tpe.ToString(ind) + "=" +
      value.ToString(ind) + ";"
    }
  }

  datatype NamelessField =
    NamelessField(visibility: Visibility, tpe: Type)
  {
    function ToString(ind: string): string {
      visibility.ToString() + tpe.ToString(ind)
    }
  }

  datatype Field = Field(visibility: Visibility, formal: Formal)
  {
    function ToString(ind: string): string {
      visibility.ToString() + formal.ToString(ind)
    }
    function ToNamelessField(): NamelessField {
      NamelessField(visibility, formal.tpe)
    }
  }

  datatype Fields =
    | NamedFields(fields: seq<Field>)
    | NamelessFields(types: seq<NamelessField>)
  {
    function ToNamelessFields(): Fields
      requires NamedFields?
    {
      NamelessFields(seq(|fields|, i requires 0 <= i < |fields| => fields[i].ToNamelessField()))
    }
    function ToString(ind: string, newLine: bool): string {
      if NamedFields? then
        var separator := if newLine then ",\n" + ind + IND else ", ";
        var (beginSpace, endSpace) :=
          if newLine && |fields| > 0 then
            ("\n" + ind + IND, "\n" + ind)
          else if |fields| > 0 then
            (" ", " ")
          else
            ("", "");
        " {" + beginSpace +
        SeqToString(fields, (field: Field) => field.ToString(ind + IND), separator)
        + endSpace + "}"
      else
        assert NamelessFields?;
        var separator := if newLine then ",\n" + ind + IND else ", ";
        "("+
        SeqToString(types, (t: NamelessField) => t.ToString(ind + IND), separator)
        +")"
    }
  }

  datatype EnumCase =
    | EnumCase(name: string, fields: Fields)
  {
    function ToString(ind: string, newLine: bool): string {
      name + fields.ToString(ind, newLine)
    }
  }

  datatype Enum =
    Enum(attributes: seq<Attribute>,
         name: string, typeParams: seq<TypeParamDecl>,
         variants: seq<EnumCase>)
  {
    function ToString(ind: string): string {
      Attribute.ToStringMultiple(attributes, ind) +
      "pub enum " + name +
      TypeParamDecl.ToStringMultiple(typeParams, ind)
      + " {" +
      SeqToString(
        variants,
        (variant: EnumCase) =>
          "\n" + ind + IND + variant.ToString(ind + IND, true), ",") +
      "\n" + ind + "}"
    }
  }

  type TypeParamConstraint = Type

  datatype TypeParamDecl =
    | TypeParamDecl(name: string, constraints: seq<TypeParamConstraint>)
  {
    static function ToStringMultiple(typeParams: seq<TypeParamDecl>, ind: string): string {
      if |typeParams| == 0 then "" else
      "<" + SeqToString(typeParams, (t: TypeParamDecl) => t.ToString(ind + IND), ", ") + ">"
    }
    static function {:tailrecursion true} AddConstraintsMultiple(
      typeParams: seq<TypeParamDecl>, constraints: seq<TypeParamConstraint>
    ): seq<TypeParamDecl> {
      if |typeParams| == 0 then []
      else
        [typeParams[0].AddConstraints(constraints)] + AddConstraintsMultiple(typeParams[1..], constraints)
    }
    function AddConstraints(constraints: seq<TypeParamConstraint>): TypeParamDecl {
      this.(constraints := this.constraints + constraints)
    }
    function ToString(ind: string): string {
      name + (
        if |constraints| == 0 then
          ""
        else
          ": " + SeqToString(constraints, (t: TypeParamConstraint) requires t < this =>
                               t.ToString(ind + IND), " + "))
    }
  }
  const SelfBorrowed := Borrowed(SelfOwned)

  const SelfBorrowedMut := BorrowedMut(SelfOwned)

  const RcPath := std.MSel("rc").MSel("Rc")

  const RcType := RcPath.AsType()

  const ObjectPath: Path := dafny_runtime.MSel("Object")

  const Object := ObjectPath.AsExpr()

  function ObjectType(underlying: Type): Type {
    ObjectPath.AsType().Apply([underlying])
  }

  const PtrPath: Path := dafny_runtime.MSel("Ptr")

  const Ptr := PtrPath.AsExpr()

  function PtrType(underlying: Type): Type {
    PtrPath.AsType().Apply([underlying])
  }

  function Rc(underlying: Type): Type {
    TypeApp(RcType, [underlying])
  }
  function RefCell(underlying: Type): Type {
    TypeApp(RefcellType, [underlying])
  }
  function Vec(underlying: Type): Type {
    TypeApp(std.MSel("vec").MSel("Vec").AsType(), [underlying])
  }
  function NewVec(elements: seq<Expr>): Expr {
    Identifier("vec!").Apply(elements)
  }
  function Borrow(underlying: Expr): Expr {
    UnaryOp("&", underlying, UnaryOpFormat.NoFormat)
  }
  function BorrowMut(underlying: Expr): Expr {
    UnaryOp("&mut", underlying, UnaryOpFormat.NoFormat)
  }

  function RawType(content: string): Type {
    TIdentifier(content)
  }

  function Box(content: Type): Type {
    TypeApp(TIdentifier("Box"), [content])
  }
  function BoxNew(content: Expr): Expr {
    Identifier("Box").FSel("new").Apply([content])
  }

  datatype Path =
    | Global() // ::...   to access other crates
    | Crate()  // crate::... to access modules and imported modules in the same crate
    | Self()   // Self::...
    | PMemberSelect(base: Path, name: string)
  {
    function MSel(name: string): Path {
      PMemberSelect(this, name)
    }
    function FSel(name: string): Expr {
      AsExpr().FSel(name)
    }
    function AsType(): Type {
      TypeFromPath(this)
    }
    function AsExpr(): Expr {
      ExprFromPath(this)
    }
    function ToString(): string {
      match this {
        case Global() => ""
        case Crate() => "crate"
        case Self() => "Self"
        case PMemberSelect(base, name) => base.ToString() + "::" + name
      }
    }
    function RightMostIdentifier(): Option<string> {
      match this {
        case Global() => None
        case Crate() => Some("crate")
        case Self() => Some("Self")
        case PMemberSelect(base, name) => Some(name)
      }
    }
  }

  const SelfOwned := Self().AsType()

  datatype Type =
    | U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128
    | Bool
    | TIdentifier(name: string)
    | TypeFromPath(path: Path)
    | TypeApp(baseName: Type, arguments: seq<Type>)
    | Borrowed(underlying: Type)
    | BorrowedMut(underlying: Type)
    | ImplType(underlying: Type)
    | DynType(underlying: Type)
    | TupleType(arguments: seq<Type>)
    | FnType(arguments: seq<Type>, returnType: Type)
    | IntersectionType(left: Type, right: Type)
    | Array(underlying: Type, size: Option<string>)
    | TSynonym(display: Type, base: Type)
  {
    function Expand(): (r: Type)
      ensures !r.TSynonym? && (!TSynonym? ==> r == this)
    {
      if TSynonym? then base.Expand() else this
    }
    predicate EndsWithNameThatCanAcceptGenerics() {
      || U8? || U16? || U32? || U64? || U128? || I8? || I16? || I32? || I64? || I128?
      || TIdentifier? || TypeFromPath?
      || (Borrowed? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (BorrowedMut? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (ImplType? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (DynType? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (IntersectionType? && right.EndsWithNameThatCanAcceptGenerics())
      || (TSynonym? && display.EndsWithNameThatCanAcceptGenerics())
    }
    function ReplaceMap(mapping: map<Type, Type>): Type {
      Replace((t: Type) => if t in mapping then mapping[t] else t)
    }
    function Replace(mapping: Type -> Type): Type {
      var r :=
        match this {
          case U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | Bool => this
          case TIdentifier(_) => this
          case TypeFromPath(path) => this
          case TypeApp(baseName, arguments) =>
            this.(baseName := baseName.Replace(mapping),
            arguments := Std.Collections.Seq.Map(
              t requires t in arguments => t.Replace(mapping), arguments))
          case Borrowed(underlying) => this.(underlying := underlying.Replace(mapping))
          case BorrowedMut(underlying) => this.(underlying := underlying.Replace(mapping))
          case ImplType(underlying) => this.(underlying := underlying.Replace(mapping))
          case DynType(underlying) => this.(underlying := underlying.Replace(mapping))
          case TupleType(arguments) =>
            this.(
            arguments := Std.Collections.Seq.Map(
              t requires t in arguments => t.Replace(mapping), arguments))
          case FnType(arguments, returnType) =>
            this.(arguments := Std.Collections.Seq.Map(
              t requires t in arguments => t.Replace(mapping), arguments),
            returnType := returnType.Replace(mapping))
          case IntersectionType(left, right) =>
            this.(left := left.Replace(mapping), right := right.Replace(mapping))
          case Array(underlying, size) =>
            this.(underlying := underlying.Replace(mapping))
          case TSynonym(display, base) =>
            this.(display := display.Replace(mapping), base := base.Replace(mapping))
        };
      mapping(r)
    }

    function Fold<T>(acc: T, f: (T, Type) -> T): T
      // Traverses all types in a random order
    {
      var newAcc := f(acc, this);
      match this {
        case U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | Bool => newAcc
        case TIdentifier(_) => newAcc
        case TypeFromPath(path) => newAcc
        case TypeApp(baseName, arguments) =>
          Std.Collections.Seq.FoldLeft(
            (acc: T, argType: Type) => assume {:axiom} argType in arguments; argType.Fold(acc, f),
            baseName.Fold(newAcc, f),
            arguments)
        case Borrowed(underlying) => underlying.Fold(newAcc, f)
        case BorrowedMut(underlying) => underlying.Fold(newAcc, f)
        case ImplType(underlying) => underlying.Fold(newAcc, f)
        case DynType(underlying) => underlying.Fold(newAcc, f)
        case TupleType(arguments) =>
          Std.Collections.Seq.FoldLeft(
            (acc: T, argType: Type) => assume {:axiom} argType in arguments; argType.Fold(acc, f),
            newAcc, arguments)
        case FnType(arguments, returnType) =>
          returnType.Fold(
            Std.Collections.Seq.FoldLeft(
              (acc: T, argType: Type) => assume {:axiom} argType in arguments; argType.Fold(acc, f),
              newAcc, arguments),
            f)
        case IntersectionType(left, right) =>
          right.Fold(left.Fold(newAcc, f), f)
        case Array(underlying, size) => underlying.Fold(newAcc, f)
        case TSynonym(display, base) => display.Fold(newAcc, f)
      }
    }

    predicate CanReadWithoutClone() {
      U8? || U16? || U32? || U64? || U128? || I8? || I16? || I32? || I64? || I128? || Bool?
      || (TSynonym? && base.CanReadWithoutClone()) || IsPointer()
    }
    predicate IsRcOrBorrowedRc() {
      (TypeApp? && baseName == RcType) ||
      (Borrowed? && underlying.IsRcOrBorrowedRc()) ||
      (TSynonym? && base.IsRcOrBorrowedRc())
    }
    function ExtractMaybePlacebo(): Option<Type> {
      match this {
        case TypeApp(wrapper, arguments) =>
          if wrapper == TypeFromPath(MaybePlaceboPath)
             && |arguments| == 1
          then
            Some(arguments[0])
          else
            None
        case _ => None
      }
    }
    function ExtractMaybeUninitArrayElement(): Option<Type> {
      if this.IsObjectOrPointer() then
        var s := this.ObjectOrPointerUnderlying();
        if s.Array? && IsMaybeUninitType(s.underlying) then
          Some(MaybeUninitTypeUnderlying(s.underlying))
        else if s.IsMultiArray() && IsMaybeUninitType(s.MultiArrayUnderlying()) then
          Some(MaybeUninitTypeUnderlying(s.MultiArrayUnderlying()))
        else
          None
      else
        None
    }
    function ToString(ind: string): string {
      match this {
        case Bool() => "bool"
        case TIdentifier(underlying) => underlying
        case TypeFromPath(underlying) => underlying.ToString()
        case Borrowed(underlying) => "&" + underlying.ToString(ind)
        case BorrowedMut(underlying) => "&mut " + underlying.ToString(ind)
        case ImplType(underlying) => "impl " + underlying.ToString(ind)
        case DynType(underlying) => "dyn " + underlying.ToString(ind)
        case FnType(arguments, returnType) =>
          "::std::ops::Fn("+
          SeqToString(arguments, (arg: Type) requires arg < this =>
                        arg.ToString(ind + IND), ", ")
          +") -> " + returnType.ToString(ind + IND)
        case IntersectionType(left, right) =>
          left.ToString(ind) + " + " + right.ToString(ind)
        case TupleType(args) =>
          (if args == [] then
             "()"
           else
             "(" +
             SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
             + ")")
        case TypeApp(base, args) =>
          base.ToString(ind) +
          (if args == [] then
             ""
           else
             "<" +
             SeqToString(args, (arg: Type) requires arg < this => arg.ToString(ind + IND), ", ")
             + ">")

        case U8() => "u8"
        case U16() => "u16"
        case U32() => "u32"
        case U64() => "u64"
        case U128() => "u128"
        case I8() => "i8"
        case I16() => "i16"
        case I32() => "i32"
        case I64() => "i64"
        case I128() => "i128"
        case Array(underlying, size) => "[" + underlying.ToString(ind) + (if size.Some? then "; " + size.value else "") + "]"
        case TSynonym(display, base) => display.ToString(ind)
      }
    }

    function Apply1(arg: Type): Type {
      TypeApp(this, [arg])
    }

    function Apply(args: seq<Type>): Type {
      TypeApp(this, args)
    }

    function ToOwned(): Type {
      match this {
        case Borrowed(x) => x
        case BorrowedMut(x) => x
        case x => x
      }
    }

    function ToNullExpr(): Expr
      requires IsObjectOrPointer()
    {
      assert Expand().IsObject() || Expand().IsPointer();
      if Expand().IsObject() then
        Object.FSel("null").Apply([])
      else
        Ptr.FSel("null").Apply([])
    }

    predicate IsMultiArray() {
      var t := Expand();
      t.TypeApp? &&
      var baseName := t.baseName;
      var args := t.arguments;
      |args| == 1 &&
      baseName.TypeFromPath? && baseName.path.PMemberSelect? &&
      baseName.path.base == dafny_runtime &&
      |baseName.path.name| >= 5 && baseName.path.name[0..5] == "Array"
    }

    function MultiArrayClass(): string
      requires IsMultiArray()
    {
      this.Expand().baseName.path.name
    }

    function MultiArrayUnderlying(): Type
      requires IsMultiArray()
    {
      this.Expand().arguments[0]
    }

    // Given an array type like *mut [T], produces the type *mut[MaybeUninit<T>]
    // Same for *mut ::dafny_runtime::Array2<T> that becomes *mut ::dafny_runtime::Array2<MaybeUninit<T>>
    function TypeAtInitialization(): Type {
      if this.IsObjectOrPointer() then
        var s := this.ObjectOrPointerUnderlying();
        if s.Array? && s.size.None? then
          var newUnderlying := Array(MaybeUninitType(s.underlying), None);
          if this.IsObject() then ObjectType(newUnderlying) else PtrType(newUnderlying)
        else if s.IsMultiArray() then
          var newUnderlying := TypeApp(s.Expand().baseName, [MaybeUninitType(s.Expand().arguments[0])]);
          if this.IsObject() then ObjectType(newUnderlying) else PtrType(newUnderlying)
        else
          this
      else
        this
    }

    predicate IsMaybeUninit() {
      TypeApp? && baseName.TypeFromPath?
      && baseName.path == MaybeUninitPath && |this.arguments| == 1
    }

    predicate IsUninitArray() {
      if IsObjectOrPointer() then
        var s := ObjectOrPointerUnderlying().Expand();
        if s.Array? && s.size.None? then
          s.underlying.IsMaybeUninit()
        else if s.IsMultiArray() then
          s.arguments[0].IsMaybeUninit()
        else
          false
      else
        false
    }
    predicate IsObject() {
      match this {
        case TypeApp(TypeFromPath(o), elems1) =>
          o == ObjectPath &&
          |elems1| == 1
        case _ => false
      }
    }
    predicate IsPointer() {
      match this {
        case TypeApp(TypeFromPath(o), elems1) =>
          o == PtrPath &&
          |elems1| == 1
        case _ => false
      }
    }
    predicate IsObjectOrPointer() {
      this.Expand().IsPointer() || this.Expand().IsObject()
    } by method {
      var t := this.Expand();
      return t.IsPointer() || t.IsObject();
    }
    function ObjectOrPointerUnderlying(): Type
      requires IsObjectOrPointer()
    {
      match Expand() {
        case TypeApp(_, elems1) =>
          elems1[0]
      }
    }

    predicate IsBuiltinCollection() {
      match this.Expand() {
        case TypeApp(TypeFromPath(PMemberSelect(PMemberSelect(Global(), "dafny_runtime"), tpe)), elems1) =>
          || ((tpe == "Set" || tpe == "Sequence" || tpe == "Multiset") && |elems1| == 1)
          || (tpe == "Map" && |elems1| == 2)
        case _ => false
      }
    }

    function GetBuiltinCollectionElement(): Type
      requires IsBuiltinCollection()
    {
      match this.Expand() {
        case TypeApp(TypeFromPath(PMemberSelect(PMemberSelect(Global(), "dafny_runtime"), tpe)), elems) =>
          if tpe == "Map" then elems[1] else elems[0]
      }
    }

    predicate IsRc() {
      this.TypeApp? && this.baseName == RcType && |arguments| == 1
    }
    function RcUnderlying(): Type
      requires IsRc()
    {
      arguments[0]
    }
  }

  function SystemTupleType(elements: seq<Type>): Type {
    dafny_runtime.MSel("_System").MSel("Tuple" + Strings.OfNat(|elements|)).AsType().Apply(elements)
  }

  const global := Global()
  const std: Path := global.MSel("std")
  const cell := std.MSel("cell")
  const RefcellType := cell.MSel("RefCell").AsType()
  const dafny_runtime: Path := global.MSel("dafny_runtime")
  const CloneTrait := std.MSel("clone").MSel("Clone").AsType()
  const DefaultPath := std.MSel("default").MSel("Default")
  const DefaultTrait := DefaultPath.AsType()
  const AnyTrait := std.MSel("any").MSel("Any").AsType()
  const StaticTrait := RawType("'static")
  const DafnyType := dafny_runtime.MSel("DafnyType").AsType()
  const DafnyPrint := dafny_runtime.MSel("DafnyPrint").AsType()
  const DafnyTypeEq := dafny_runtime.MSel("DafnyTypeEq").AsType()
  const Eq := std.MSel("cmp").MSel("Eq").AsType()
  const Hash := std.MSel("hash").MSel("Hash").AsType()
  const DafnyInt := dafny_runtime.MSel("DafnyInt").AsType()

  function SystemTuple(elements: seq<Expr>): Expr {
    var size := Strings.OfNat(|elements|);
    StructBuild(dafny_runtime.MSel("_System").MSel("Tuple" + size).MSel("_T" + size).AsExpr(),
                seq(|elements|, i requires 0 <= i < |elements| =>
                  AssignIdentifier("_" + Strings.OfNat(i), elements[i])
                  )
    )
  }

  const MaybeUninitPath := std.MSel("mem").MSel("MaybeUninit")
  const MaybeUninitPathType := MaybeUninitPath.AsType()
  const MaybeUninitExpr := MaybeUninitPath.AsExpr()

  function MaybeUninitType(underlying: Type): Type {
    MaybeUninitPathType.Apply([underlying])
  }
  predicate IsMaybeUninitType(tpe: Type) {
    tpe.TypeApp? && tpe.baseName == MaybeUninitPathType && |tpe.arguments| == 1
  }
  function MaybeUninitTypeUnderlying(tpe: Type): Type
    requires IsMaybeUninitType(tpe)
  {
    tpe.arguments[0]
  }
  function MaybeUninitNew(underlying: Expr): Expr {
    MaybeUninitPath.FSel("new").Apply([underlying])
  }

  const MaybePlaceboPath := dafny_runtime.MSel("MaybePlacebo")

  function MaybePlaceboType(underlying: Type): Type {
    MaybePlaceboPath.AsType().Apply1(underlying)
  }


  datatype Trait =
    | Trait(typeParams: seq<TypeParamDecl>, tpe: Type, parents: seq<Type>, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      var tpConstraints := Std.Collections.Seq
                           .Filter((typeParamDecl: TypeParamDecl) reads {} requires true => |typeParamDecl.constraints| > 0, typeParams);
      var additionalConstraints :=
        SeqToString(
          tpConstraints,
          (t: TypeParamDecl) => t.ToString(ind + IND), ",\n" + ind + IND);
      var parents := if |parents| == 0 then "" else ": " + SeqToString(
                       parents,
                       (t: Type) => t.ToString(ind + IND),
                       " + "
                     );
      var where :=
        if additionalConstraints == "" then "" else
        "\n"+ind+IND+"where\n" + ind + IND + additionalConstraints;
      "pub trait " + tpe.ToString(ind) + parents + where
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }

  datatype Impl =
    | ImplFor(typeParams: seq<TypeParamDecl>, tpe: Type, forType: Type, where: string, body: seq<ImplMember>)
    | Impl(typeParams: seq<TypeParamDecl>, tpe: Type, where: string, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "impl" + TypeParamDecl.ToStringMultiple(typeParams, ind) + " " + tpe.ToString(ind)
      + (if ImplFor? then "\n" + ind + IND + "for " + forType.ToString(ind + IND) else "")
      + (if where != "" then "\n" + ind + IND + where else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }
  datatype ImplMember =
    | RawImplMember(content: string)
    | FnDecl(pub: Visibility, fun: Fn)
    | ImplMemberMacro(expr: Expr)
  {
    function ToString(ind: string): string {
      if FnDecl? then pub.ToString() + fun.ToString(ind)
      else if ImplMemberMacro? then expr.ToString(ind) + ";"
      else assert RawImplMember?; content
    }
  }
  datatype Visibility = PUB | PRIV {
    function ToString(): string {
      if PUB? then "pub " else ""
    }
  }

  datatype Formal =
    Formal(name: string, tpe: Type)
  {
    function ToString(ind: string): string {
      if name == "self" && tpe == SelfOwned then name
      else if name == "self" && tpe == SelfBorrowed then "&" + name
      else if name == "self" && tpe == SelfBorrowedMut then "&mut " + name
      else
        name + ": " + tpe.ToString(ind)
    }
    static const selfBorrowed := Formal("self", SelfBorrowed)
    static const selfOwned := Formal("self", SelfOwned)
    static const selfBorrowedMut := Formal("self", SelfBorrowedMut)
  }

  datatype Pattern =
    RawPattern(content: string)
  {
    function ToString(ind: string): string {
      content
    }
  }

  datatype MatchCase =
    MatchCase(pattern: Pattern, rhs: Expr)
  {
    ghost function Height(): nat {
      1 + rhs.Height()
    }
    function ToString(ind: string): string
      decreases Height()
    {
      var newIndent := if rhs.Block? then ind else ind + IND;
      var rhsString := rhs.ToString(newIndent);

      pattern.ToString(ind) + " =>" +
      if '\n' in rhsString && rhsString[0] != '{' then "\n" + ind + IND + rhsString
      else " " + rhsString
    }
  }

  datatype AssignIdentifier =
    AssignIdentifier(identifier: string, rhs: Expr)
  {
    ghost function Height(): nat {
      1 + rhs.Height()
    }

    function ToString(ind: string): string
      decreases Height()
    {
      identifier + ": " + rhs.ToString(ind + IND)
    }
  }

  // When a raw stream is given, try to put some indentation on it
  function AddIndent(raw: string, ind: string): string {
    if |raw| == 0 then raw
    else if raw[0] in "[({" then
      [raw[0]] + AddIndent(raw[1..], ind + IND)
    else if raw[0] in "})]" && |ind| > 2 then
      [raw[0]] + AddIndent(raw[1..], ind[..|ind|-2])
    else if raw[0] == '\n' then
      [raw[0]] + ind + AddIndent(raw[1..], ind)
    else
      [raw[0]] + AddIndent(raw[1..], ind)
  }

  function max(i: nat, j: nat): nat {
    if i < j then j else i
  }

  datatype DeclareType = MUT | CONST

  datatype Associativity = LeftToRight | RightToLeft | RequiresParentheses
  datatype PrintingInfo =
    | UnknownPrecedence()
    | Precedence(precedence: nat)
    | SuffixPrecedence(precedence: nat)
    | PrecedenceAssociativity(precedence: nat, associativity: Associativity)
  {
    predicate NeedParenthesesFor(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then true
      else false
    }
    predicate NeedParenthesesForLeft(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.LeftToRight?
      else false
    }
    predicate NeedParenthesesForRight(underlying: PrintingInfo) {
      if UnknownPrecedence? then true
      else if underlying.UnknownPrecedence? then true
      else if precedence <= underlying.precedence then
        precedence < underlying.precedence || !PrecedenceAssociativity? || !associativity.RightToLeft?
      else false
    }
    lemma Tests()
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, LeftToRight)) == false
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(20, RightToLeft)) == false
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForLeft(PrecedenceAssociativity(20, RightToLeft)) == true
      ensures PrecedenceAssociativity(20, LeftToRight)
              .NeedParenthesesForLeft(PrecedenceAssociativity(30, LeftToRight)) == true
      ensures PrecedenceAssociativity(20, RightToLeft)
              .NeedParenthesesForRight(PrecedenceAssociativity(30, RightToLeft)) == true
    {
    }
  }

  function AssignVar(name: string, rhs: Expr): Expr {
    Expr.Assign(Some(LocalVar(name)), rhs)
  }

  function AssignMember(on: Expr, field: string, rhs: Expr): Expr {
    Expr.Assign(Some(SelectMember(on, field)), rhs)
  }

  datatype AssignLhs =
    LocalVar(name: string) |
    SelectMember(on: Expr, field: string) |
    ExtractTuple(names: seq<string>) |
    Index(expr: Expr, indices: seq<Expr>)

  datatype Expr =
      RawExpr(content: string)
    | ExprFromType(tpe: Type)
    | Identifier(name: string) // Never empty
    | Match(matchee: Expr, cases: seq<MatchCase>)
    | StmtExpr(stmt: Expr, rhs: Expr)
    | Block(underlying: Expr)
    | StructBuild(underlying: Expr, assignments: seq<AssignIdentifier>)
    | Tuple(arguments: seq<Expr>)
    | UnaryOp(op1: string, underlying: Expr, format: Format.UnaryOpFormat)
    | BinaryOp(op2: string, left: Expr, right: Expr, format2: Format.BinaryOpFormat)
    | TypeAscription(left: Expr, tpe: Type)          // underlying as tpe
    | LiteralInt(value: string)
    | LiteralBool(bvalue: bool)
    | LiteralString(value: string, binary: bool, verbatim: bool)
    | DeclareVar(declareType: DeclareType, name: string, optType: Option<Type>, optRhs: Option<Expr>) // let mut name: optType = optRhs;
    | Assign(names: Option<AssignLhs>, rhs: Expr)           // name1, name2 = rhs;
    | IfExpr(cond: Expr, thn: Expr, els: Expr)       // if cond { thn } else { els }
    | Loop(optCond: Option<Expr>, underlying: Expr)  // loop { body }
    | For(name: string, range: Expr, body: Expr)     // for name in range { body }
    | Labelled(lbl: string, underlying: Expr)        // label lbl { expr }
    | Break(optLbl: Option<string>)                  // break lbl;
    | Continue(optLbl: Option<string>)               // continue optLabel;
    | Return(optExpr: Option<Expr>)                  // return optExpr;
    | CallType(obj: Expr, typeParameters: seq<Type>) // obj::<...type parameters>
    | Call(obj: Expr, arguments: seq<Expr>)          // obj(...arguments)
    | Select(obj: Expr, name: string)                // obj.name
    | SelectIndex(obj: Expr, range: Expr)            // obj[range]
    | ExprFromPath(path: Path)                       // ::dafny_runtime::int! for example
    | FunctionSelect(obj: Expr, name: string)        // objType::name
    | Lambda(params: seq<Formal>, retType: Option<Type>, body: Expr) // move |<params>| -> retType { body }
  {
    predicate NoExtraSemicolonAfter() {
      DeclareVar? || Assign? || Break? || Continue? || Return? || For? ||
      (RawExpr? && |content| > 0 && content[|content| - 1] == ';')
    }
    // Taken from https://doc.rust-lang.org/reference/expressions.html
    const printingInfo: PrintingInfo :=
      match this {
        case RawExpr(_) => UnknownPrecedence()
        case ExprFromType(_) => Precedence(1)
        case Identifier(_) => Precedence(1)
        case LiteralInt(_) => Precedence(1)
        case LiteralBool(_) => Precedence(1)
        case LiteralString(_, _, _) => Precedence(1)
        // Paths => Precedence(1)
        // Method call => Precedence(2)
        // Field expression => PrecedenceAssociativity(3, LeftToRight)
        // case function call | ArrayIndexing => Precedence(4)
        case UnaryOp(op, underlying, format) =>
          match op {
            case "?" => SuffixPrecedence(5)
            case "-" | "*" | "!" | "&" | "&mut" => Precedence(6)
            case _ => UnknownPrecedence()
          }
        case Select(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case SelectIndex(underlying, range) => PrecedenceAssociativity(2, LeftToRight)
        case ExprFromPath(underlying) => Precedence(2)
        case FunctionSelect(underlying, name) => PrecedenceAssociativity(2, LeftToRight)
        case CallType(_, _) => PrecedenceAssociativity(2, LeftToRight)
        case Call(_, _) => PrecedenceAssociativity(2, LeftToRight)
        case TypeAscription(left, tpe) =>
          PrecedenceAssociativity(10, LeftToRight)
        case BinaryOp(op2, left, right, format) =>
          match op2 {
            case "*" | "/" | "%" => PrecedenceAssociativity(20, LeftToRight)
            case "+" | "-" => PrecedenceAssociativity(30, LeftToRight)
            case "<<" | ">>" =>
              // x as u16 << 6 is parsed as x as u16<... and expect a generic argument
              if op2 == "<<" && left.TypeAscription? && left.tpe.EndsWithNameThatCanAcceptGenerics() then
                PrecedenceAssociativity(9, LeftToRight)
              else
                PrecedenceAssociativity(40, LeftToRight)
            case "&" => PrecedenceAssociativity(50, LeftToRight)
            case "^" => PrecedenceAssociativity(60, LeftToRight)
            case "|" => PrecedenceAssociativity(70, LeftToRight)
            case "==" | "!=" | "<" | ">" | "<=" | ">=" =>
              if (op2 == "<" || op2 == "<=") && left.TypeAscription? && left.tpe.EndsWithNameThatCanAcceptGenerics() then
                PrecedenceAssociativity(9, LeftToRight)
              else
                PrecedenceAssociativity(80, RequiresParentheses)
            case "&&" => PrecedenceAssociativity(90, LeftToRight)
            case "||" => PrecedenceAssociativity(100, LeftToRight)
            case ".." | "..=" => PrecedenceAssociativity(110, RequiresParentheses)
            case "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" =>
              if op2 == "<<=" && left.TypeAscription? && left.tpe.EndsWithNameThatCanAcceptGenerics() then
                PrecedenceAssociativity(9, LeftToRight)
              else
                PrecedenceAssociativity(110, RightToLeft)
            case _ => PrecedenceAssociativity(0, RequiresParentheses)
          }
        case Lambda(_, _, _) => PrecedenceAssociativity(300, LeftToRight)
        case _ => UnknownPrecedence()
      }

    ghost function Height(): nat {
      match this {
        case Identifier(_) => 1
        case ExprFromType(_) => 1
        case LiteralInt(_) => 1
        case LiteralBool(_) => 1
        case LiteralString(_, _, _) => 1
        case Match(matchee, cases) =>
          1 + max(matchee.Height(),
                  SeqToHeight(cases, (oneCase: MatchCase)
                              requires oneCase < this
                              => oneCase.Height()))
        case StmtExpr(stmt, rhs) =>
          var default := 1 + max(stmt.Height(), rhs.Height());
          match this {
            case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(Assign(name2, rhs), last)) =>
              if name2 == Some(LocalVar(name)) then
                1 + default
              else default
            case StmtExpr(IfExpr(UnaryOp("!", BinaryOp("==", a, b, f), of), RawExpr("panic!(\"Halt\");"), RawExpr("")), last) =>
              1 + default
            case _ => default
          }

        case Block(underlying) =>
          1 + underlying.Height()
        case StructBuild(name, assignments) =>
          1 + max(name.Height(), SeqToHeight(assignments, (assignment: AssignIdentifier)
                                             requires assignment < this
                                             => assignment.Height()))
        case Tuple(arguments) =>
          1 + SeqToHeight(arguments, (argument: Expr)
                          requires argument < this
                          => argument.Height())
        // Special cases
        case UnaryOp(_, underlying, _) => 1 + underlying.Height()
        case TypeAscription(left, tpe) => 1 + left.Height()
        case BinaryOp(op, left, right, format) =>
          1 + max(left.Height(), right.Height())
        case IfExpr(cond, thn, els) =>
          1 + max(cond.Height(), max(thn.Height(), els.Height()))
        case DeclareVar(declareType, name, tpe, expr) =>
          1 + (match expr {
                 case Some(e) => e.Height()
                 case None => 0
               })
        case Assign(names, expr) =>
          match names {
            case Some(SelectMember(on, field)) => 1 + max(on.Height(), expr.Height())
            case Some(Index(arr, indices)) => 1 + max(expr.Height(), max(arr.Height(), SeqToHeight(indices,  (index: Expr) requires index < this => index.Height())))
            case _ => 1 + expr.Height()
          }
        case Loop(optCond, underlying) =>
          1 + if optCond.Some? then max(optCond.value.Height(), underlying.Height()) else underlying.Height()
        case Labelled(lbl, underlying) =>
          1 + underlying.Height()
        case Break(_) => 1
        case Continue(_) => 1
        case For(name, range, body) =>
          1 + max(range.Height(), body.Height())
        case Return(optExpr) =>
          if optExpr.Some? then 1 + optExpr.value.Height() else 1
        case CallType(obj, tpes) =>
          1 + max(obj.Height(),
                  SeqToHeight(tpes, (tpe: Type) requires tpe < this => 1))
        case Call(obj, args) =>
          1 + max(obj.Height(),
                  SeqToHeight(args, (arg: Expr) requires arg < this => arg.Height()))
        case Select(expression, name) =>
          1 + expression.Height()
        case SelectIndex(expression, range) =>
          1 + max(expression.Height(), range.Height())
        case ExprFromPath(underlying) =>
          1
        case FunctionSelect(expression, name) =>
          1 + expression.Height()
        case Lambda(params, retType, body) =>
          if body.Block? || retType.None? then 1 + body.Height()
          else 2 + body.Height()
        case _ =>
          assert RawExpr?;
          1
      }
    }

    // Wish: Prove that Optimize() preserves semantics, if any
    // TODO: Ensure that even without Optimize(), tests pass
    opaque function Optimize(): (r: Expr)
      ensures this == r || r.Height() < this.Height()
    {
      match this {
        case UnaryOp("!", BinaryOp("==", left, right, format),
          CombineFormat()) =>
          assert BinaryOp("==", left, right, format).Height()
              == BinaryOp("!=", left, right, BinaryOpFormat.NoFormat()).Height();
          BinaryOp("!=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, NoFormat()),
          CombineFormat()) =>
          assert BinaryOp(">=", left, right, BinaryOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinaryOpFormat.NoFormat()).Height();
          BinaryOp(">=", left, right, BinaryOpFormat.NoFormat())

        case UnaryOp("!", BinaryOp("<", left, right, ReverseFormat()),
          CombineFormat()) =>
          assert BinaryOp("<=", right, left, BinaryOpFormat.NoFormat()).Height()
              == BinaryOp("<", left, right, BinaryOpFormat.ReverseFormat()).Height();
          BinaryOp("<=", right, left, BinaryOpFormat.NoFormat())
        case Call(ExprFromPath(PMemberSelect(r, "truncate!")), args) =>
          if (r != dafny_runtime && r != global) || |args| != 2  then
            this
          else
            var expr := args[0];
            var tpeExpr := args[1];
            if !tpeExpr.ExprFromType? then this else
            var tpe := tpeExpr.tpe;
            if || tpe.U8? || tpe.U16? || tpe.U32? || tpe.U64? || tpe.U128?
               || tpe.I8? || tpe.I16? || tpe.I32? || tpe.I64? || tpe.I128? then
              match expr {
                case Call(ExprFromPath(PMemberSelect(base, "int!")), args) =>
                  if |args| == 1 && (base == dafny_runtime || base == global) then
                    match args[0] {
                      case LiteralInt(number) => LiteralInt(number)
                      case LiteralString(number, _, _) => LiteralInt(number)
                      case _ => this
                    }
                  else this
                case _ => this
              }
            else
              this
        case StmtExpr(DeclareVar(mod, name, Some(tpe), None), StmtExpr(Assign(name2, rhs), last)) =>
          if name2 == Some(LocalVar(name)) then
            var rewriting := StmtExpr(DeclareVar(mod, name, Some(tpe), Some(rhs)), last);
            assert rewriting.Height() < this.Height() by {
              assert StmtExpr(Assign(name2, rhs), last).Height() ==
                     1 + max(Assign(name2, rhs).Height(), last.Height()) ==
                     1 + max(1 + rhs.Height(), last.Height());
              assert this.Height() == 2 + max(1, 1 + max(1 + rhs.Height(), last.Height()));
              assert rewriting.Height() == 1 + max(1 + rhs.Height(), last.Height());
            }
            rewriting
          else
            this
        case StmtExpr(IfExpr(UnaryOp("!", BinaryOp("==", a, b, f), of), RawExpr("panic!(\"Halt\");"), RawExpr("")), last) =>
          var rewriting := StmtExpr(Identifier("assert_eq!").Apply([a, b]), last);
          assume {:axiom} rewriting.Height() < this.Height(); // TODO: Need to prove formally
          rewriting
        case _ => this
      }
    }

    predicate LeftRequiresParentheses(left: Expr) {
      printingInfo.NeedParenthesesForLeft(left.Optimize().printingInfo)
    }
    function LeftParentheses(left: Expr): (string, string) {
      if LeftRequiresParentheses(left) then
        ("(", ")")
      else
        ("", "")
    }

    predicate RightRequiresParentheses(right: Expr) {
      printingInfo.NeedParenthesesForRight(right.Optimize().printingInfo)
    }


    function RightParentheses(right: Expr): (string, string) {
      if RightRequiresParentheses(right) then
        ("(", ")")
      else
        ("", "")
    }

    function RightMostIdentifier(): Option<string> {
      match this {
        case FunctionSelect(_, id) => Some(id)
        case ExprFromPath(p) => p.RightMostIdentifier()
        case _ => None
      }
    }

    static function MaxHashes(s: string, currentHashes: string, mostHashes: string): string {
      if |s| == 0 then if |currentHashes| < |mostHashes| then mostHashes else currentHashes else
      if s[0..1] == "#" then MaxHashes(s[1..], currentHashes + "#", mostHashes)
      else MaxHashes(s[1..], "", if |currentHashes| < |mostHashes| then mostHashes else currentHashes)
    }

    static function RemoveDoubleQuotes(s: string): string {
      if |s| <= 1 then s else
      if s[0..2] == @"""""" then @"""" + RemoveDoubleQuotes(s[2..]) else
      s[0..1] + RemoveDoubleQuotes(s[1..])
    }

    function ToString(ind: string): string
      decreases Height()
    {
      match this.Optimize() {
        case Identifier(name) => name
        case ExprFromType(t) => t.ToString(ind)
        case LiteralInt(number) => number
        case LiteralBool(b) => if b then "true" else "false"
        case LiteralString(characters, binary, verbatim) =>
          var hashes := if verbatim then MaxHashes(characters, "", "") + "#" else "";
          (if binary then "b" else "") + (if verbatim then "r" + hashes else "") +
          "\"" + (if verbatim then RemoveDoubleQuotes(characters) else characters) + "\"" + hashes
        case Match(matchee, cases) =>
          "match " + matchee.ToString(ind + IND) + " {" +
          SeqToString(cases,
                      (c: MatchCase) requires c.Height() < this.Height() =>
                        "\n" + ind + IND + c.ToString(ind + IND) + ",", "") +
          "\n" + ind + "}"
        case StmtExpr(stmt, rhs) => // They are built like StmtExpr(1, StmtExpr(2, StmtExpr(3, ...)))
          if stmt.RawExpr? && stmt.content == "" then rhs.ToString(ind) else
          stmt.ToString(ind) + (if stmt.NoExtraSemicolonAfter() then "" else ";") +
          "\n" + ind + rhs.ToString(ind)
        case Block(underlying) =>
          "{\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case IfExpr(cond, thn, els) =>
          "if " + cond.ToString(ind + IND) + " {\n" + ind + IND + thn.ToString(ind + IND) +
          "\n" + ind + "}" +
          if els == RawExpr("") then "" else
          " else {\n" + ind + IND + els.ToString(ind + IND) + "\n" + ind + "}"
        case StructBuild(name, assignments) =>
          if |assignments| > 0 && assignments[0].identifier == "0" then
            // Numeric
            name.ToString(ind) + " (" +
            SeqToString(assignments, (assignment: AssignIdentifier)
                        requires assignment.Height() < this.Height()
                        =>
                          "\n" + ind + IND + assignment.rhs.ToString(ind + IND), ",") +
            (if |assignments| > 1 then "\n" + ind else "") + ")"
          else
            name.ToString(ind) + " {" +
            SeqToString(assignments, (assignment: AssignIdentifier)
                        requires assignment.Height() < this.Height()
                        =>
                          "\n" + ind + IND + assignment.ToString(ind + IND), ",") +
            (if |assignments| > 0 then "\n" + ind else "") + "}"
        case Tuple(arguments) =>
          "(" +
          SeqToString(arguments, (arg: Expr)
                      requires arg.Height() < this.Height()
                      =>
                        "\n" + ind + IND + arg.ToString(ind + IND), ",") +
          (if |arguments| > 0 then "\n" + ind else "") + ")"

        case UnaryOp(op, underlying, format) =>
          var (leftP, rightP) :=
            if printingInfo.NeedParenthesesFor(underlying.Optimize().printingInfo) then
              ("(", ")")
            else
              ("", "");
          var leftOp := if op == "&mut" && leftP != "(" then op + " " else if op == "?" then "" else op;
          var rightOp := if op == "?" then op else "";

          leftOp + leftP  + underlying.ToString(ind) + rightP + rightOp
        case TypeAscription(left, tpe) =>
          var (leftLeftP, leftRightP) := LeftParentheses(left);
          leftLeftP + left.ToString(IND) + leftRightP + " as " + tpe.ToString(IND)
        case BinaryOp(op2, left, right, format) =>
          var (leftLeftP, leftRighP) := LeftParentheses(left);
          var (rightLeftP, rightRightP) := RightParentheses(right);
          var opRendered := " " + op2 + " ";
          var indLeft := if leftLeftP == "(" then ind + IND else ind;
          var indRight := if rightLeftP == "(" then ind + IND else ind;
          leftLeftP + left.ToString(indLeft) + leftRighP + opRendered + rightLeftP + right.ToString(indRight) + rightRightP
        case DeclareVar(declareType, name, optType, optExpr) =>
          "let " + (if declareType == MUT then "mut " else "") +
          name + (if optType.Some? then ": " + optType.value.ToString(ind + IND) else "") +

          (if optExpr.Some? then
             var optExprString := optExpr.value.ToString(ind + IND);
             if optExprString == "" then
               "= /*issue with empty RHS*/" +
               if optExpr.value.RawExpr? then "Empty Raw expr" else
               if optExpr.value.LiteralString? then "Empty string literal" else
               if optExpr.value.LiteralInt? then "Empty int literal" else
               "Another case"
             else " = " + optExprString else "") + ";"
        case Assign(names, expr) =>
          var lhs := match names {
            case Some(LocalVar(name)) => name + " = "
            case Some(SelectMember(member, field)) =>
              var (leftP, rightP) := Select(member, field).LeftParentheses(member);
              leftP + member.ToString(ind) + rightP + "." + field + " = "
            case Some(ExtractTuple(names)) => "(" + SeqToString(names, (name: string) => name, ",") + ") = "
            case Some(Index(e, indices)) =>
              var (leftP, rightP) := Call(e, indices).LeftParentheses(e);
              leftP + e.ToString(ind) + rightP + "[" + SeqToString(indices,
                                                                   (index: Expr) requires index.Height() < this.Height() => index.ToString(ind + IND), "][")
              + "] = "
            case None => "_ = "
          };
          lhs + expr.ToString(ind + IND) + ";"
        case Labelled(name, underlying) =>
          "'" + name + ": " + underlying.ToString(ind)
        case Break(optLbl) =>
          match optLbl {
            case Some(lbl) => "break '" + lbl + ";"
            case None => "break;"
          }
        case Continue(optLbl) =>
          match optLbl {
            case Some(lbl) => "continue '" + lbl + ";"
            case None => "continue;"
          }
        case Loop(optCond, underlying) =>
          (match optCond {
             case None => "loop"
             case Some(c) => "while " + c.ToString(ind + IND)
           }) + " {\n" + ind + IND + underlying.ToString(ind + IND) + "\n" + ind + "}"
        case For(name, range, body) =>
          "for "+ name +" in " + range.ToString(ind + IND) + " {\n" + ind + IND +
          body.ToString(ind + IND) + "\n" + ind + "}"
        case Return(optExpr) =>
          "return" + (if optExpr.Some? then " " + optExpr.value.ToString(ind + IND) else "") + ";"
        case CallType(expr, tpes) =>
          var (leftP, rightP) := LeftParentheses(expr);
          if tpes == [] then expr.ToString(ind) else
          leftP + expr.ToString(ind) + rightP + "::<" +
          SeqToString(tpes, (tpe: Type) => tpe.ToString(ind + IND), ", ") +">"

        case Call(expr, args) =>
          var (leftP, rightP) := LeftParentheses(expr);
          var (leftCallP, rightCallP) := match expr.RightMostIdentifier() {
            case Some("seq!") | Some("map!")  =>
              ("[","]")
            case Some("set!") | Some("multiset!") =>
              ("{","}")
            case _ =>
              ("(", ")")
          };
          leftP + expr.ToString(ind) + rightP +
          leftCallP + SeqToString(args, (arg: Expr) requires arg.Height() < this.Height() => arg.ToString(ind + IND), ", ")+ rightCallP
        case Select(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "." + name
        case SelectIndex(expression, range) =>
          var (leftP, rightP) := LeftParentheses(expression);
          var rangeStr := range.ToString(ind + IND);
          leftP + expression.ToString(ind) + rightP + "[" + rangeStr + "]"
        case ExprFromPath(path) =>
          path.ToString()
        case FunctionSelect(expression, name) =>
          var (leftP, rightP) := LeftParentheses(expression);
          leftP + expression.ToString(ind) + rightP + "::" + name
        case Lambda(params, retType, body) =>
          "move |" + SeqToString(params, (arg: Formal) => arg.ToString(ind), ",") + "| " +
          (if retType.Some? then
             "-> " + retType.value.ToString(ind)
           else "") +
          (if retType.Some? && !body.Block? then
             Block(body).ToString(ind)
           else body.ToString(ind))
        case r =>
          assert r.RawExpr?; AddIndent(r.content, ind)
      }
    }
    function Then(rhs2: Expr): Expr {
      if this.StmtExpr? then
        StmtExpr(stmt, rhs.Then(rhs2))
      else if this == RawExpr("") then
        rhs2
      else
        StmtExpr(this, rhs2)
    }

    // Helpers

    function Sel(name: string): Expr {
      Select(this, name)
    }
    function FSel(name: string): Expr {
      FunctionSelect(this, name)
    }
    function ApplyType(typeParameters: seq<Type>): Expr {
      if |typeParameters| == 0 then this else
      CallType(this, typeParameters)
    }
    function ApplyType1(typeParameter: Type): Expr {
      CallType(this, [typeParameter])
    }
    function Apply(arguments: seq<Expr>): Expr {
      Call(this, arguments)
    }

    function Apply1(argument: Expr): Expr {
      Call(this, [argument])
    }

    predicate IsLhsIdentifier() {
      || this.Identifier?
      || (&& this.Call?
          &&
             (|| (
                   && this.obj.ExprFromPath? && this.obj.path == dafny_runtime.MSel("modify!")
                   && |this.arguments| == 1 // modify!(self)
                   && this.arguments[0].Identifier?)
              || (
                   && this.obj.ExprFromPath? && this.obj.path == dafny_runtime.MSel("md!")
                   && |this.arguments| == 1 // md!(identifier.clone())
                   && var lhs := this.arguments[0];
                   && lhs.Call?
                   && lhs.obj.Select?
                   && lhs.obj.obj.Identifier?
                 )))
    }

    function LhsIdentifierName(): string requires IsLhsIdentifier() {
      if this.Identifier? then name
      else if this.obj.ExprFromPath? && obj.path == dafny_runtime.MSel("modify!") then
        this.arguments[0].name
      else
        this.arguments[0].obj.obj.name
    }

    function Clone(): Expr {
      Select(this, "clone").Apply([])
    }
  }

  const self := Identifier("self")


  const crate := Crate()
  const dafny_runtime_Set := dafny_runtime.MSel("Set").AsExpr()
  const dafny_runtime_Set_from_array := dafny_runtime_Set.FSel("from_array")
  const dafny_runtime_Sequence := dafny_runtime.MSel("Sequence").AsExpr()
  const Sequence_from_array_owned := dafny_runtime_Sequence.FSel("from_array_owned")
  const Sequence_from_array := dafny_runtime_Sequence.FSel("from_array")
  const dafny_runtime_Multiset := dafny_runtime.MSel("Multiset").AsExpr()
  const dafny_runtime_Multiset_from_array := dafny_runtime_Multiset.FSel("from_array")

  function MaybePlacebo(underlying: Expr): Expr {
    MaybePlaceboPath.FSel("from").Apply1(underlying)
  }

  const std_rc := std.MSel("rc")

  const std_rc_Rc := std_rc.MSel("Rc")

  const std_rc_Rc_new := std_rc_Rc.FSel("new")

  const std_Default_default := DefaultPath.FSel("default").Apply([])

  function RcNew(underlying: Expr): Expr {
    Call(std_rc_Rc_new, [underlying])
  }

  function IntoUsize(underlying: Expr): Expr {
    dafny_runtime.MSel("DafnyUsize").FSel("into_usize").Apply1(underlying)
  }

  datatype Fn =
    Fn(name: string, typeParams: seq<TypeParamDecl>, formals: seq<Formal>,
       returnType: Option<Type>,
       where: string,
       body: Option<Expr>)
  {
    function ToString(ind: string): string {
      "fn " + name + TypeParamDecl.ToStringMultiple(typeParams, ind) +
      "(" + SeqToString(formals, (formal: Formal) => formal.ToString(ind), ", ") + ")" +
      (match returnType case Some(t) => " -> " + t.ToString(ind) case _ => "") +
      (if where == "" then "" else "\n" + ind + IND + where) +
      match body {
        case None => ";"
        case Some(body) =>
          " {\n" + ind + IND +
          body.ToString(ind + IND) +
          "\n" + ind + "}"
      }
    }
  }
}

module {:extern "DCOMP"} DafnyToRustCompiler {
  import FactorPathsOptimization

  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  import opened DafnyCompilerRustUtils

  const IND := R.IND
  type Type = DAST.Type
  type Formal = DAST.Formal

  const AttributeOwned := Attribute("owned", [])

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
  datatype CharType = UTF16 | Unicode
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
    | AdvancedExtern(enclosingModule: string, overrideName: string)
    | UnsupportedExtern(reason: string)

  opaque function OptExtern(attr: Attribute, dafnyName: Name): Option<ExternAttribute> {
    if attr.name == "extern" then
      Some(
        if |attr.args| == 0 then SimpleExtern(escapeName(dafnyName)) else
        if |attr.args| == 1 then SimpleExtern(attr.args[0]) else
        if |attr.args| == 2 then AdvancedExtern(ReplaceDotByDoubleColon(attr.args[0]), attr.args[1]) else
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

  class COMP {
    const charType: CharType
    const pointerType: PointerType
    const rootType: RootType

    const thisFile: R.Path := if rootType.RootCrate? then R.crate else R.crate.MSel(rootType.moduleName)

    const DafnyChar := if charType.Unicode? then "DafnyChar" else "DafnyCharUTF16"
    const DafnyCharUnderlying := if charType.Unicode? then R.RawType("char") else R.RawType("u16")
    const string_of := if charType.Unicode? then "string_of" else "string_utf16_of"
    const allocate :=
      if pointerType.Raw? then "allocate" else "allocate_object"
    const allocate_fn := "_" + allocate
    const update_field_uninit_macro :=
      if pointerType.Raw? then "update_field_uninit!" else "update_field_uninit_object!"
    const thisInConstructor :=
      if pointerType.Raw? then R.Identifier("this") else R.Identifier("this").Clone()
    const array_construct :=
      if pointerType.Raw? then "construct" else "construct_object"
    const modify_macro := R.dafny_runtime.MSel(if pointerType.Raw? then "modify!" else "md!").AsExpr()
    const read_macro := R.dafny_runtime.MSel(if pointerType.Raw? then "read!" else "rd!").AsExpr()
    function Object(underlying: R.Type): R.Type {
      if pointerType.Raw? then R.PtrType(underlying) else R.ObjectType(underlying)
    }
    const placebos_usize := if pointerType.Raw? then "placebos_usize" else "placebos_usize_object"
    const update_field_if_uninit_macro :=
      if pointerType.Raw? then "update_field_if_uninit!" else "update_field_if_uninit_object!"
    const Upcast :=
      if pointerType.Raw? then "Upcast" else "UpcastObject"
    const UpcastFnMacro :=
      Upcast + "Fn!"
    const upcast :=
      if pointerType.Raw? then "upcast" else "upcast_object"

    const downcast :=
      if pointerType.Raw? then "cast!" else "cast_object!"

    function UnreachablePanicIfVerified(optText: string := ""): string {
      if pointerType.Raw? then "unsafe { ::std::hint::unreachable_unchecked() }" else
      if optText == "" then "panic!()" else "panic!(\"" + optText + "\")"
    }


    var error: Option<string>

    var optimizations: seq<R.Mod -> R.Mod>

    static const DAFNY_EXTERN_MODULE := "_dafny_externs"

    constructor(charType: CharType, pointerType: PointerType, rootType: RootType) {
      this.charType := charType;
      this.pointerType := pointerType;
      this.rootType := rootType;
      this.error := None; // If error, then the generated code contains <i>Unsupported: .*</i>
      this.optimizations := [FactorPathsOptimization.apply];
      new;
    }

    static function ContainingPathToRust(containingPath: seq<Ident>): seq<string> {
      Std.Collections.Seq.Map((i: Ident) => escapeName(i.id), containingPath)
    }

    // Returns a top-level gathering module that can be merged with other gathering modules
    method GenModule(mod: Module, containingPath: seq<Ident>) returns (s: SeqMap<string, GatheringModule>)
      decreases mod, 1
      modifies this
    {
      var (innerPath, innerName) := DafnyNameToContainingPathAndName(mod.name);
      var containingPath := containingPath + innerPath;
      var modName := escapeName(innerName);
      if mod.body.None? {
        s := GatheringModule.Wrap(ContainingPathToRust(containingPath), R.ExternMod(modName));
      } else {
        assume {:axiom} forall m: ModuleItem <- mod.body.value :: m < mod;
        var optExtern: ExternAttribute := ExtractExternMod(mod);
        var body, allmodules := GenModuleBody(mod, mod.body.value, containingPath + [Ident.Ident(innerName)]);
        if optExtern.SimpleExtern? {
          if mod.requiresExterns {
            body := [R.UseDecl(R.Use(R.PUB, thisFile.MSel(DAFNY_EXTERN_MODULE).MSel(ReplaceDotByDoubleColon(optExtern.overrideName)).MSel("*")))] + body;
          }
        } else if optExtern.AdvancedExtern? {
          error := Some("Externs on modules can only have 1 string argument");
        } else if optExtern.UnsupportedExtern? {
          error := Some(optExtern.reason);
        }
        s := GatheringModule.MergeSeqMap(
          GatheringModule.Wrap(ContainingPathToRust(containingPath), R.Mod(modName, body)),
          allmodules);
      }
    }

    method GenModuleBody(ghost parent: Module, body: seq<ModuleItem>, containingPath: seq<Ident>)
      returns (s: seq<R.ModDecl>, allmodules: SeqMap<string, GatheringModule>)
      requires forall m: ModuleItem <- body :: m < parent
      decreases parent, 0
      modifies this
    {
      s := [];
      allmodules := SeqMap.Empty();
      for i := 0 to |body| {
        var generated;
        match body[i] {
          case Module(m) =>
            assume {:axiom} m < parent;
            var mm := GenModule(m, containingPath);
            allmodules := GatheringModule.MergeSeqMap(allmodules, mm);
            generated := [];
          case Class(c) =>
            generated := GenClass(c, containingPath + [Ident.Ident(c.name)]);
          case Trait(t) =>
            generated := GenTrait(t, containingPath);
          case Newtype(n) =>
            generated := GenNewtype(n);
          case SynonymType(s) =>
            generated := GenSynonymType(s);
          case Datatype(d) =>
            generated := GenDatatype(d);
        }
        s := s + generated;
      }
    }

    method GenTypeParam(tp: TypeArgDecl) returns (typeArg: Type, typeParam: R.TypeParamDecl)
    {
      typeArg := TypeArg(tp.name);
      var genTpConstraint := if SupportsEquality in tp.bounds then
        [R.DafnyTypeEq]
      else
        [R.DafnyType];
      if SupportsDefault in tp.bounds {
        genTpConstraint := genTpConstraint + [R.DefaultTrait];
      }
      typeParam := R.TypeParamDecl(escapeName(tp.name.id), genTpConstraint);
    }

    method GenTypeParameters(params: seq<TypeArgDecl>)
      returns (
        typeParamsSeq: seq<Type>,
        typeParams: seq<R.Type>,
        constrainedTypeParams: seq<R.TypeParamDecl>,
        whereConstraints: string)
    {
      typeParamsSeq := [];
      typeParams := [];
      constrainedTypeParams := [];
      whereConstraints := "";
      if |params| > 0 {
        for tpI := 0 to |params| {
          var tp := params[tpI];
          var typeArg, typeParam := GenTypeParam(tp);
          var rType := GenType(typeArg, GenTypeContext.default());
          typeParamsSeq := typeParamsSeq + [typeArg];
          typeParams := typeParams + [rType];
          constrainedTypeParams := constrainedTypeParams + [typeParam];
        }
      }
    }

    // If we build a resolved type from this compiler, we won't have access to all
    // the extended traits, so the equality can be relaxed a bit
    predicate IsSameResolvedTypeAnyArgs(r1: ResolvedType, r2: ResolvedType) {
      r1.path == r2.path &&
      r1.kind == r2.kind
    }

    // If we build a resolved type from this compiler, we won't have access to all
    // the extended traits, so the equality can be relaxed a bit
    predicate IsSameResolvedType(r1: ResolvedType, r2: ResolvedType) {
      IsSameResolvedTypeAnyArgs(r1, r2)
      && r1.typeArgs == r2.typeArgs
    }

    function GatherTypeParamNames(types: set<string>, typ: R.Type): set<string> {
      typ.Fold(types, (types: set<string>, currentType: R.Type) =>
                 if currentType.TIdentifier? then
                   types + {currentType.name}
                 else
                   types
      )
    }

    method GenClass(c: Class, path: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls, whereConstraints := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParamDecl.ToStringMultiple(rTypeParamsDecls, R.IND + R.IND);

      var fields: seq<R.Field> := [];
      var fieldInits: seq<R.AssignIdentifier> := [];
      var usedTypeParams: set<string> := {};
      for fieldI := 0 to |c.fields| {
        var field := c.fields[fieldI];
        var fieldType := GenType(field.formal.typ, GenTypeContext.default());
        usedTypeParams := GatherTypeParamNames(usedTypeParams, fieldType);
        var fieldRustName := escapeVar(field.formal.name);
        fields := fields + [R.Field(R.PUB, R.Formal(fieldRustName, fieldType))];

        match field.defaultValue {
          case Some(e) => {
            // TODO(mikael): Fields must be initialized before the code of the constructor if possible
            var expr, _, _ := GenExpr(e, NoSelf, Environment.Empty(), OwnershipOwned);

            fieldInits := fieldInits + [
              R.AssignIdentifier(
                fieldRustName, expr)];
          }
          case None => {
            // TODO(mikael) Use type descriptors for default values if generics
            var default := R.std_Default_default;
            if fieldType.IsObjectOrPointer() {
              default := fieldType.ToNullExpr();
            }
            fieldInits := fieldInits + [
              R.AssignIdentifier(
                fieldRustName, default)];
          }
        }
      }

      // A phantom field is necessary to avoid Rust complaining about no reference to the type parameter.
      // PhantomData is zero-sized so it won't impact final performance or layout
      for typeParamI := 0 to |c.typeParams| {
        var typeArg, typeParam := GenTypeParam(c.typeParams[typeParamI]);
        var rTypeArg := GenType(typeArg, GenTypeContext.default());
        if typeParam.name in usedTypeParams {
          continue;
        }
        fields := fields + [
          R.Field(R.PRIV,
                  R.Formal("_phantom_type_param_" + Strings.OfNat(typeParamI),
                           R.TypeApp(R.std.MSel("marker").MSel("PhantomData").AsType(), [rTypeArg])))];
        fieldInits := fieldInits + [
          R.AssignIdentifier(
            "_phantom_type_param_" + Strings.OfNat(typeParamI),
            R.RawExpr("::std::marker::PhantomData"))];
      }

      var extern := ExtractExtern(c.attributes, c.name);

      var className;
      if extern.SimpleExtern? {
        className := extern.overrideName;
      } else {
        className := escapeName(c.name);
        if extern.AdvancedExtern? {
          error := Some("Multi-argument externs not supported for classes yet");
        }
      }

      var struct := R.Struct([], className, rTypeParamsDecls, R.NamedFields(fields));
      s := [];

      if extern.NoExtern? {
        s := s + [R.StructDecl(struct)];
      }

      var implBody, traitBodies := GenClassImplBody(
        c.body, false,
        Type.UserDefined(
          ResolvedType(
            path,
            [],
            ResolvedTypeBase.Class(),
            c.attributes,
            [], [])),
        typeParamsSeq);

      if extern.NoExtern? && className != "_default" {
        implBody := [
          R.FnDecl(
            R.PUB,
            R.Fn(allocate_fn,
                 [], [], Some(Object(R.SelfOwned)),
                 "",
                 Some(
                   R.dafny_runtime.MSel(allocate).AsExpr().ApplyType1(R.SelfOwned).Apply([])
                 ))
          )
        ] + implBody;
      }

      var selfTypeForImpl;
      if extern.NoExtern? || extern.UnsupportedExtern? {
        selfTypeForImpl := R.TIdentifier(className);
      } else if extern.AdvancedExtern? {
        selfTypeForImpl := R.crate.MSel(extern.enclosingModule).MSel(extern.overrideName).AsType();
      } else if extern.SimpleExtern? {
        selfTypeForImpl := R.TIdentifier(extern.overrideName);
      }
      if |implBody| > 0 {
        var i := R.Impl(
          rTypeParamsDecls,
          R.TypeApp(selfTypeForImpl, rTypeParams),
          whereConstraints,
          implBody
        );
        s := s + [R.ImplDecl(i)];
      }
      var genSelfPath := GenPathType(path);
      // TODO: If general traits, check whether the trait extends object or not.
      if className != "_default" {
        s := s + [
          R.ImplDecl(
            R.ImplFor(
              rTypeParamsDecls,
              R.dafny_runtime.MSel(Upcast).AsType().Apply([R.DynType(R.AnyTrait)]),
              R.TypeApp(genSelfPath, rTypeParams),
              whereConstraints,
              [
                R.ImplMemberMacro(
                  R.dafny_runtime
                  .MSel(UpcastFnMacro).AsExpr()
                  .Apply1(R.ExprFromType(R.DynType(R.AnyTrait))))
              ]
            )
          )
        ];
      }
      var superClasses := if className == "_default" then [] else c.superClasses;
      for i := 0 to |superClasses| {
        var superClass := superClasses[i];
        match superClass {
          case UserDefined(ResolvedType(traitPath, typeArgs, Trait(), _, properMethods, _)) => {
            var pathStr := GenPathType(traitPath);
            var typeArgs := GenTypeArgs(typeArgs, GenTypeContext.default());
            var body: seq<R.ImplMember> := [];
            if traitPath in traitBodies {
              body := traitBodies[traitPath];
            }

            var traitType := R.TypeApp(pathStr, typeArgs);
            if !extern.NoExtern? { // An extern of some kind
              // Either the Dafny code implements all the methods of the trait or none,
              if |body| == 0 && |properMethods| != 0 {
                continue; // We assume everything is implemented externally
              }
              if |body| != |properMethods| {
                error := Some("Error: In the class " + R.SeqToString(path, (s: Ident) => s.id.dafny_name, ".") + ", some proper methods of " +
                              traitType.ToString("") + " are marked {:extern} and some are not." +
                              " For the Rust compiler, please make all methods (" + R.SeqToString(properMethods, (s: Name) => s.dafny_name, ", ") +
                              ")  bodiless and mark as {:extern} and implement them in a Rust file, "+
                              "or mark none of them as {:extern} and implement them in Dafny. " +
                              "Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.");
              }
            }
            if |body| == 0 {
              // Extern type, we assume
            }
            var x := R.ImplDecl(
              R.ImplFor(
                rTypeParamsDecls,
                traitType,
                R.TypeApp(genSelfPath, rTypeParams),
                whereConstraints,
                body
              ));
            s := s + [x];

            s := s + [
              R.ImplDecl(
                R.ImplFor(
                  rTypeParamsDecls,
                  R.dafny_runtime.MSel(Upcast).AsType().Apply([R.DynType(traitType)]),
                  R.TypeApp(genSelfPath, rTypeParams),
                  whereConstraints,
                  [
                    R.ImplMemberMacro(
                      R.dafny_runtime
                      .MSel(UpcastFnMacro).AsExpr()
                      .Apply1(R.ExprFromType(R.DynType(traitType))))
                  ]
                )
              )
            ];
          }
          case _ => {}
        }
      }
    }

    method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq := [];
      var typeParamDecls := [];
      var typeParams := [];
      if |t.typeParams| > 0 {
        for tpI := 0 to |t.typeParams| {
          var tp := t.typeParams[tpI];
          var typeArg, typeParamDecl := GenTypeParam(tp);
          typeParamsSeq := typeParamsSeq + [typeArg];
          typeParamDecls := typeParamDecls + [typeParamDecl];
          var typeParam := GenType(typeArg, GenTypeContext.default());
          typeParams := typeParams + [typeParam];
        }
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var implBody, _ := GenClassImplBody(
        t.body, true,
        UserDefined(
          ResolvedType(
            fullPath, [],
            ResolvedTypeBase.Trait(), t.attributes,
            [], [])),
        typeParamsSeq);
      var parents := [];
      for i := 0 to |t.parents| {
        var tpe := GenType(t.parents[i], GenTypeContext.ForTraitParents());
        parents := parents + [tpe] + [R.dafny_runtime.MSel(Upcast).AsType().Apply1(R.DynType(tpe))];
      }
      s := [
        R.TraitDecl(
          R.Trait(
            typeParamDecls, R.TypeApp(R.TIdentifier(escapeName(t.name)), typeParams),
            parents,
            implBody
          ))];
    }

    method GenNewtype(c: Newtype) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls, whereConstraints := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParamDecl.ToStringMultiple(rTypeParamsDecls, R.IND + R.IND);

      var underlyingType;
      match NewtypeRangeToRustType(c.range) {
        case Some(v) =>
          underlyingType := v;
        case None =>
          underlyingType := GenType(c.base, GenTypeContext.default());
      }
      var resultingType :=
        UserDefined(
          ResolvedType(
            [], [],
            ResolvedTypeBase.Newtype(c.base, c.range, false),
            c.attributes, [], []));
      var newtypeName := escapeName(c.name);
      s := [
        R.StructDecl(
          R.Struct(
            [
              R.RawAttribute("#[derive(Clone, PartialEq)]"),
              R.RawAttribute("#[repr(transparent)]")
            ],
            newtypeName,
            rTypeParamsDecls,
            R.NamelessFields([R.NamelessField(R.PUB, underlyingType)])
          ))];

      var fnBody := R.Identifier(newtypeName);

      match c.witnessExpr {
        case Some(e) => {
          var e := if c.base == resultingType then e else Convert(e, c.base, resultingType);
          // TODO(Mikael): generate statements if any
          var eStr, _, _ := GenExpr(e, NoSelf, Environment.Empty(), OwnershipOwned);
          fnBody := fnBody.Apply1(eStr);
        }
        case None => {
          fnBody := fnBody.Apply1(R.std_Default_default);
        }
      }

      var body :=
        R.FnDecl(
          R.PRIV,
          R.Fn(
            "default", [], [], Some(R.SelfOwned),
            "",
            Some(fnBody)
          ));
      match c.constraint {
        case None =>
        case Some(NewtypeConstraint(formal, constraintStmts)) =>
          var rStmts, _, newEnv := GenStmts(constraintStmts, NoSelf, Environment.Empty(), false, None);
          var rFormals := GenParams([formal]);
          s := s + [
            R.ImplDecl(
              R.Impl(
                rTypeParamsDecls,
                R.TypeApp(R.TIdentifier(newtypeName), rTypeParams),
                whereConstraints,
                [
                  R.FnDecl(
                    R.PUB,
                    R.Fn(
                      "is", [], rFormals, Some(R.Bool()),
                      "",
                      Some(rStmts)
                    ))
                ]
              )
            )];
      }
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.DefaultTrait,
            R.TypeApp(R.TIdentifier(newtypeName), rTypeParams),
            whereConstraints,
            [body]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.DafnyPrint,
            R.TypeApp(R.TIdentifier(newtypeName), rTypeParams),
            "",
            [R.FnDecl(
               R.PRIV,
               R.Fn("fmt_print", [],
                    [R.Formal.selfBorrowed, R.Formal("_formatter", R.RawType("&mut ::std::fmt::Formatter")), R.Formal("in_seq", R.Type.Bool)],
                    Some(R.RawType("::std::fmt::Result")),
                    "",
                    Some(R.RawExpr("::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)"))
               ))]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.RawType("::std::ops::Deref"),
            R.TypeApp(R.TIdentifier(newtypeName), rTypeParams),
            "",
            [R.RawImplMember("type Target = " + underlyingType.ToString(IND) + ";"),
             R.FnDecl(
               R.PRIV,
               R.Fn("deref", [],
                    [R.Formal.selfBorrowed], Some(R.Borrowed(R.Self().MSel("Target").AsType())),
                    "",
                    Some(R.RawExpr("&self.0"))))]))];
    }

    method GenSynonymType(c: SynonymType) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls, whereConstraints := GenTypeParameters(c.typeParams);
      var synonymTypeName := escapeName(c.name);
      var resultingType := GenType(c.base, GenTypeContext.default());

      s := [
        R.TypeDecl(
          R.TypeSynonym(
            [],
            synonymTypeName, rTypeParamsDecls, resultingType
          ))];

      var defaultConstrainedTypeParams := R.TypeParamDecl.AddConstraintsMultiple(
        rTypeParamsDecls, [R.DefaultTrait]
      );
      match c.witnessExpr {
        case Some(e) => {
          var rStmts, _, newEnv := GenStmts(c.witnessStmts, NoSelf, Environment.Empty(), false, None);
          var rExpr, _, _ := GenExpr(e, NoSelf, newEnv, OwnershipOwned);
          var constantName := escapeName(Name("_init_" + c.name.dafny_name));
          s := s + [
            R.TopFnDecl(
              R.TopFn(
                [], R.PUB,
                R.Fn(
                  constantName, defaultConstrainedTypeParams, [], Some(resultingType),
                  "",
                  Some(rStmts.Then(rExpr)))
              )
            )
          ];
        }
        case None => {}
      }
    }

    predicate TypeIsEq(t: Type)
      decreases t
    {
      match t
      case UserDefined(_) => true // ResolvedTypes are assumed to support equality
      case Tuple(ts) => forall t <- ts :: TypeIsEq(t)
      case Array(t, _) => TypeIsEq(t)
      case Seq(t) => TypeIsEq(t)
      case Set(t) => TypeIsEq(t)
      case Multiset(t) => TypeIsEq(t)
      case Map(k, v) => TypeIsEq(k) && TypeIsEq(v)
      case SetBuilder(t) => TypeIsEq(t)
      case MapBuilder(k, v) => TypeIsEq(k) && TypeIsEq(v)
      case Arrow(_, _) => false
      case Primitive(_) => true
      case Passthrough(_) => true // should be Rust primitive types
      case TypeArg(i) => true // i(==) is asserted at the point of use by the verifier
      case Object() => true
    }

    predicate DatatypeIsEq(c: Datatype) {
      !c.isCo && forall ctor <- c.ctors, arg <- ctor.args :: TypeIsEq(arg.formal.typ)
    }

    method GenDatatype(c: Datatype) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls, whereConstraints := GenTypeParameters(c.typeParams);
      var datatypeName := escapeName(c.name);
      var ctors: seq<R.EnumCase> := [];
      var variances := Std.Collections.Seq.Map((typeParamDecl: TypeArgDecl) => typeParamDecl.variance, c.typeParams);
      var usedTypeParams: set<string> := {};
      for i := 0 to |c.ctors| {
        var ctor := c.ctors[i];
        var ctorArgs: seq<R.Field> := [];
        var isNumeric := false;
        for j := 0 to |ctor.args| {
          var dtor := ctor.args[j];
          var formalType := GenType(dtor.formal.typ, GenTypeContext.default());
          usedTypeParams := GatherTypeParamNames(usedTypeParams, formalType);
          var formalName := escapeVar(dtor.formal.name);
          if j == 0 && "0" == formalName {
            isNumeric := true;
          }
          if j != 0 && isNumeric && Strings.OfNat(j) != formalName {
            error := Some("Formal extern names were supposed to be numeric but got " + formalName + " instead of " + Strings.OfNat(j));
            isNumeric := false;
          }
          if c.isCo {
            ctorArgs := ctorArgs + [
              R.Field(R.PRIV,
                      R.Formal(formalName,
                               R.TypeApp(R.dafny_runtime.MSel("LazyFieldWrapper").AsType(), [formalType])))];
          } else {
            ctorArgs := ctorArgs + [
              R.Field(R.PRIV,
                      R.Formal(formalName, formalType))];
          }
        }
        var namedFields := R.NamedFields(ctorArgs);
        if isNumeric {
          namedFields := namedFields.ToNamelessFields();
        }
        ctors := ctors + [R.EnumCase(escapeName(ctor.name), namedFields)];
      }
      var unusedTypeParams := (set tp <- rTypeParamsDecls :: tp.name) - usedTypeParams;

      var selfPath := [Ident.Ident(c.name)];
      var implBodyRaw, traitBodies :=
        GenClassImplBody(
          c.body, false,
          UserDefined(
            ResolvedType(
              selfPath,
              typeParamsSeq,
              ResolvedTypeBase.Datatype(variances),
              c.attributes, [], [])),
          typeParamsSeq);
      var implBody: seq<R.ImplMember> := implBodyRaw;
      var emittedFields: set<string> := {};
      for i := 0 to |c.ctors| {
        // we know that across all ctors, each any fields with the same name have the same type
        // so we want to emit methods for each field that pull the appropriate value given
        // the current variant (and panic if we have a variant with no such field)
        var ctor := c.ctors[i];
        for j := 0 to |ctor.args| {
          var dtor := ctor.args[j];
          var callName := dtor.callName.GetOr(escapeVar(dtor.formal.name));
          if !(callName in emittedFields) {
            emittedFields := emittedFields + {callName};

            var formalType := GenType(dtor.formal.typ, GenTypeContext.default());
            var cases: seq<R.MatchCase> := [];
            for k := 0 to |c.ctors| {
              var ctor2 := c.ctors[k];

              var pattern := datatypeName + "::" + escapeName(ctor2.name);
              var rhs: string;
              var hasMatchingField := None;
              var patternInner := "";
              var isNumeric := false;
              for l := 0 to |ctor2.args| {
                var dtor2 := ctor2.args[l];
                var patternName := escapeVar(dtor2.formal.name);
                if l == 0 && patternName == "0" {
                  isNumeric := true;
                }
                if isNumeric {
                  patternName := dtor2.callName.GetOr("v" + Strings.OfNat(l));
                }
                if dtor.formal.name == dtor2.formal.name {
                  // Note: here, we use escapeVar because the corresponding destructor uses a non-punned name
                  hasMatchingField := Some(patternName);
                }
                patternInner := patternInner + patternName + ", ";
              }
              if isNumeric {
                pattern := pattern + "(" + patternInner + ")";
              } else {
                pattern := pattern + "{" + patternInner + "}";
              }

              if hasMatchingField.Some? {
                if c.isCo {
                  rhs := "::std::ops::Deref::deref(&" + hasMatchingField.value + ".0)";
                } else {
                  rhs := hasMatchingField.value + "";
                }
              } else {
                rhs := UnreachablePanicIfVerified("field does not exist on this variant");
              }
              var ctorMatch := R.MatchCase(R.RawPattern(pattern), R.RawExpr(rhs));
              cases := cases + [ctorMatch];
            }

            if |c.typeParams| > 0 && |unusedTypeParams| > 0 {
              cases := cases + [
                R.MatchCase(R.RawPattern(datatypeName + "::_PhantomVariant(..)"), R.RawExpr(UnreachablePanicIfVerified("")))
              ];
            }

            var methodBody := R.Match(
              R.self,
              cases
            );

            implBody := implBody + [
              R.FnDecl(
                R.PUB,
                R.Fn(
                  callName,
                  [], [R.Formal.selfBorrowed], Some(R.Borrowed(formalType)),
                  "",
                  Some(methodBody)
                ))];
          }
        }
      }
      var coerceTypes: seq<R.Type> := [];
      var rCoerceTypeParams: seq<R.TypeParamDecl> := [];
      var coerceArguments: seq<R.Formal> := [];
      var coerceMap: map<Type, Type> := map[];
      var rCoerceMap: map<R.Type, R.Type> := map[];
      var coerceMapToArg: map<(R.Type, R.Type), R.Expr> := map[];
      if |c.typeParams| > 0 {
        var types: seq<R.Type> := [];
        for typeI := 0 to |c.typeParams| {
          var typeParam := c.typeParams[typeI];
          var typeArg, rTypeParamDecl := GenTypeParam(typeParam);
          var rTypeArg := GenType(typeArg, GenTypeContext.default());
          types := types + [R.TypeApp(R.std.MSel("marker").MSel("PhantomData").AsType(), [rTypeArg])];
          // Coercion arguments
          if typeI < |variances| && variances[typeI].Nonvariant? {
            coerceTypes := coerceTypes + [rTypeArg];
            continue; // We ignore nonvariant arguments
          }
          var coerceTypeParam := typeParam.(name := Ident.Ident(Name("_T" + Strings.OfNat(typeI))));
          var coerceTypeArg, rCoerceTypeParamDecl := GenTypeParam(coerceTypeParam);
          coerceMap := coerceMap + map[typeArg := coerceTypeArg];
          var rCoerceType := GenType(coerceTypeArg, GenTypeContext.default());
          rCoerceMap := rCoerceMap + map[rTypeArg := rCoerceType];
          coerceTypes := coerceTypes + [rCoerceType];
          rCoerceTypeParams := rCoerceTypeParams + [rCoerceTypeParamDecl];
          var coerceFormal := "f_" + Strings.OfNat(typeI);
          coerceMapToArg := coerceMapToArg + map[
            (rTypeArg, rCoerceType) := R.Identifier(coerceFormal).Clone()
          ];
          coerceArguments := coerceArguments + [
            R.Formal(
              coerceFormal,
              R.Rc(R.IntersectionType(R.ImplType(R.FnType([rTypeArg], rCoerceType)), R.StaticTrait)))
          ];
        }
        if |unusedTypeParams| > 0 {
          ctors := ctors + [
            R.EnumCase(
              "_PhantomVariant",
              R.NamelessFields(
                Std.Collections.Seq.Map(
                  tpe => R.NamelessField(R.PRIV, tpe), types))
            )];
        }
      }

      var cIsEq := DatatypeIsEq(c);

      // Derive PartialEq when c supports equality / derive Clone in all cases
      s :=
        [R.EnumDecl(
           R.Enum(
             if cIsEq then
               [R.RawAttribute("#[derive(PartialEq, Clone)]")]
             else
               [R.RawAttribute("#[derive(Clone)]")],
             datatypeName,
             rTypeParamsDecls,
             ctors
           )),
         R.ImplDecl(
           R.Impl(
             rTypeParamsDecls,
             R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
             whereConstraints,
             implBody
           ))];

      var printImplBodyCases: seq<R.MatchCase> := [];
      var hashImplBodyCases: seq<R.MatchCase> := [];
      var coerceImplBodyCases: seq<R.MatchCase> := [];

      for i := 0 to |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := escapeName(ctor.name);

        var modulePrefix := if c.enclosingModule.id.dafny_name == "_module" then "" else c.enclosingModule.id.dafny_name + ".";
        var ctorName := modulePrefix + c.name.dafny_name + "." + ctor.name.dafny_name;
        if |ctorName| >= 13 && ctorName[0..13] == "_System.Tuple" {
          ctorName := "";
        }
        var printRhs :=
          R.RawExpr("write!(_formatter, \"" + ctorName + (if ctor.hasAnyArgs then "(\")?" else "\")?"));
        var hashRhs := R.RawExpr("");
        var coerceRhsArgs := [];

        var isNumeric := false;
        var ctorMatchInner := "";
        for j := 0 to |ctor.args| {
          var dtor := ctor.args[j];
          var patternName := escapeVar(dtor.formal.name);
          var formalType := dtor.formal.typ;
          if j == 0 && patternName == "0" {
            isNumeric := true;
          }
          if isNumeric {
            patternName := dtor.callName.GetOr("v" + Strings.OfNat(j));
          }
          hashRhs :=
            if formalType.Arrow? then
              hashRhs.Then(R.LiteralInt("0").Sel("hash").Apply1(R.Identifier("_state")))
            else
              hashRhs.Then(R.std.MSel("hash").MSel("Hash").MSel("hash").AsExpr().Apply([R.Identifier(patternName), R.Identifier("_state")]));

          ctorMatchInner := ctorMatchInner + patternName + ", ";

          if (j > 0) {
            printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \", \")?"));
          }

          printRhs := printRhs.Then(
            R.RawExpr(
              if formalType.Arrow? then
                "write!(_formatter, \"<function>\")?"
              else
                "::dafny_runtime::DafnyPrint::fmt_print(" + patternName + ", _formatter, false)?"
            ));

          var coerceRhsArg: R.Expr;

          //var formalTpe := GenType(formalType, GenTypeContext.default());
          //var newFormalType :=
          var formalTpe := GenType(formalType, GenTypeContext.default());

          var newFormalType := formalType.Replace(coerceMap);
          var newFormalTpe := formalTpe.ReplaceMap(rCoerceMap);

          var upcastConverter := UpcastConversionLambda(formalType, formalTpe, newFormalType, newFormalTpe, coerceMapToArg);
          if upcastConverter.Success? {
            var coercionFunction := upcastConverter.value;
            coerceRhsArg := coercionFunction.Apply1(R.Identifier(patternName));
          } else {
            error := Some("Could not generate coercion function for contructor " + Strings.OfNat(j) + " of " + datatypeName);
            coerceRhsArg := R.Identifier("todo!").Apply1(R.LiteralString(error.value, false, false));
          }

          coerceRhsArgs := coerceRhsArgs + [R.AssignIdentifier(patternName, coerceRhsArg)];
        }
        var coerceRhs := R.StructBuild(R.Identifier(datatypeName).FSel(escapeName(ctor.name)),
                                       coerceRhsArgs);

        if isNumeric {
          ctorMatch := ctorMatch + "(" + ctorMatchInner + ")";
        } else {
          ctorMatch := ctorMatch + "{" + ctorMatchInner + "}";
        }

        if (ctor.hasAnyArgs) {
          printRhs := printRhs.Then(R.RawExpr("write!(_formatter, \")\")?"));
        }

        printRhs := printRhs.Then(R.RawExpr("Ok(())"));

        printImplBodyCases := printImplBodyCases + [
          R.MatchCase(R.RawPattern(datatypeName + "::" + ctorMatch),
                      R.Block(printRhs))
        ];
        hashImplBodyCases := hashImplBodyCases + [
          R.MatchCase(R.RawPattern(datatypeName + "::" + ctorMatch),
                      R.Block(hashRhs))
        ];
        coerceImplBodyCases := coerceImplBodyCases + [
          R.MatchCase(R.RawPattern(datatypeName + "::" + ctorMatch),
                      R.Block(coerceRhs))
        ];
      }

      if |c.typeParams| > 0 && |unusedTypeParams| > 0 {
        var extraCases := [
          R.MatchCase(R.RawPattern(datatypeName + "::_PhantomVariant(..)"), R.RawExpr("{"+UnreachablePanicIfVerified()+"}"))
        ];
        printImplBodyCases := printImplBodyCases + extraCases;
        hashImplBodyCases := hashImplBodyCases + extraCases;
        coerceImplBodyCases := coerceImplBodyCases + extraCases;
      }
      var defaultConstrainedTypeParams := R.TypeParamDecl.AddConstraintsMultiple(
        rTypeParamsDecls, [R.DefaultTrait]
      );
      var rTypeParamsDeclsWithEq := R.TypeParamDecl.AddConstraintsMultiple(
        rTypeParamsDecls, [R.Eq]
      );
      var rTypeParamsDeclsWithHash := R.TypeParamDecl.AddConstraintsMultiple(
        rTypeParamsDecls, [R.Hash]
      );
      var printImplBody := R.Match(
        R.self,
        printImplBodyCases);
      var hashImplBody := R.Match(
        R.self,
        hashImplBodyCases
      );

      // Implementation of Debug and Print traits
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.std.MSel("fmt").MSel("Debug").AsType(),
            R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
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
                       .MSel("fmt_print")
                       .AsExpr()
                       .Apply(
                         [ R.self,
                           R.Identifier("f"),
                           R.LiteralBool(true)
                         ])))
              )
            ]
          )),
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.DafnyPrint,
            R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
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
      ];
      if |rCoerceTypeParams| > 0 {
        var coerceImplBody := R.Match(
          R.Identifier("this"),
          coerceImplBodyCases);
        s := s + [
          R.ImplDecl(
            R.Impl(
              rTypeParamsDecls,
              R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
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
                           [R.TypeApp(R.TIdentifier(datatypeName), rTypeParams)],
                           R.TypeApp(R.TIdentifier(datatypeName), coerceTypes))))),
                   "",
                   Some(
                     R.RcNew(R.Lambda([R.Formal("this", R.SelfOwned)],
                                      Some(R.TypeApp(R.TIdentifier(datatypeName), coerceTypes)),
                                      coerceImplBody)))))]
            ))
        ];
      }

      // Implementation of Eq when c supports equality
      if cIsEq {
        s := s + [R.ImplDecl(
                    R.ImplFor(
                      rTypeParamsDeclsWithEq,
                      R.Eq,
                      R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
                      "",
                      []
                    )
                  )];
      }

      // Implementation of Hash trait
      s := s + [R.ImplDecl(
                  R.ImplFor(
                    rTypeParamsDeclsWithHash,
                    R.Hash,
                    R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
                    "",
                    [R.FnDecl(
                       R.PRIV,
                       R.Fn(
                         "hash", [R.TypeParamDecl("_H", [R.std.MSel("hash").MSel("Hasher").AsType()])],
                         [R.Formal.selfBorrowed,
                          R.Formal("_state", R.BorrowedMut(R.TIdentifier("_H")))],
                         None,
                         "",
                         Some(hashImplBody)))]
                  )
                )];

      if |c.ctors| > 0 {
        var structName := R.Identifier(datatypeName).FSel(escapeName(c.ctors[0].name));
        var structAssignments: seq<R.AssignIdentifier> := [];
        for i := 0 to |c.ctors[0].args| {
          var dtor := c.ctors[0].args[i];
          structAssignments := structAssignments + [
            R.AssignIdentifier(escapeVar(dtor.formal.name), R.RawExpr("::std::default::Default::default()"))
          ];
        }
        var defaultConstrainedTypeParams := R.TypeParamDecl.AddConstraintsMultiple(
          rTypeParamsDecls, [R.DefaultTrait]
        );
        var fullType := R.TypeApp(R.TIdentifier(datatypeName), rTypeParams);

        // Implementation of Default trait when c supports equality
        if cIsEq {
          s := s +
          [R.ImplDecl(
             R.ImplFor(
               defaultConstrainedTypeParams,
               R.DefaultTrait,
               fullType,
               "",
               [R.FnDecl(
                  R.PRIV,
                  R.Fn(
                    "default", [], [], Some(fullType),
                    "",
                    Some(
                      R.StructBuild(
                        structName,
                        structAssignments
                      )))
                )]
             ))];
        }

        // Implementation of AsRef trait
        s := s + [
          R.ImplDecl(
            R.ImplFor(
              rTypeParamsDecls,
              R.std.MSel("convert").MSel("AsRef").AsType().Apply1(fullType),
              R.Borrowed(fullType),
              "",
              [R.FnDecl(
                 R.PRIV,
                 R.Fn("as_ref", [], [R.Formal.selfBorrowed], Some(R.SelfOwned),
                      "",
                      Some(R.self))
               )]
            ))];
      }
    }

    static method GenPath(p: seq<Ident>, escape: bool := true) returns (r: R.Path) {
      if |p| == 0 {
        return R.Self();
      } else {
        r :=
          if p[0].id.dafny_name == "std" then
            R.Global()
          else if p[0].id.dafny_name == "_System" then
            R.dafny_runtime
          else
            thisFile;
        for i := 0 to |p| {
          var name := p[i].id;
          if escape {
            var (modules, finalName) := DafnyNameToContainingPathAndName(name);
            for j := 0 to |modules| {
              r := r.MSel(escapeName(modules[j].id));
            }
            r := r.MSel(escapeName(finalName));
          } else {
            // TODO: Try removing this else branch and the escape test.
            r := r.MSel(ReplaceDotByDoubleColon(name.dafny_name));
          }
        }
      }
    }

    static method GenPathType(p: seq<Ident>) returns (t: R.Type) {
      var p := GenPath(p, true);
      t := p.AsType();
    }

    static method GenPathExpr(p: seq<Ident>, escape: bool := true) returns (e: R.Expr) {
      if |p| == 0 {
        return R.self;
      }
      var p := GenPath(p, escape);
      e := p.AsExpr();
    }

    method GenTypeArgs(args: seq<Type>, genTypeContext: GenTypeContext) returns (s: seq<R.Type>) {
      s := [];
      for i := 0 to |args| {
        var genTp := GenType(args[i], genTypeContext);
        s := s + [genTp];
      }
    }

    predicate IsRcWrapped(attributes: seq<Attribute>) {
      (Attribute("auto-nongrowing-size", []) !in attributes &&
       Attribute("rust_rc", ["false"]) !in attributes) ||
      Attribute("rust_rc", ["true"]) in attributes
    }

    /** The type context is useful in the case when we need to generate a type
        in a position that requires a variant of the given type.

        For now, it makes it possible to ensure that:
        GenType(UserDefined(ResolveType(["U"], Trait()), ForTrait()) == U

        but

        GenType(UserDefined(ResolveType(["U"], Trait()), default()) == Object<dyn U>
     
        so that we can generate U instead of Object<dyn U> in the following context:

        trait U: Any {}
        trait T: Any + U {}

        The last U is obtained with GenType() with GenTypeContext(forTraitParents := true)
        Otherwise, we would have had Object<dyn U>, which is not a trait type.
     */
    method GenType(c: Type, genTypeContext: GenTypeContext) returns (s: R.Type) {
      match c {
        case UserDefined(resolved) => {
          var t := GenPathType(resolved.path);
          var typeArgs := GenTypeArgs(resolved.typeArgs, genTypeContext.(forTraitParents := false));
          s := R.TypeApp(t, typeArgs);

          match resolved.kind {
            case Class() => {
              s := Object(s);
            }
            case Datatype(_) => {
              if IsRcWrapped(resolved.attributes) {
                s := R.Rc(s);
              }
            }
            case Trait() => {
              if resolved.path == [Ident.Ident(Name("_System")), Ident.Ident(Name("object"))] {
                s := R.AnyTrait;
              }
              if !genTypeContext.forTraitParents {
                s := Object(R.DynType(s));
              }
            }
            case Newtype(base, range, erased) => {
              if erased {
                match NewtypeRangeToRustType(range) {
                  case Some(v) =>
                    s := v;
                  case None =>
                    var underlying := GenType(base, GenTypeContext.default());
                    s := R.TSynonym(s, underlying);
                }
              }
            }
          }
        }
        case Object() => {
          s := R.AnyTrait;
          if !genTypeContext.forTraitParents {
            s := Object(R.DynType(s));
          }
        }
        case Tuple(types) => {
          var args := [];
          var i := 0;
          while i < |types| {
            var generated := GenType(types[i], genTypeContext.(forTraitParents := false));
            args := args + [generated];
            i := i + 1;
          }
          s := if |types| <= R.MAX_TUPLE_SIZE then R.TupleType(args) else R.SystemTupleType(args);
        }
        case Array(element, dims) => {
          if dims > 16 {
            s := R.RawType("<i>Array of dimensions greater than 16</i>");
          } else {
            var elem := GenType(element, genTypeContext.(forTraitParents := false));
            if dims == 1 {
              s := R.Array(elem, None);
              s := Object(s);
            } else {
              var n := "Array" + Strings.OfNat(dims);
              s := R.dafny_runtime.MSel(n).AsType().Apply([elem]);
              s := Object(s);
            }
          }
        }
        case Seq(element) => {
          var elem := GenType(element, genTypeContext.(forTraitParents := false));
          s := R.TypeApp(R.dafny_runtime.MSel("Sequence").AsType(), [elem]);
        }
        case Set(element) => {
          var elem := GenType(element, genTypeContext.(forTraitParents := false));
          s := R.TypeApp(R.dafny_runtime.MSel("Set").AsType(), [elem]);
        }
        case Multiset(element) => {
          var elem := GenType(element, genTypeContext.(forTraitParents := false));
          s := R.TypeApp(R.dafny_runtime.MSel("Multiset").AsType(), [elem]);
        }
        case Map(key, value) => {
          var keyType := GenType(key, genTypeContext.(forTraitParents := false));
          var valueType := GenType(value, genTypeContext);
          s := R.TypeApp(R.dafny_runtime.MSel("Map").AsType(), [keyType, valueType]);
        }
        case MapBuilder(key, value) => {
          var keyType := GenType(key, genTypeContext.(forTraitParents := false));
          var valueType := GenType(value, genTypeContext);
          s := R.TypeApp(R.dafny_runtime.MSel("MapBuilder").AsType(), [keyType, valueType]);
        }
        case SetBuilder(elem) => {
          var elemType := GenType(elem, genTypeContext.(forTraitParents := false));
          s := R.TypeApp(R.dafny_runtime.MSel("SetBuilder").AsType(), [elemType]);
        }
        case Arrow(args, result) => {
          var argTypes := [];
          var i := 0;
          while i < |args| {

            var generated := GenType(args[i], genTypeContext.(forTraitParents := false));
            argTypes := argTypes + [R.Borrowed(generated)];
            i := i + 1;
          }

          var resultType := GenType(result, GenTypeContext.default());
          s :=
            R.Rc(R.DynType(R.FnType(argTypes, resultType)));
        }
        case TypeArg(Ident(name)) => s := R.TIdentifier(escapeName(name));
        case Primitive(p) => {
          match p {
            case Int => s := R.dafny_runtime.MSel("DafnyInt").AsType();
            case Real => s := R.dafny_runtime.MSel("BigRational").AsType();
            case String => s := R.TypeApp(R.dafny_runtime.MSel("Sequence").AsType(),
                                          [R.dafny_runtime.MSel(DafnyChar).AsType()]);
            case Bool => s := R.Type.Bool;
            case Char => s := R.dafny_runtime.MSel(DafnyChar).AsType();
          }
        }
        case Passthrough(v) => s := R.RawType(v);
      }
    }

    predicate EnclosingIsTrait(tpe: Type) {
      tpe.UserDefined? && tpe.resolved.kind.Trait?
    }

    method GenClassImplBody(body: seq<ClassItem>, forTrait: bool, enclosingType: Type, enclosingTypeParams: seq<Type>)
      returns (s: seq<R.ImplMember>, traitBodies: map<seq<Ident>, seq<R.ImplMember>>)
      modifies this
    {
      s := [];
      traitBodies := map[];

      for i := 0 to |body| {
        match body[i] {
          case Method(m) => {
            match m.overridingPath {
              case Some(p) => {
                var existing: seq<R.ImplMember> := [];
                if p in traitBodies {
                  existing := traitBodies[p];
                }
                if |m.typeParams| > 0 && EnclosingIsTrait(enclosingType) {
                  error := Some("Error: Rust does not support method with generic type parameters in traits");
                }

                var genMethod := GenMethod(m, true, enclosingType, enclosingTypeParams);
                existing := existing + [genMethod];

                traitBodies := traitBodies + map[p := existing];
              }
              case None => {
                var generated := GenMethod(m, forTrait, enclosingType, enclosingTypeParams);
                s := s + [generated];
              }
            }
          }
        }
      }
    }

    // Transform DAST formals to Rust formals
    method GenParams(params: seq<Formal>, forLambda: bool := false) returns (s: seq<R.Formal>)
      ensures |s| == |params|
    {
      s := [];
      for i := 0 to |params| invariant |s| == i && i <= |params| {
        var param := params[i];
        var paramType := GenType(param.typ, GenTypeContext.default());
        if (!paramType.CanReadWithoutClone() || forLambda) && AttributeOwned !in param.attributes {
          paramType := R.Borrowed(paramType);
        }
        s := s + [R.Formal(escapeVar(param.name), paramType)];
      }
    }

    method GenMethod(m: Method, forTrait: bool, enclosingType: Type, enclosingTypeParams: seq<Type>) returns (s: R.ImplMember)
      modifies this
    {
      var params: seq<R.Formal> := GenParams(m.params);
      var paramNames := [];
      var paramTypes := map[];
      for paramI := 0 to |m.params| {
        var dafny_formal := m.params[paramI];
        var formal := params[paramI];
        var name := formal.name;
        paramNames := paramNames + [name];
        paramTypes := paramTypes[name := formal.tpe];
      }
      var fnName := escapeName(m.name);

      var selfIdent := NoSelf;

      if (!m.isStatic) {
        var selfId := "self";
        if m.outVarsAreUninitFieldsToAssign {
          // Constructors take a raw pointer, which is not accepted as a self type in Rust
          selfId := "this";
        }
        var instanceType := match enclosingType {
          case UserDefined(r) =>
            UserDefined(r.(typeArgs := enclosingTypeParams))
          case _ => enclosingType
        };
        if (forTrait) {
          // Mutability is required when not using raw pointers, even for functione, because
          // --release optimisations sometimes removes the code to increment the reference counting on upcasting
          var selfFormal := if m.wasFunction && ObjectType.RawPointers? then R.Formal.selfBorrowed else R.Formal.selfBorrowedMut;
          params := [selfFormal] + params;
        } else {
          var tpe := GenType(instanceType, GenTypeContext.default());
          if selfId == "this" {
            if pointerType.RcMut? {
              tpe := R.Borrowed(tpe);
            }
            // For raw pointers, no borrowing is necessary, because it implements the Copy type
          } else if selfId == "self" {
            if tpe.IsObjectOrPointer() { // For classes and traits
              if m.wasFunction && ObjectType.RawPointers? {
                tpe := R.SelfBorrowed;
              } else {
                tpe := R.SelfBorrowedMut;
              }
            } else { // For Rc-defined datatypes
              if enclosingType.UserDefined? && enclosingType.resolved.kind.Datatype?
                 && IsRcWrapped(enclosingType.resolved.attributes) {
                tpe := R.Borrowed(R.Rc(R.SelfOwned));
              } else { // For raw-defined datatypes, newtypes
                tpe := R.Borrowed(R.SelfOwned);
              }
            }
          }
          params := [R.Formal(selfId, tpe)] + params;
        }
        selfIdent := ThisTyped(selfId, instanceType);
      }

      // TODO: Use mut instead of a tuple for the API of multiple output parameters
      var retTypeArgs := [];
      //var retType := if |m.outTypes| != 1 then "(" else "";

      var typeI := 0;
      while typeI < |m.outTypes| {
        var typeExpr := GenType(m.outTypes[typeI], GenTypeContext.default());
        retTypeArgs := retTypeArgs + [typeExpr];

        typeI := typeI + 1;
      }

      var visibility := if forTrait then R.PRIV else R.PUB;

      var typeParamsFiltered := [];
      for typeParamI := 0 to |m.typeParams| {
        var typeParam := m.typeParams[typeParamI];
        if !(TypeArg(typeParam.name) in enclosingTypeParams) {
          typeParamsFiltered := typeParamsFiltered + [typeParam];
        }
      }

      var typeParams: seq<R.TypeParamDecl> := [];

      if (|typeParamsFiltered| > 0) {
        for i := 0 to |typeParamsFiltered| {
          var typeArg, rTypeParamDecl := GenTypeParam(typeParamsFiltered[i]);
          rTypeParamDecl := rTypeParamDecl.(constraints := rTypeParamDecl.constraints);
          typeParams := typeParams + [rTypeParamDecl];
        }
      }

      var fBody: Option<R.Expr>;
      var env: Environment;
      var preBody := R.RawExpr("");
      var preAssignNames: seq<string> := [];
      var preAssignTypes: map<string, R.Type> := map[];

      if m.hasBody {
        var earlyReturn: Option<seq<string>> := None;
        match m.outVars {
          case Some(outVars) => {
            if m.outVarsAreUninitFieldsToAssign {
              earlyReturn := Some([]);
              for outI := 0 to |outVars| {
                var outVar := outVars[outI];
                var outName := escapeVar(outVar);
                var tracker_name := AddAssignedPrefix(outName);
                preAssignNames := preAssignNames + [tracker_name];
                preAssignTypes := preAssignTypes[tracker_name := R.Type.Bool];

                preBody := preBody.Then(R.DeclareVar(R.MUT, tracker_name, Some(R.Type.Bool), Some(R.LiteralBool(false))));
              }
            } else {
              var tupleArgs := [];
              assume {:axiom} |m.outTypes| == |outVars|;

              for outI := 0 to |outVars| {
                var outVar := outVars[outI];
                var outType := GenType(m.outTypes[outI], GenTypeContext.default());
                var outName := escapeVar(outVar);
                paramNames := paramNames + [outName];
                var outMaybeType := if outType.CanReadWithoutClone() then outType else R.MaybePlaceboType(outType);
                paramTypes := paramTypes[outName := outMaybeType];

                tupleArgs := tupleArgs + [outName];
              }
              earlyReturn := Some(tupleArgs);
            }
          }
          case None => {}
        }
        env := Environment(preAssignNames + paramNames, preAssignTypes + paramTypes);

        var body, _, _ := GenStmts(m.body, selfIdent, env, true, earlyReturn);

        fBody := Some(preBody.Then(body));
      } else {
        env := Environment(paramNames, paramTypes);
        fBody := None;
      }
      s := R.FnDecl(
        visibility,
        R.Fn(
          fnName,
          typeParams,
          params,
          Some(if |retTypeArgs| == 1 then retTypeArgs[0] else R.TupleType(retTypeArgs)),
          "",
          fBody
        )
      );
    }

    method GenStmts(stmts: seq<Statement>, selfIdent: SelfInfo, env: Environment, isLast: bool, earlyReturn: Option<seq<string>>)
      returns (generated: R.Expr, readIdents: set<string>, newEnv: Environment)
      decreases stmts, 1, 0
      modifies this
    {
      generated := R.RawExpr("");
      var declarations := {};
      readIdents := {};
      var i := 0;
      newEnv := env;
      ghost var oldStmts := stmts;
      var stmts := stmts; // Make it mutable
      while i < |stmts| {
        var stmt := stmts[i];
        // Avoid lazy initialization if it is not necessary
        match stmt {
          case DeclareVar(name, optType, None) =>
            if i + 1 < |stmts| {
              match stmts[i + 1] {
                case Assign(Ident(name2), rhs) =>
                  if name2 == name {
                    stmts := stmts[0..i] + [DeclareVar(name, optType, Some(rhs))] + stmts[i+2..];
                    stmt := stmts[i];
                  }
                case _ =>
              }
            }
          case _ =>

        }
        assume {:axiom} stmt in oldStmts;
        var stmtExpr, recIdents, newEnv2 := GenStmt(stmt, selfIdent, newEnv, isLast && (i == |stmts| - 1), earlyReturn);
        newEnv := newEnv2;

        match stmt {
          case DeclareVar(name, _, _) => {
            declarations := declarations + {escapeVar(name)};
          }
          case _ => {}
        }
        readIdents := readIdents + (recIdents - declarations);
        generated := generated.Then(stmtExpr);

        i := i + 1;
        if stmtExpr.Return? { // The rest of statements is unreachable
          break;
        }
      }
    }

    method GenAssignLhs(lhs: AssignLhs, rhs: R.Expr, selfIdent: SelfInfo, env: Environment) returns (generated: R.Expr, needsIIFE: bool, readIdents: set<string>, newEnv: Environment)
      decreases lhs, 1
      modifies this
    {
      newEnv := env;
      match lhs {
        case Ident(id) => {
          var idRust := escapeVar(id);
          if env.IsBorrowed(idRust) || env.IsBorrowedMut(idRust) {
            generated := R.AssignVar("*" + idRust, rhs);
          } else {
            generated := R.AssignVar(idRust, rhs);
          }

          readIdents := {idRust};
          needsIIFE := false;
        }

        case Select(on, field) => {
          var fieldName := escapeVar(field);
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

          match onExpr { // Particular case of the constructor, we don't want the previous value to be dropped if it's assigned the first time
            case Call(Select(Identifier("this"), "clone"), _)
              | Identifier("this")
              | UnaryOp("&", Identifier("this"), _) =>
              var isAssignedVar := AddAssignedPrefix(fieldName);
              if isAssignedVar in newEnv.names {
                generated := R.dafny_runtime.MSel(update_field_uninit_macro).AsExpr().Apply(
                  [ thisInConstructor,
                    R.Identifier(fieldName),
                    R.Identifier(isAssignedVar),
                    rhs]);
                newEnv := newEnv.RemoveAssigned(isAssignedVar);
              } else {
                error := Some("Unespected field to assign whose isAssignedVar is not in the environment: " + isAssignedVar);
                generated :=
                  R.AssignMember(R.RawExpr(error.value), fieldName, rhs);
              }
            case _ =>
              if onExpr != R.Identifier("self") {
                onExpr := modify_macro.Apply1(onExpr);
              }
              generated :=
                R.AssignMember(onExpr, fieldName, rhs);
          }
          readIdents := recIdents;
          needsIIFE := false;
        }

        case Index(on, indices) => {
          // Retrieve the pointer to the array
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;

          onExpr := modify_macro.Apply1(onExpr);

          var r := R.RawExpr("");

          var indicesExpr := [];
          for i := 0 to |indices| {
            var idx, _, recIdentsIdx := GenExpr(indices[i], selfIdent, env, OwnershipOwned);
            var varName := "__idx" + Strings.OfNat(i);
            indicesExpr := indicesExpr + [R.Identifier(varName)];
            r := r.Then(
              R.DeclareVar(
                R.CONST, varName, None,
                Some(
                  R.IntoUsize(idx))));
            readIdents := readIdents + recIdentsIdx;
          }

          if |indices| > 1 { // Multi-dimensional arrays
            onExpr := onExpr.Sel("data");
          }

          generated := r.Then(R.Assign(Some(R.Index(onExpr, indicesExpr)), rhs));
          needsIIFE := true;
        }
      }
    }

    method GenStmt(stmt: Statement, selfIdent: SelfInfo, env: Environment, isLast: bool, earlyReturn: Option<seq<string>>) returns (generated: R.Expr, readIdents: set<string>, newEnv: Environment)
      decreases stmt, 1, 1
      modifies this
    {
      match stmt {
        case ConstructorNewSeparator(fields) => {
          generated := R.RawExpr("");
          readIdents := {};
          newEnv := env;
          for i := 0 to |fields| {
            var field := fields[i];
            var fieldName := escapeVar(field.name);
            var fieldTyp := GenType(field.typ, GenTypeContext.default());
            var isAssignedVar := AddAssignedPrefix(fieldName);
            if isAssignedVar in newEnv.names {
              assume {:axiom} InitializationValue(field.typ) < stmt; // Needed for termination
              var rhs, _, _ := GenExpr(InitializationValue(field.typ), selfIdent, env, OwnershipOwned);
              readIdents := readIdents + {isAssignedVar};
              generated := generated.Then(R.dafny_runtime.MSel(update_field_if_uninit_macro).AsExpr().Apply([
                                                                                                              R.Identifier("this"), R.Identifier(fieldName), R.Identifier(isAssignedVar), rhs]));
              newEnv := newEnv.RemoveAssigned(isAssignedVar);
            }
          }
        }
        case DeclareVar(name, typ, Some(expression)) => {
          var tpe := GenType(typ, GenTypeContext.default());
          var varName := escapeVar(name);
          var hasCopySemantics := tpe.CanReadWithoutClone();
          if expression.InitializationValue? && !hasCopySemantics {
            generated := R.DeclareVar(R.MUT, varName, None, Some(R.MaybePlaceboPath.AsExpr().ApplyType1(tpe).FSel("new").Apply([])));
            readIdents := {};
            newEnv := env.AddAssigned(varName, R.MaybePlaceboType(tpe));
          } else {
            var expr, recIdents;
            if expression.InitializationValue? &&
               tpe.IsObjectOrPointer() {
              expr := tpe.ToNullExpr();
              recIdents := {};
            } else {
              var exprOwnership;
              expr, exprOwnership, recIdents := GenExpr(expression, selfIdent, env, OwnershipOwned);
            }
            readIdents := recIdents;
            tpe := if expression.NewUninitArray? then tpe.TypeAtInitialization() else tpe;
            generated := R.DeclareVar(R.MUT, varName, Some(tpe), Some(expr));
            newEnv := env.AddAssigned(varName, tpe);
          }
        }
        case DeclareVar(name, typ, None) => {
          var newStmt := DeclareVar(name, typ, Some(InitializationValue(typ)));
          assume {:axiom} newStmt < stmt;
          generated, readIdents, newEnv := GenStmt(newStmt, selfIdent, env, isLast, earlyReturn);
        }
        case Assign(lhs, expression) => {
          var exprGen, _, exprIdents := GenExpr(expression, selfIdent, env, OwnershipOwned);
          if lhs.Ident? {
            var rustId := escapeVar(lhs.ident);
            var tpe := env.GetType(rustId);
            if tpe.Some? && tpe.value.ExtractMaybePlacebo().Some? {
              exprGen := R.MaybePlacebo(exprGen);
            }
          }
          if lhs.Index? && lhs.expr.Ident? {
            var rustId := escapeVar(lhs.expr.name);
            var tpe := env.GetType(rustId);
            if tpe.Some? && tpe.value.ExtractMaybeUninitArrayElement().Some? {
              exprGen := R.MaybeUninitNew(exprGen);
            }
          }
          var lhsGen, needsIIFE, recIdents, resEnv := GenAssignLhs(lhs, exprGen, selfIdent, env);
          generated := lhsGen;
          newEnv := resEnv;

          if needsIIFE {
            generated := R.Block(generated);
          }
          readIdents := recIdents + exprIdents;
        }
        case If(cond, thnDafny, elsDafny) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, env, OwnershipOwned);
          var condString := cond.ToString(IND);

          readIdents := recIdents;
          var thn, thnIdents, thnEnv := GenStmts(thnDafny, selfIdent, env, isLast, earlyReturn);
          readIdents := readIdents + thnIdents;
          var els, elsIdents, elsEnv := GenStmts(elsDafny, selfIdent, env, isLast, earlyReturn);
          readIdents := readIdents + elsIdents;
          newEnv := env;
          generated := R.IfExpr(cond, thn, els);
        }
        case Labeled(lbl, body) => {
          var body, bodyIdents, env2 := GenStmts(body, selfIdent, env, isLast, earlyReturn);
          readIdents := bodyIdents;
          generated := R.Labelled("label_" + lbl, R.Loop(None, R.StmtExpr(body, R.Break(None))));
          newEnv := env;
        }
        case While(cond, body) => {
          var cond, _, recIdents := GenExpr(cond, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;

          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, selfIdent, env, false, earlyReturn);

          newEnv := env;
          readIdents := readIdents + bodyIdents;
          generated := R.Loop(Some(cond), bodyExpr);
        }
        case Foreach(boundName, boundType, overExpr, body) => {
          // Variables are usually owned, so we request OwnershipOwned here although it's for each variable.
          var over, _, recIdents := GenExpr(overExpr, selfIdent, env, OwnershipOwned);
          if overExpr.MapBoundedPool? || overExpr.SetBoundedPool? {
            over := over.Sel("cloned").Apply([]);
          }

          var boundTpe := GenType(boundType, GenTypeContext.default());

          readIdents := recIdents;
          var boundRName: string := escapeVar(boundName);
          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, selfIdent, env.AddAssigned(boundRName, boundTpe), false, earlyReturn);
          readIdents := readIdents + bodyIdents - {boundRName};
          newEnv := env;
          generated := R.For(boundRName, over, bodyExpr);
        }
        case Break(toLabel) => {
          match toLabel {
            case Some(lbl) => {
              generated := R.Break(Some("label_" + lbl));
            }
            case None => {
              generated := R.Break(None);
            }
          }
          readIdents := {};
          newEnv := env;
        }
        case TailRecursive(body) => {
          // clone the parameters to make them mutable
          generated := R.RawExpr("");

          if selfIdent != NoSelf {
            var selfClone, _, _ := GenIdent(selfIdent.rSelfName, selfIdent, Environment.Empty(), OwnershipOwned);
            generated := generated.Then(R.DeclareVar(R.MUT, "_this", None, Some(selfClone)));
          }
          newEnv := env;
          for paramI := 0 to |env.names| {
            var param := env.names[paramI];
            var paramInit, _, _ := GenIdent(param, selfIdent, env, OwnershipOwned);
            generated := generated.Then(R.DeclareVar(R.MUT, param, None, Some(paramInit)));
            if param in env.types {
              // We made the input type owned by the variable.
              // so we can remove borrow annotations.
              var declaredType := env.types[param].ToOwned();
              newEnv := newEnv.AddAssigned(param, declaredType);
            }
          }
          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, if selfIdent != NoSelf then ThisTyped("_this", selfIdent.dafnyType) else NoSelf, newEnv, false, earlyReturn);
          readIdents := bodyIdents;
          generated := generated.Then(
            R.Labelled("TAIL_CALL_START",
                       R.Loop(None, bodyExpr)));
        }
        case JumpTailCallStart() => {
          generated := R.Continue(Some("TAIL_CALL_START"));
          readIdents := {};
          newEnv := env;
        }
        case Call(on, name, typeArgs, args, maybeOutVars) => {
          assume {:axiom} (if |args| > 0 then args[0] else Expression.Tuple([])) < stmt;
          var argExprs, recIdents, typeExprs, fullNameQualifier := GenArgs(None, selfIdent, name, typeArgs, args, env);
          readIdents := recIdents;

          match fullNameQualifier {
            // Trait calls are fully specified as we can't guarantee traits will be in context
            case Some(ResolvedType(path, onTypeArgs, base, _, _, _)) =>
              var fullPath := GenPathExpr(path);
              var onTypeExprs := GenTypeArgs(onTypeArgs, GenTypeContext.default());
              var onExpr, recOwnership, recIdents;
              if base.Trait? || base.Class? {
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipOwned);
                onExpr := modify_macro.Apply1(onExpr);
                readIdents := readIdents + recIdents;
              } else {
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowedMut);
                readIdents := readIdents + recIdents;
              }
              generated := fullPath.ApplyType(onTypeExprs).FSel(escapeName(name.name)).ApplyType(typeExprs).Apply([onExpr] + argExprs);
            case _ => // Infix call on.name(args)
              var onExpr, _, enclosingIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
              readIdents := readIdents + enclosingIdents;
              var renderedName := GetMethodName(on, name);
              match on {
                case Companion(_, _) | ExternCompanion(_) => {
                  onExpr := onExpr.FSel(renderedName);
                }
                case _ => {
                  if onExpr != R.self { // Self has the reference type already
                    match name {
                      case CallName(_, Some(tpe), _, _, _) =>
                        var typ := GenType(tpe, GenTypeContext.default());
                        if typ.IsObjectOrPointer() && onExpr != R.Identifier("self") {
                          onExpr := modify_macro.Apply1(onExpr);
                        }
                      case _ =>
                    }
                  }
                  onExpr := onExpr.Sel(renderedName);
                }
              }
              generated := onExpr.ApplyType(typeExprs).Apply(argExprs);
          }

          if maybeOutVars.Some? && |maybeOutVars.value| == 1 {
            var outVar := escapeVar(maybeOutVars.value[0]);
            if !env.CanReadWithoutClone(outVar) {
              generated := R.MaybePlacebo(generated);
            }
            generated := R.AssignVar(outVar, generated);
          } else if maybeOutVars.None? || |maybeOutVars.value| == 0 {
            // Nothing to do here.
          } else { // Multiple variables
            var tmpVar := "_x";
            var tmpId := R.Identifier(tmpVar);
            generated := R.DeclareVar(R.CONST, tmpVar, None, Some(generated));
            // We emit assignment to each receiver depending on its type, if it could be a placebo or not.
            var outVars := maybeOutVars.value;
            for outI := 0 to |outVars| {
              var outVar := escapeVar(outVars[outI]);
              var rhs := tmpId.Sel(Strings.OfNat(outI));
              if !env.CanReadWithoutClone(outVar) {
                rhs := R.MaybePlacebo(rhs);
              }
              generated := generated.Then(R.AssignVar(outVar, rhs));
            }
          }
          newEnv := env;
        }
        case Return(exprDafny) => {
          var expr, _, recIdents := GenExpr(exprDafny, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;

          if isLast {
            generated := expr;
          } else {
            generated := R.Return(Some(expr));
          }
          newEnv := env;
        }
        case EarlyReturn() => {

          match earlyReturn {
            case None =>
              generated := R.Return(None);
            case Some(rustIdents) =>
              var tupleArgs := [];
              for i := 0 to |rustIdents| {
                var rIdent, _, _ := GenIdent(rustIdents[i], selfIdent, env, OwnershipOwned);
                tupleArgs := tupleArgs + [rIdent];
              }
              if |tupleArgs| == 1 {
                generated := R.Return(Some(tupleArgs[0]));
              } else {
                generated := R.Return(Some(R.Tuple(tupleArgs)));
              }
          }
          readIdents := {};
          newEnv := env;
        }
        case Halt() => {
          generated := R.Identifier("panic!").Apply1(R.LiteralString("Halt", false, false));
          readIdents := {};
          newEnv := env;
        }
        case Print(e) => {
          var printedExpr, recOwnership, recIdents := GenExpr(e, selfIdent, env, OwnershipBorrowed);
          generated := R.Identifier("print!").Apply([R.LiteralString("{}", false, false),
                                                     R.dafny_runtime.MSel("DafnyPrintWrapper").AsExpr().Apply1(printedExpr)]);
          readIdents := recIdents;
          newEnv := env;
        }
      }
    }

    static const OpTable: map<BinOp, string> :=
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

    static function NewtypeRangeToRustType(range: NewtypeRange)
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
        case _ => None
      }
    }

    method FromOwned(r: R.Expr, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      ensures resultingOwnership != OwnershipAutoBorrowed
      ensures expectedOwnership != OwnershipAutoBorrowed
              ==> resultingOwnership == expectedOwnership
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      if expectedOwnership == OwnershipOwnedBox {
        out := R.BoxNew(r);
        resultingOwnership := OwnershipOwnedBox;
      } else if expectedOwnership == OwnershipOwned || expectedOwnership == OwnershipAutoBorrowed {
        out := r;
        resultingOwnership := OwnershipOwned;
      } else if expectedOwnership == OwnershipBorrowed {
        out := R.Borrow(r);
        resultingOwnership := OwnershipBorrowed;
      } else {
        assert expectedOwnership == OwnershipBorrowedMut;
        out := modify_macro.Apply1(R.RawExpr(r.ToString("") + "/*TODO: Conversion from Borrowed or BorrowedMut to BorrowedMut*/"));
        resultingOwnership := OwnershipBorrowedMut;
      }
    }

    method FromOwnership(r: R.Expr, ownership: Ownership, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      requires ownership != OwnershipAutoBorrowed
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      if ownership == expectedOwnership {
        out := r;
        resultingOwnership := expectedOwnership;
        return;
      }
      if ownership == OwnershipOwned {
        out, resultingOwnership := FromOwned(r, expectedOwnership);
        return;
      } else if ownership == OwnershipOwnedBox {
        out, resultingOwnership := FromOwned(R.UnaryOp("*", r, Format.UnaryOpFormat.NoFormat), expectedOwnership);
      } else if ownership == OwnershipBorrowed || ownership == OwnershipBorrowedMut {
        if expectedOwnership == OwnershipOwned{
          resultingOwnership := OwnershipOwned;
          out := r.Clone();
        } else if expectedOwnership == OwnershipOwnedBox {
          resultingOwnership := OwnershipOwnedBox;
          out := R.BoxNew(r.Clone());
        } else if expectedOwnership == ownership
                  || expectedOwnership == OwnershipAutoBorrowed {
          resultingOwnership := ownership;
          out := r;
        } else if expectedOwnership == OwnershipBorrowed
                  && ownership == OwnershipBorrowedMut {
          resultingOwnership := OwnershipBorrowed;
          out := r;
        } else {
          assert expectedOwnership == OwnershipBorrowedMut;
          resultingOwnership := OwnershipBorrowedMut;
          out := R.BorrowMut(r); // Not sure if it will ever happen
        }
      } else {
        assert false;
      }
    }

    static predicate OwnershipGuarantee(expectedOwnership: Ownership, resultingOwnership: Ownership) {
      && (expectedOwnership != OwnershipAutoBorrowed ==>
            resultingOwnership == expectedOwnership)
      && resultingOwnership != OwnershipAutoBorrowed // We know what's going on
    }

    method GenExprLiteral(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Literal?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      match e {
        case Literal(BoolLiteral(b)) => {
          r, resultingOwnership :=
            FromOwned(R.LiteralBool(b), expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(IntLiteral(i, t)) => {
          match t {
            case Primitive(Int) => {
              if |i| <= 4 {
                r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(R.LiteralInt(i));
              } else {
                r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(
                  R.LiteralString(i, binary := true, verbatim := false));
              }
            }
            case o => {
              var genType := GenType(o, GenTypeContext.default());
              r := R.TypeAscription(R.RawExpr(i), genType);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\"" + n + "\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"" + d + "\", 10).unwrap())"));
            }
            case o => {
              var genType := GenType(o, GenTypeContext.default());
              r := R.TypeAscription(R.RawExpr("(" + n + ".0 / " + d + ".0" + ")"), genType);
            }
          }

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(StringLiteral(l, verbatim)) => {
          r := R.dafny_runtime.MSel(string_of).AsExpr().Apply1(R.LiteralString(l, binary := false, verbatim := verbatim));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(CharLiteralUTF16(c)) => {
          r := R.LiteralInt(Strings.OfNat(c));
          r := R.TypeAscription(r, R.U16);
          r := R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(CharLiteral(c)) => {
          r := R.LiteralInt(Strings.OfNat(c as nat));
          if !charType.Unicode? {
            r := R.TypeAscription(r, R.U16);
          } else {
            r :=
              R.global.MSel("std").MSel("primitive")
              .MSel("char").FSel("from_u32")
              .Apply1(r).Sel("unwrap").Apply([]);
          }
          r := R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(Null(tpe)) => {
          var tpeGen := GenType(tpe, GenTypeContext.default());
          if pointerType.Raw? {
            r := R.std.MSel("ptr").FSel("null_mut");
          } else {
            r := R.TypeAscription(R.dafny_runtime.MSel("Object").AsExpr().Apply1(R.RawExpr("None")), tpeGen);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
      }
    }

    method GenExprBinary(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.BinOp?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var BinOp(op, lExpr, rExpr, format) := e;
      var becomesLeftCallsRight := match op {
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
      };
      var becomesRightCallsLeft := match op {
        case In() => true
        case _ => false
      };
      var becomesCallLeftRight := match op {
        case Eq(true) => false
        case SetMerge() => true
        case SetSubtraction() => true
        case SetIntersection() => true
        case SetDisjoint() => true
        case MapMerge() => true
        case MapSubtraction() => true
        case MultisetMerge() => true
        case MultisetSubtraction() => true
        case MultisetIntersection() => true
        case MultisetDisjoint() => true
        case Concat() => true
        case _ => false
      };
      var expectedLeftOwnership :=
        if becomesLeftCallsRight then OwnershipAutoBorrowed
        else if becomesRightCallsLeft || becomesCallLeftRight then OwnershipBorrowed
        else OwnershipOwned;
      var expectedRightOwnership :=
        if becomesLeftCallsRight || becomesCallLeftRight then OwnershipBorrowed
        else if becomesRightCallsLeft then OwnershipAutoBorrowed
        else OwnershipOwned;
      var left, _, recIdentsL := GenExpr(lExpr, selfIdent, env, expectedLeftOwnership);
      var right, _, recIdentsR := GenExpr(rExpr, selfIdent, env, expectedRightOwnership);

      match op {
        case In() => {
          r := right.Sel("contains").Apply1(left);
        }
        case SeqProperPrefix() =>
          r := R.BinaryOp("<", left, right, format);
        case SeqPrefix() =>
          r := R.BinaryOp("<=", left, right, format);
        case SetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case SetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case SetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Subset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case SetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case MapMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MapSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetMerge() => {
          r := left.Sel("merge").Apply1(right);
        }
        case MultisetSubtraction() => {
          r := left.Sel("subtract").Apply1(right);
        }
        case MultisetIntersection() => {
          r := left.Sel("intersect").Apply1(right);
        }
        case Submultiset() => {
          r := R.BinaryOp("<=", left, right, format);
        }
        case ProperSubmultiset() => {
          r := R.BinaryOp("<", left, right, format);
        }
        case MultisetDisjoint() => {
          r := left.Sel("disjoint").Apply1(right);
        }
        case Concat() => {
          r := left.Sel("concat").Apply1(right);
        }
        case _ => {

          if op in OpTable {
            r := R.Expr.BinaryOp(
              OpTable[op],
              left,
              right,
              format);
          } else {
            match op {
              case Eq(referential) => {
                if (referential) {
                  if pointerType.Raw? {
                    error := Some("Cannot compare raw pointers yet - need to wrap them with a structure to ensure they are compared properly");
                    r := R.RawExpr(error.value);
                  } else {
                    r := R.BinaryOp("==", left, right, DAST.Format.BinaryOpFormat.NoFormat());
                  }
                } else {
                  if rExpr.SeqValue? && |rExpr.elements| == 0 {
                    r := R.BinaryOp("==", left.Sel("to_array").Apply([]).Sel("len").Apply([]), R.LiteralInt("0"), DAST.Format.BinaryOpFormat.NoFormat());
                  } else if lExpr.SeqValue? && |lExpr.elements| == 0 {
                    r := R.BinaryOp("==", R.LiteralInt("0"), right.Sel("to_array").Apply([]).Sel("len").Apply([]), DAST.Format.BinaryOpFormat.NoFormat());
                  } else {
                    r := R.BinaryOp("==", left, right, DAST.Format.BinaryOpFormat.NoFormat());
                  }
                }
              }
              case EuclidianDiv() => {
                r := R.RawExpr("::dafny_runtime::euclidian_division").Apply([left, right]);
              }
              case EuclidianMod() => {
                r := R.RawExpr("::dafny_runtime::euclidian_modulo").Apply([left, right]);
              }
              case Passthrough(op) => {
                r := R.Expr.BinaryOp(op, left, right, format);
              }
            }
          }
        }
      }
      r, resultingOwnership := FromOwned(r, expectedOwnership);
      readIdents := recIdentsL + recIdentsR;
      return;
    }

    method GenExprConvertToNewtype(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires e.typ.UserDefined? && e.typ.resolved.kind.Newtype?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var UserDefined(ResolvedType(path, typeArgs, Newtype(b, range, erase), _, _, _)) := toTpe;
      var nativeToType := NewtypeRangeToRustType(range);
      if fromTpe == b {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
        readIdents := recIdents;
        match nativeToType {
          case Some(v) =>
            r := R.dafny_runtime.MSel("truncate!").AsExpr().Apply([recursiveGen, R.ExprFromType(v)]);
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          case None =>
            if erase {
              r := recursiveGen;
            } else {
              var rhsType := GenType(toTpe, GenTypeContext.default());
              r := R.RawExpr(rhsType.ToString(IND) + "(" + recursiveGen.ToString(IND) + ")");
            }
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        }
      } else {
        if nativeToType.Some? {
          // Conversion between any newtypes that can be expressed as a native Rust type
          match fromTpe {
            case UserDefined(
              ResolvedType(_, _, Newtype(b0, range0, erase0), attributes0, _, _)) => {
              var nativeFromType := NewtypeRangeToRustType(range0);
              if nativeFromType.Some? {
                var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
                r, resultingOwnership := FromOwnership(R.TypeAscription(recursiveGen, nativeToType.value), recOwned, expectedOwnership);
                readIdents := recIdents;
                return;
              }
            }
            case _ =>
          }
          if fromTpe == Primitive(Char) {
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r, resultingOwnership := FromOwnership(R.TypeAscription(recursiveGen.Sel("0"), nativeToType.value), recOwned, expectedOwnership);
            readIdents := recIdents;
            return;
          }
        }
        assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
        r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, env, expectedOwnership);
      }
    }

    method GenExprConvertFromNewtype(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      requires e.from != e.typ
      requires (!e.typ.UserDefined? || !e.typ.resolved.kind.Newtype?)
      requires e.from.UserDefined? && e.from.resolved.kind.Newtype?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var UserDefined(
      ResolvedType(_, _, Newtype(b, range, erase), attributes, _, _)) := fromTpe;
      var nativeFromType := NewtypeRangeToRustType(range);
      if b == toTpe {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
        readIdents := recIdents;
        match nativeFromType {
          case Some(v) =>
            var toTpeRust := GenType(toTpe, GenTypeContext.default());
            r := R.std.MSel("convert").MSel("Into").AsExpr().ApplyType([toTpeRust]).FSel("into").Apply([recursiveGen]);
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          case None =>
            if erase {
              r := recursiveGen;
            } else {
              r := recursiveGen.Sel("0");
            }
            r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        }
      } else {
        if nativeFromType.Some? {
          // The case where toTpe is a NewType which compiles to a native integer has already been handled.
          if toTpe == Primitive(Char) {
            var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
            r, resultingOwnership := FromOwnership(
              R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(
                R.TypeAscription(recursiveGen, DafnyCharUnderlying)
              ), recOwned, expectedOwnership);
            readIdents := recIdents;
            return;
          }
        }
        assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
        r, resultingOwnership, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, env, expectedOwnership);
      }
    }

    predicate IsBuiltinCollection(typ: Type) {
      typ.Seq? || typ.Set? || typ.Map? || typ.Multiset?
    }
    function GetBuiltinCollectionElement(typ: Type): Type
      requires IsBuiltinCollection(typ)
    {
      if typ.Map? then typ.value else typ.element
    }

    predicate SameTypesButDifferentTypeParameters(fromType: Type, fromTpe: R.Type, toType: Type, toTpe: R.Type) {
      && fromTpe.TypeApp?
      && toTpe.TypeApp?
      && fromTpe.baseName == toTpe.baseName
      && fromType.UserDefined?
      && toType.UserDefined?
      && IsSameResolvedTypeAnyArgs(fromType.resolved, toType.resolved)
      && |fromType.resolved.typeArgs|
      == |toType.resolved.typeArgs|
      == |fromTpe.arguments|
      == |toTpe.arguments|
    }

    /* Applies a function to every element of a sequence, returning a Result value (which is a
      failure-compatible type). Returns either a failure, or, if successful at every element,
      the transformed sequence.  */
    function {:opaque} SeqResultToResultSeq<T, E>(xs: seq<Result<T, E>>): (result: Result<seq<T>, E>)
    {
      if |xs| == 0 then Success([])
      else
        var head :- xs[0];
        var tail :- SeqResultToResultSeq(xs[1..]);
        Success([head] + tail)
    }

    function UpcastConversionLambda(fromType: Type, fromTpe: R.Type, toType: Type, toTpe: R.Type, typeParams: map<(R.Type, R.Type), R.Expr>): Result<R.Expr, (Type, R.Type, Type, R.Type, map<(R.Type, R.Type), R.Expr>)>
    {
      if fromTpe == toTpe then
        Success(R.dafny_runtime.MSel("upcast_id").AsExpr().ApplyType([fromTpe]).Apply([]))
      else if fromTpe.IsObjectOrPointer() && toTpe.IsObjectOrPointer() then
        if !toTpe.ObjectOrPointerUnderlying().DynType? then Failure((fromType, fromTpe, toType, toTpe, typeParams)) else
        var fromTpeUnderlying := fromTpe.ObjectOrPointerUnderlying();
        var toTpeUnderlying := toTpe.ObjectOrPointerUnderlying();
        Success(R.dafny_runtime.MSel(upcast).AsExpr().ApplyType([fromTpeUnderlying, toTpeUnderlying]).Apply([]))
      else if (fromTpe, toTpe) in typeParams then
        Success(typeParams[(fromTpe, toTpe)])
      else if fromTpe.IsRc() && toTpe.IsRc() then
        var lambda :- UpcastConversionLambda(fromType, fromTpe.RcUnderlying(), toType, toTpe.RcUnderlying(), typeParams);
        if fromType.Arrow? then
          Success(lambda)
        else
          Success(R.dafny_runtime.MSel("rc_coerce").AsExpr().Apply1(lambda))
      else if SameTypesButDifferentTypeParameters(fromType, fromTpe, toType, toTpe) then
        var indices :=
          if fromType.UserDefined? && fromType.resolved.kind.Datatype? then
            Std.Collections.Seq.Filter(i =>
                                         if 0 <= i < |fromTpe.arguments| then
                                           (0 <= i < |fromType.resolved.kind.variances| ==>
                                              !fromType.resolved.kind.variances[i].Nonvariant?)
                                         else
                                           false
                                      , seq(|fromTpe.arguments|, i => i))
          else
            seq(|fromTpe.arguments|, i => i);
        var lambdas :- SeqResultToResultSeq(
                         seq(|indices|, j requires 0 <= j < |indices| =>
                           var i := indices[j];
                           UpcastConversionLambda(
                             fromType.resolved.typeArgs[i],
                             fromTpe.arguments[i],
                             toType.resolved.typeArgs[i],
                             toTpe.arguments[i],
                             typeParams
                           )));
        Success(R.ExprFromType(fromTpe.baseName).ApplyType(
                  seq(|fromTpe.arguments|, i requires 0 <= i < |fromTpe.arguments| =>
                    fromTpe.arguments[i])
                ).FSel("coerce").Apply(
                  lambdas
                ))
      else if && fromTpe.IsBuiltinCollection() && toTpe.IsBuiltinCollection()
              && IsBuiltinCollection(fromType) && IsBuiltinCollection(toType) then
        var newFromTpe := fromTpe.GetBuiltinCollectionElement();
        var newToTpe := toTpe.GetBuiltinCollectionElement();
        var newFromType := GetBuiltinCollectionElement(fromType);
        var newToType := GetBuiltinCollectionElement(toType);
        var coerceArg :-
          UpcastConversionLambda(newFromType, newFromTpe, newToType, newToTpe, typeParams);
        var collectionType := R.dafny_runtime.MSel(fromTpe.Expand().baseName.path.name);
        var baseType :=
          if fromTpe.Expand().baseName.path.name == "Map" then
            collectionType.AsExpr().ApplyType([fromTpe.Expand().arguments[0], newFromTpe])
          else
            collectionType.AsExpr().ApplyType([newFromTpe]);
        Success(baseType.FSel("coerce").Apply1(coerceArg))
      else if && fromTpe.DynType? && fromTpe.underlying.FnType?
              && toTpe.DynType? && toTpe.underlying.FnType?
              && fromTpe.underlying.arguments == toTpe.underlying.arguments // TODO: Support contravariance
              && fromType.Arrow? && toType.Arrow?
              && |fromTpe.underlying.arguments| == 1
              && fromTpe.underlying.arguments[0].Borrowed?
      then
        var lambda :- UpcastConversionLambda(fromType.result, fromTpe.underlying.returnType, toType.result, toTpe.underlying.returnType, typeParams);
        Success(
          R.dafny_runtime
          .MSel("fn1_coerce")
          .AsExpr()
          .ApplyType([
                       fromTpe.underlying.arguments[0].underlying,
                       fromTpe.underlying.returnType,
                       toTpe.underlying.returnType
                     ]).Apply1(lambda))
      else
        Failure((fromType, fromTpe, toType, toTpe, typeParams))
    }

    predicate IsDowncastConversion(fromTpe: R.Type, toTpe: R.Type) {
      if fromTpe.IsObjectOrPointer() && toTpe.IsObjectOrPointer() then
        fromTpe.ObjectOrPointerUnderlying().DynType? && !toTpe.ObjectOrPointerUnderlying().DynType?
      else
        false
    }

    method GenExprConvertOther(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      var fromTpeGen := GenType(fromTpe, GenTypeContext.default());
      var toTpeGen := GenType(toTpe, GenTypeContext.default());
      var upcastConverter := UpcastConversionLambda(fromTpe, fromTpeGen, toTpe, toTpeGen, map[]);
      if upcastConverter.Success? {
        var conversionLambda := upcastConverter.value;
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
        readIdents := recIdents;
        r := conversionLambda.Apply1(recursiveGen);
        r, resultingOwnership := FromOwnership(r, OwnershipOwned, expectedOwnership);
      } else if IsDowncastConversion(fromTpeGen, toTpeGen) {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
        readIdents := recIdents;
        assert toTpeGen.IsObjectOrPointer();
        toTpeGen := toTpeGen.ObjectOrPointerUnderlying();
        r := R.dafny_runtime
        .MSel(downcast).AsExpr().Apply([recursiveGen, R.ExprFromType(toTpeGen)]);
        r, resultingOwnership := FromOwnership(r, OwnershipOwned, expectedOwnership);
      } else {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
        readIdents := recIdents;
        var Failure((fromType, fromTpeGen, toType, toTpeGen, m)) := upcastConverter;
        var msg := "/* <i>Coercion from " + fromTpeGen.ToString(IND) + " to " + toTpeGen.ToString(IND) + "</i> not yet implemented */";
        error := Some(msg);
        r := R.RawExpr(recursiveGen.ToString(IND) + msg);
        r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
      }
    }

    method GenExprConvert(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      requires e.Convert?
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases e, 0
    {
      var Convert(expr, fromTpe, toTpe) := e;
      if fromTpe == toTpe {
        var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, expectedOwnership);
        r := recursiveGen;
        r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
        readIdents := recIdents;
      } else {
        match (fromTpe, toTpe) {
          case (_, UserDefined(ResolvedType(_, _, Newtype(b, range, erase), attributes, _, _))) => {
            r, resultingOwnership, readIdents := GenExprConvertToNewtype(e, selfIdent, env, expectedOwnership);
          }
          case (UserDefined(ResolvedType(_, _, Newtype(b, range, erase), attributes, _, _)), _) => {
            r, resultingOwnership, readIdents := GenExprConvertFromNewtype(e, selfIdent, env, expectedOwnership);
          }
          case (Primitive(Int), Primitive(Real)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RcNew(R.RawExpr("::dafny_runtime::BigRational::from_integer(" + recursiveGen.ToString(IND) + ")"));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Real), Primitive(Int)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipBorrowed);
            r := R.RawExpr("::dafny_runtime::dafny_rational_to_int(" + recursiveGen.ToString(IND) + ")");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Passthrough(_)) => {
            var rhsType := GenType(toTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("<" + rhsType.ToString(IND) + " as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap()");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::DafnyInt::new(::std::rc::Rc::new(::dafny_runtime::BigInt::from(" + recursiveGen.ToString(IND) + ")))");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Primitive(Char)) => {
            var rhsType := GenType(toTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.RawExpr("::dafny_runtime::" + DafnyChar + "(" + (if charType.Unicode? then "char::from_u32(<u32" else "<u16") + " as ::dafny_runtime::NumCast>::from(" + recursiveGen.ToString(IND) + ").unwrap())" + if charType.Unicode? then ".unwrap())" else "");
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Char), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(recursiveGen.Sel("0"));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Passthrough(_)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            var toTpeGen := GenType(toTpe, GenTypeContext.default());

            r := R.RawExpr("((" + recursiveGen.ToString(IND) + ") as " + toTpeGen.ToString(IND) + ")");

            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case _ => {
            r, resultingOwnership, readIdents := GenExprConvertOther(e, selfIdent, env, expectedOwnership);
          }
        }
      }
      assert OwnershipGuarantee(expectedOwnership, resultingOwnership);
      return;
    }

    method GenIdent(
      rName: string,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      r := R.Identifier(rName);
      var tpe := env.GetType(rName);
      var placeboOpt := if tpe.Some? then tpe.value.ExtractMaybePlacebo() else None;
      var currentlyBorrowed := env.IsBorrowed(rName); // Otherwise names are owned
      var noNeedOfClone := env.CanReadWithoutClone(rName);
      if placeboOpt.Some? {
        r := r.Sel("read").Apply([]);
        currentlyBorrowed := false;
        noNeedOfClone := true; // No need to clone it, it's already owned
        tpe := Some(placeboOpt.value);
      }
      if expectedOwnership == OwnershipAutoBorrowed {
        resultingOwnership := if currentlyBorrowed then OwnershipBorrowed else OwnershipOwned;
        // No need to do anything
      } else if expectedOwnership == OwnershipBorrowedMut {
        if rName == "self" {
          resultingOwnership := OwnershipBorrowedMut;
        } else {
          if tpe.Some? && tpe.value.IsObjectOrPointer() {
            r := modify_macro.Apply1(r);
          } else {
            r := R.BorrowMut(r); // Needs to be explicit for out-parameters on methods
          }
        }
        resultingOwnership := OwnershipBorrowedMut;
      } else if expectedOwnership == OwnershipOwned {
        var needObjectFromRef :=
          selfIdent.ThisTyped? && selfIdent.IsSelf() && selfIdent.rSelfName == rName &&
          match selfIdent.dafnyType {
            case UserDefined(ResolvedType(_, _, base, attributes, _, _)) =>
              base.Class? || base.Trait?
            case _ => false
          };
        if needObjectFromRef {
          r := R.dafny_runtime.MSel("Object").AsExpr().ApplyType([R.RawType("_")]).FSel("from_ref").Apply([r]);
        } else {
          if !noNeedOfClone {
            r := r.Clone(); // We don't transfer the ownership of an identifier
          }
        }
        resultingOwnership := OwnershipOwned;
      } else if expectedOwnership == OwnershipOwnedBox {
        if !noNeedOfClone {
          r := r.Clone(); // We don't transfer the ownership of an identifier
        }
        r := R.BoxNew(r);
        resultingOwnership := OwnershipOwnedBox;
      } else if currentlyBorrowed {
        assert expectedOwnership == OwnershipBorrowed;
        resultingOwnership := OwnershipBorrowed;
      } else {
        assert expectedOwnership == OwnershipBorrowed;
        if rName != "self" {
          // It's currently owned. If it's a pointer, we need to convert it to a borrow
          if tpe.Some? && tpe.value.IsPointer() {
            r := read_macro.Apply1(r);
          } else {
            r := R.Borrow(r); // Needs to be explicit for out-parameters on methods
          }
        }
        resultingOwnership := OwnershipBorrowed;
      }
      readIdents := {rName};
      return;
    }

    predicate HasExternAttributeRenamingModule(attributes: seq<Attribute>) {
      exists attribute <- attributes :: attribute.name == "extern" && |attribute.args| == 2
    }

    method GenArgs(
      ghost e: Option<Expression>,
      selfIdent: SelfInfo,
      name: CallName,
      typeArgs: seq<Type>,
      args: seq<Expression>,
      env: Environment
    ) returns (argExprs: seq<R.Expr>, readIdents: set<string>, typeExprs: seq<R.Type>, fullNameQualifier: Option<ResolvedType>)
      modifies this
      requires e.Some? ==> forall a <- args :: a < e.value
      decreases if e.Some? then e.value else if |args| > 0 then args[0] else Expression.Tuple([]), 1, 1
      ensures fullNameQualifier.Some? ==> name.CallName?
    {
      argExprs := [];
      readIdents := {};
      var signature :=
        if name.CallName? then
          if name.receiverArg.Some? && name.receiverAsArgument then
            [name.receiverArg.value] + name.signature.parameters
          else
            name.signature.parameters
        else
          [];
      for i := 0 to |args| {
        var argOwnership := OwnershipBorrowed;
        if i < |signature| {
          var tpe := GenType(signature[i].typ, GenTypeContext.default());
          if tpe.CanReadWithoutClone() {
            argOwnership := OwnershipOwned;
          }
        }
        assume {:axiom} args[i] < if e.Some? then e.value else if |args| > 0 then args[0] else Expression.Tuple([]);
        var argExpr, _, argIdents := GenExpr(args[i], selfIdent, env, argOwnership);
        argExprs := argExprs + [argExpr];
        readIdents := readIdents + argIdents;
      }

      typeExprs := [];
      for typeI := 0 to |typeArgs| {
        var typeExpr := GenType(typeArgs[typeI], GenTypeContext.default());
        typeExprs := typeExprs + [typeExpr];
      }

      match name {
        // Calls on traits should be fully specified as we can't guarantee traits will be in context
        // Calls on non-traits should be also fully specified if the method is not found in the definition of that type
        case CallName(nameIdent, Some(UserDefined(resolvedType)), _, _, _) =>
          if resolvedType.kind.Trait? || forall m <- resolvedType.properMethods :: m != nameIdent {
            fullNameQualifier := Some(TraitTypeContainingMethod(resolvedType, nameIdent.dafny_name).GetOr(resolvedType));
          } else {
            fullNameQualifier := None;
          }
        case _ =>
          fullNameQualifier := None;
      }

      // If we are in the same context as the trait on which we are making a method call,
      // we don't need to know the type of self.
      // One exception is if the method has an extern attribute with two arguments, in which case
      // we don't simplify it.
      if && fullNameQualifier.Some?
         && selfIdent.ThisTyped? && selfIdent.dafnyType.UserDefined?
         && IsSameResolvedType(selfIdent.dafnyType.resolved, fullNameQualifier.value)
         && !HasExternAttributeRenamingModule(fullNameQualifier.value.attributes) {
        fullNameQualifier := None; // We can just use the "infix" annotation
      }
    }

    function GetMethodName(on: Expression, name: CallName): string {
      match name {
        case CallName(ident, _, _, _, _) =>
          if on.ExternCompanion? then ident.dafny_name else escapeName(ident)
        case MapBuilderAdd() | SetBuilderAdd() => "add"
        case MapBuilderBuild() | SetBuilderBuild() => "build"
      }
    }

    method GenExpr(
      e: Expression,
      selfIdent: SelfInfo,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership, readIdents: set<string>)
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      modifies this
      decreases e, 1 {
      match e {
        case Literal(_) =>
          r, resultingOwnership, readIdents :=
            GenExprLiteral(e, selfIdent, env, expectedOwnership);
        case Ident(name) => {
          r, resultingOwnership, readIdents := GenIdent(escapeVar(name), selfIdent, env, expectedOwnership);
        }
        case ExternCompanion(path) => {
          r := GenPathExpr(path, false);

          if expectedOwnership == OwnershipBorrowed {
            resultingOwnership := OwnershipBorrowed;
          } else if expectedOwnership == OwnershipOwned {
            resultingOwnership := OwnershipOwned;
          } else {
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          }
          readIdents := {};
          return;
        }
        case Companion(path, typeArgs) => {
          r := GenPathExpr(path);
          if |typeArgs| > 0 {
            var typeExprs := [];
            for i := 0 to |typeArgs| {
              var typeExpr := GenType(typeArgs[i], GenTypeContext.default());
              typeExprs := typeExprs + [typeExpr];
            }
            r := r.ApplyType(typeExprs);
          }
          if expectedOwnership == OwnershipBorrowed {
            resultingOwnership := OwnershipBorrowed;
          } else if expectedOwnership == OwnershipOwned {
            resultingOwnership := OwnershipOwned;
          } else {
            r, resultingOwnership := FromOwned(r, expectedOwnership);
          }
          readIdents := {};
          return;
        }
        case InitializationValue(typ) => {
          var typExpr := GenType(typ, GenTypeContext.default());
          if typExpr.IsObjectOrPointer() {
            r := typExpr.ToNullExpr();
          } else {
            r := R.RawExpr("<" + typExpr.ToString(IND) + " as std::default::Default>::default()");
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Tuple(values) => {
          var exprs := [];
          readIdents := {};

          for i := 0 to |values| {
            var recursiveGen, _, recIdents := GenExpr(values[i], selfIdent, env, OwnershipOwned);
            exprs := exprs + [recursiveGen];
            readIdents := readIdents + recIdents;
          }
          r := if |values| <= R.MAX_TUPLE_SIZE then R.Tuple(exprs) else R.SystemTuple(exprs);

          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case New(path, typeArgs, args) => {
          // args are provided if it is an extern type
          r := GenPathExpr(path);
          if |typeArgs| > 0 {
            var typeExprs := [];
            for i := 0 to |typeArgs| {
              var typeExpr := GenType(typeArgs[i], GenTypeContext.default());
              typeExprs := typeExprs + [typeExpr];
            }
            r := r.ApplyType(typeExprs);
          }
          r := r.FSel(allocate_fn);

          readIdents := {};
          var arguments := [];
          for i := 0 to |args| {
            var recursiveGen, _, recIdents := GenExpr(args[i], selfIdent, env, OwnershipOwned);
            arguments := arguments + [recursiveGen];
            readIdents := readIdents + recIdents;
          }
          r := r.Apply(arguments);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case NewUninitArray(dims, typ) => {
          if 16 < |dims| {
            var msg := "Unsupported: Creation of arrays of more than 16 dimensions";
            if this.error.None? {
              this.error := Some(msg);
            }
            r := R.RawExpr(msg);
            readIdents := {};
          } else {
            r := R.RawExpr("");
            var typeGen := GenType(typ, GenTypeContext.default());
            readIdents := {};
            var dimExprs := [];
            for i := 0 to |dims| invariant |dimExprs| == i {
              var recursiveGen, _, recIdents := GenExpr(dims[i], selfIdent, env, OwnershipOwned);
              dimExprs := dimExprs + [R.IntoUsize(recursiveGen)];
              readIdents := readIdents + recIdents;
            }
            if |dims| > 1 {
              var class_name := "Array" + Strings.OfNat(|dims|);
              r := R.dafny_runtime.MSel(class_name).AsExpr().ApplyType([typeGen]).FSel(placebos_usize).Apply(dimExprs);
            } else {
              r := R.dafny_runtime.MSel("array").AsExpr().FSel(placebos_usize).ApplyType([typeGen]).Apply(dimExprs);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case ArrayIndexToInt(underlying) => {
          var recursiveGen, _, recIdents := GenExpr(underlying, selfIdent, env, OwnershipOwned);
          r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(recursiveGen);
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case FinalizeNewArray(underlying, typ) => {
          var tpe := GenType(typ, GenTypeContext.default());
          var recursiveGen, _, recIdents := GenExpr(underlying, selfIdent, env, OwnershipOwned);
          readIdents := recIdents;
          if tpe.IsObjectOrPointer() {
            var t := tpe.ObjectOrPointerUnderlying();
            if t.Array? {
              r := R.dafny_runtime.MSel("array").AsExpr().FSel(array_construct).Apply1(recursiveGen);
            } else if t.IsMultiArray() {
              var c := t.MultiArrayClass();
              r := R.dafny_runtime.MSel(c).AsExpr().FSel(array_construct).Apply1(recursiveGen);
            } else {
              error := Some("Finalize New Array with a pointer or object type to something that is not an array or a multi array: " + tpe.ToString(IND));
              r := R.RawExpr(error.value);
            }
          } else {
            error := Some("Finalize New Array with a type that is not a pointer or an object: " + tpe.ToString(IND));
            r := R.RawExpr(error.value);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case DatatypeValue(datatypeType, typeArgs, variant, isCo, values) => {
          r := GenPathExpr(datatypeType.path);
          var genTypeArgs := [];
          for i := 0 to |typeArgs| {
            var typeExpr := GenType(typeArgs[i], GenTypeContext.default());
            genTypeArgs := genTypeArgs + [typeExpr];
          }
          if |typeArgs| > 0 {
            r := r.ApplyType(genTypeArgs);
          }
          r := r.FSel(escapeName(variant));
          readIdents := {};

          var assignments: seq<R.AssignIdentifier> := [];
          for i := 0 to |values| {
            var (name, value) := values[i];

            if isCo {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, Environment.Empty(), OwnershipOwned);

              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let " + next + " = " + next + ".clone();\n";
                recIdents := recIdents - {next};
              }
              var wasAssigned: string := "::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n" + allReadCloned + "move || (" + recursiveGen.ToString(IND) + ")})))";
              assignments := assignments + [R.AssignIdentifier(escapeVar(name), R.RawExpr(wasAssigned))];
            } else {
              var recursiveGen, _, recIdents := GenExpr(value, selfIdent, env, OwnershipOwned);

              assignments := assignments + [R.AssignIdentifier(escapeVar(name), recursiveGen)];
              readIdents := readIdents + recIdents;
            }
          }
          r := R.StructBuild(r, assignments);
          if IsRcWrapped(datatypeType.attributes) {
            r := R.RcNew(r);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Convert(_, _, _) => {
          r, resultingOwnership, readIdents :=
            GenExprConvert(e, selfIdent, env, expectedOwnership);
        }
        case SeqConstruct(length, expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var lengthGen, _, lengthIdents := GenExpr(length, selfIdent, env, OwnershipOwned);

          r := R.RawExpr("{\nlet _initializer = " + recursiveGen.ToString(IND) + ";\n::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), " + lengthGen.ToString(IND) + ").map(|i| _initializer(&i)).collect::<::dafny_runtime::Sequence<_>>()\n}");

          readIdents := recIdents + lengthIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqValue(exprs, typ) => {
          readIdents := {};

          var genTpe := GenType(typ, GenTypeContext.default());

          var i := 0;
          var args := [];
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);
            readIdents := readIdents + recIdents;
            args := args + [recursiveGen];

            i := i + 1;
          }
          r := R.dafny_runtime.MSel("seq!").AsExpr().Apply(args);
          if |args| == 0 {
            r := R.TypeAscription(r,
                                  R.dafny_runtime.MSel("Sequence").AsType().Apply1(genTpe));
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("set!").AsExpr().Apply(generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MultisetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("multiset!").AsExpr().Apply(generatedValues);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case ToMultiset(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          r := recursiveGen.Sel("as_dafny_multiset").Apply([]);
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValue(mapElems) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |mapElems| {
            var recursiveGenKey, _, recIdentsKey := GenExpr(mapElems[i].0, selfIdent, env, OwnershipOwned);
            var recursiveGenValue, _, recIdentsValue := GenExpr(mapElems[i].1, selfIdent, env, OwnershipOwned);

            generatedValues := generatedValues + [(recursiveGenKey, recursiveGenValue)];
            readIdents := readIdents + recIdentsKey + recIdentsValue;
            i := i + 1;
          }

          i := 0;
          var arguments := [];
          while i < |generatedValues| {
            var genKey := generatedValues[i].0;
            var genValue := generatedValues[i].1;

            arguments := arguments + [R.BinaryOp("=>", genKey, genValue, DAST.Format.BinaryOpFormat.NoFormat())];
            i := i + 1;
          }
          r := R.dafny_runtime.MSel("map!").AsExpr().Apply(arguments);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SeqUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, env, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, env, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case MapUpdate(expr, index, value) => {
          var exprR, _, exprIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          var indexR, indexOwnership, indexIdents := GenExpr(index, selfIdent, env, OwnershipBorrowed);
          var valueR, valueOwnership, valueIdents := GenExpr(value, selfIdent, env, OwnershipBorrowed);
          r := exprR.Sel("update_index").Apply([indexR, valueR]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := exprIdents + indexIdents + valueIdents;
          return;
        }
        case This() => {
          match selfIdent {
            case ThisTyped(id, dafnyType) => {
              r, resultingOwnership, readIdents := GenIdent(id, selfIdent, env, expectedOwnership);
            }
            case None => {
              r := R.RawExpr("panic!(\"this outside of a method\")");
              r, resultingOwnership := FromOwned(r, expectedOwnership);
              readIdents := {};
            }
          }
          return;
        }
        case Ite(cond, t, f) => {
          // If then else expressions cannot recurse to return something borrowed in their branches
          // because sometimes the lifetime would be the one of a local variable.
          // Hence we need to return owned values.
          assert {:split_here} true;
          var cond, _, recIdentsCond := GenExpr(cond, selfIdent, env, OwnershipOwned);

          var fExpr, fOwned, recIdentsF := GenExpr(f, selfIdent, env, OwnershipOwned);
          var tExpr, _, recIdentsT := GenExpr(t, selfIdent, env, OwnershipOwned); // there's a chance that f forced ownership

          r := R.IfExpr(cond, tExpr, fExpr);

          r, resultingOwnership := FromOwnership(r, OwnershipOwned, expectedOwnership);
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
          return;
        }
        case UnOp(Not, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, env, OwnershipOwned);

          r := R.UnaryOp("!", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(BitwiseNot, e, format) => {
          var recursiveGen, _, recIdents := GenExpr(e, selfIdent, env, OwnershipOwned);

          r := R.UnaryOp("~", recursiveGen, format);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case UnOp(Cardinality, e, format) => {
          var recursiveGen, recOwned, recIdents := GenExpr(e, selfIdent, env, OwnershipAutoBorrowed);

          r := recursiveGen.Sel("cardinality").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BinOp(_, _, _, _) =>
          r, resultingOwnership, readIdents :=
            GenExprBinary(e, selfIdent, env, expectedOwnership);
        case ArrayLen(expr, exprType, dim, native) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var arrayType := GenType(exprType, GenTypeContext.default());

          if !arrayType.IsObjectOrPointer() {
            var msg := "Array length of something not an array but " + arrayType.ToString(IND);
            this.error := Some(msg);
            r := R.RawExpr(msg);
          } else {
            var underlying := arrayType.ObjectOrPointerUnderlying();
            if dim == 0 && underlying.Array? {
              r := read_macro.Apply1(recursiveGen).Sel("len").Apply([]);
            } else {
              if dim == 0 {
                r := read_macro.Apply1(recursiveGen).Sel("data").Sel("len").Apply([]);
              } else {
                r := read_macro.Apply1(recursiveGen).Sel("length" + Strings.OfNat(dim) + "_usize").Apply([]);
              }
            }
            if !native {
              r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(r);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MapKeys(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := recursiveGen.Sel("keys").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValues(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := recursiveGen.Sel("values").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapItems(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := recursiveGen.Sel("items").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SelectFn(on, field, isDatatype, isStatic, isConstant, arguments) => {
          // Transforms a function member into a lambda
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          var s: string;
          var onString := onExpr.ToString(IND);

          if isStatic {
            // Generates |x0: &tp0, ...xn: &tpn| on::field(x0, .... xn) (possibly with some .clone())
            var lEnv := env;
            var args := [];
            s := "|";
            for i := 0 to |arguments| {
              if i > 0 {
                s := s + ", ";
              }
              var ty := GenType(arguments[i], GenTypeContext.default());
              var bTy := R.Borrowed(ty);
              var name := "x" + Strings.OfInt(i);
              lEnv := lEnv.AddAssigned(name, bTy);

              args := args + [(name, ty)];
              s := s + name + ": " + bTy.ToString(IND);
            }
            s := s + "| " + onString + "::" + escapeVar(field) + (if isConstant then "()" else "") + "(";
            for i := 0 to |args| {
              if i > 0 {
                s := s + ", ";
              }
              var (name, ty) := args[i];
              var rIdent, _, _ := GenIdent(name, selfIdent, lEnv, if ty.CanReadWithoutClone() then OwnershipOwned else OwnershipBorrowed);
              s := s + rIdent.ToString(IND);
            }
            s := s + ")";
          } else {
            // Generates
            // {
            //   let callTarget = (on); //or (on.clone()) if it was owned.
            //   move |arg0, ...argn| {
            //     callTarget.field(arg0, .... argn) (possibly with some .clone())
            //   }
            // }
            s := "{\n";
            s := s + "let callTarget = (" + onString + (if onOwned == OwnershipOwned then ")" else ").clone()") + ";\n";
            var args := "";
            var i := 0;
            while i < |arguments| {
              if i > 0 {
                args := args + ", ";
              }
              args := args + "arg" + Strings.OfNat(i);
              i := i + 1;
            }
            s := s + "move |" + args + "| {\n";
            s := s + "callTarget." + escapeVar(field) +
            (if isConstant then "()" else "") + "(" + args + ")\n";
            s := s + "}\n";
            s := s + "}";
          }

          var typeShape := "dyn ::std::ops::Fn(";
          var i := 0;
          while i < |arguments| {
            if i > 0 {
              typeShape := typeShape + ", ";
            }
            typeShape := typeShape + "&_";
            i := i + 1;
          }

          typeShape := typeShape + ") -> _";

          s := "::std::rc::Rc::new(" + s + ") as ::std::rc::Rc<" + typeShape + ">";
          r := R.RawExpr(s);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(on, field, isConstant, isDatatype, fieldType) => {
          if on.Companion? || on.ExternCompanion? {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

            r := onExpr.FSel(escapeVar(field)).Apply([]);

            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
            return;
          } else if isDatatype {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
            r := onExpr.Sel(escapeVar(field)).Apply([]);
            var typ := GenType(fieldType, GenTypeContext.default());
            // All fields are returned as addresses for now until we have something more clever
            r, resultingOwnership := FromOwnership(r, OwnershipBorrowed, expectedOwnership);
            readIdents := recIdents;
          } else {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
            r := onExpr;
            if onExpr != R.self {// self are already borrowed or mutably borrowed
              match onExpr { // Special case, the constructor.
                case UnaryOp("&", Identifier("this"), _) =>
                  r := R.Identifier("this");
                case _ =>
              }
              if pointerType.RcMut?  {
                r := r.Clone();
              }
              if ObjectType.RawPointers? {
                r := read_macro.Apply1(r);
              } else {
                r := modify_macro.Apply1(r); // Functions have to take &mut because of upcasting
              }
            }
            r := r.Sel(escapeVar(field));
            if isConstant {
              r := r.Apply([]);
            }
            r := r.Clone(); // self could be &mut, so to avoid any borrow checker problem, we clone the value.
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          return;
        }
        case Index(on, collKind, indices) => {
          assert {:split_here} true;
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := onExpr;

          var hadArray := false;
          if collKind == CollKind.Array {
            r := read_macro.Apply1(r);
            hadArray := true;
            if |indices| > 1 {
              r := r.Sel("data");
            }
          }
          for i := 0 to |indices| {
            if collKind == CollKind.Array {
              var idx, idxOwned, recIdentsIdx := GenExpr(indices[i], selfIdent, env, OwnershipOwned);
              idx := R.IntoUsize(idx);
              r := R.SelectIndex(r, idx);
              readIdents := readIdents + recIdentsIdx;
            } else { // Sequence, Maps
              var idx, idxOwned, recIdentsIdx := GenExpr(indices[i], selfIdent, env, OwnershipBorrowed);
              r := r.Sel("get").Apply1(idx);
              readIdents := readIdents + recIdentsIdx;
            }
          }
          if hadArray {
            r := r.Clone();
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case IndexRange(on, isArray, low, high) => {
          var onExpectedOwnership :=
            if isArray then
              if pointerType.Raw? then
                OwnershipOwned
              else
                OwnershipBorrowed
            else
              OwnershipAutoBorrowed;
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, onExpectedOwnership);
          readIdents := recIdents;

          var methodName := if low.Some? then
            if high.Some? then "slice" else "drop"
          else if high.Some? then "take" else "";

          var arguments := [];
          match low {
            case Some(l) => {
              var lExpr, _, recIdentsL := GenExpr(l, selfIdent, env, OwnershipBorrowed);
              arguments := arguments + [lExpr];
              readIdents := readIdents + recIdentsL;
            }
            case None => {}
          }

          match high {
            case Some(h) => {
              var hExpr, _, recIdentsH := GenExpr(h, selfIdent, env, OwnershipBorrowed);
              arguments := arguments + [hExpr];
              readIdents := readIdents + recIdentsH;
            }
            case None => {}
          }

          r := onExpr;
          if isArray {
            if methodName != "" {
              methodName := "_" + methodName;
            }
            var object_suffix :=
              if pointerType.Raw? then "" else "_object";
            r := R.dafny_runtime_Sequence.FSel("from_array"+methodName+object_suffix).Apply([onExpr] + arguments);
          } else {
            if methodName != "" {
              r := r.Sel(methodName).Apply(arguments);
            } else {
              r := r.Clone();
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TupleSelect(on, idx, fieldType) => {
          var onExpr, onOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          var selName := Strings.OfNat(idx); // Rust tuples
          match fieldType {
            case Tuple(tps) =>
              if fieldType.Tuple? && |tps| > R.MAX_TUPLE_SIZE {
                selName := "_" + selName; // R.SystemTuple
              }
            case _ =>
          }
          r := onExpr.Sel(selName).Clone(); // If we don't clone, we would move out that field
          // even if "on" was borrowed, the field is always owned so we need to explicitly borrow it depending on the use case.
          r, resultingOwnership := FromOwnership(r, OwnershipOwned, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Call(on, name, typeArgs, args) => {
          var argExprs, recIdents, typeExprs, fullNameQualifier := GenArgs(Some(e), selfIdent, name, typeArgs, args, env);
          readIdents := recIdents;

          match fullNameQualifier {
            // Trait calls are fully specified as we can't guarantee traits will be in context
            case Some(ResolvedType(path, onTypeArgs, base, _, _, _)) =>
              var fullPath := GenPathExpr(path);
              var onTypeExprs := GenTypeArgs(onTypeArgs, GenTypeContext.default());
              var onExpr, recOwnership, recIdents;
              if base.Trait? || base.Class? {
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipOwned);
                if ObjectType.RawPointers? {
                  onExpr := read_macro.Apply1(onExpr);
                } else {
                  onExpr := modify_macro.Apply1(onExpr);
                }
                readIdents := readIdents + recIdents;
              } else {
                var expectedOnOwnership := if ObjectType.RawPointers? then OwnershipBorrowed else OwnershipBorrowedMut;
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, expectedOnOwnership);
                readIdents := readIdents + recIdents;
              }
              r := fullPath.ApplyType(onTypeExprs).FSel(escapeName(name.name)).ApplyType(typeExprs).Apply([onExpr] + argExprs);
              r, resultingOwnership := FromOwned(r, expectedOwnership);
            case _ => // Infix call on.name(args)
              var onExpr, _, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
              readIdents := readIdents + recIdents;
              var renderedName := GetMethodName(on, name);
              // Pointers in the role of "self" must be converted to borrowed versions.
              match on {
                case Companion(_, _) | ExternCompanion(_) => {
                  onExpr := onExpr.FSel(renderedName);
                }
                case _ => {
                  if onExpr != R.self { // Self has the reference type already
                    match name {
                      case CallName(_, Some(tpe), _, _, _) =>
                        var typ := GenType(tpe, GenTypeContext.default());
                        if typ.IsObjectOrPointer() {
                          if ObjectType.RawPointers? {
                            onExpr := read_macro.Apply1(onExpr);
                          } else {
                            onExpr := modify_macro.Apply1(onExpr);
                          }
                        }
                      case _ =>
                    }
                  }
                  onExpr := onExpr.Sel(renderedName);
                }
              }
              r := onExpr.ApplyType(typeExprs).Apply(argExprs);
              r, resultingOwnership := FromOwned(r, expectedOwnership);
              return;
          }
        }
        case Lambda(paramsDafny, retType, body) => {
          var params := GenParams(paramsDafny, true);
          var paramNames := [];
          var paramTypesMap := map[];
          for i := 0 to |params| {
            var name := params[i].name;
            paramNames := paramNames + [name];
            paramTypesMap := paramTypesMap[name := params[i].tpe];
          }
          var subEnv := env.ToOwned().merge(Environment(paramNames, paramTypesMap));

          var recursiveGen, recIdents, _ := GenStmts(body, if selfIdent != NoSelf then ThisTyped("_this", selfIdent.dafnyType) else NoSelf, subEnv, true, None);
          readIdents := {};
          recIdents := recIdents - (set name <- paramNames);
          var allReadCloned := R.RawExpr("");
          while recIdents != {} decreases recIdents {
            var next: string :| next in recIdents;

            if selfIdent != NoSelf && next == "_this" {
              var selfCloned, _, _ := GenIdent("self", selfIdent, Environment.Empty(), OwnershipOwned);
              allReadCloned := allReadCloned.Then(R.DeclareVar(R.MUT, "_this", None, Some(selfCloned)));
            } else if !(next in paramNames) {
              var copy := R.Identifier(next).Clone();
              allReadCloned := allReadCloned.Then(
                R.DeclareVar(R.MUT, next, None, Some(copy))
              );
              readIdents := readIdents + {next};
            }

            recIdents := recIdents - {next};
          }

          var retTypeGen := GenType(retType, GenTypeContext.default());
          r := R.Block(
            allReadCloned.Then(
              R.RcNew(
                R.Lambda(params, Some(retTypeGen), R.Block(recursiveGen))
              )
            ));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case BetaRedex(values, retType, expr) => {
          var paramNames := [];
          var paramFormals := GenParams(Std.Collections.Seq.Map(
                                          (value: (Formal, Expression)) => value.0, values));
          var paramTypes := map[];
          var paramNamesSet := {};
          for i := 0 to |values| {
            var name := values[i].0.name;
            var rName := escapeVar(name);
            paramNames := paramNames + [rName];
            paramTypes := paramTypes[rName := paramFormals[i].tpe];
            paramNamesSet := paramNamesSet + {rName};
          }

          readIdents := {};
          r := R.RawExpr("");

          for i := 0 to |values| {
            var typeGen := GenType(values[i].0.typ, GenTypeContext.default());

            var valueGen, _, recIdents := GenExpr(values[i].1, selfIdent, env, OwnershipOwned);
            r := r.Then(R.DeclareVar(R.CONST, escapeVar(values[i].0.name), Some(typeGen), Some(valueGen)));
            readIdents := readIdents + recIdents;
          }

          var newEnv := Environment(paramNames, paramTypes);

          var recGen, recOwned, recIdents := GenExpr(expr, selfIdent, newEnv, expectedOwnership);
          readIdents := recIdents - paramNamesSet;
          r := R.Block(r.Then(recGen));
          r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
          return;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, _, recIdents := GenExpr(value, selfIdent, env, OwnershipOwned);

          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, GenTypeContext.default());
          var iifeVar := escapeVar(name);
          var bodyGen, _, bodyIdents :=
            GenExpr(iifeBody, selfIdent, env.AddAssigned(iifeVar, valueTypeGen), OwnershipOwned);
          readIdents := readIdents + (bodyIdents - {iifeVar});
          r := R.Block(
            R.DeclareVar(R.CONST, iifeVar, Some(valueTypeGen), Some(valueGen))
            .Then(bodyGen));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Apply(func, args) => {
          // TODO: Need the type of the input of Func to ensure we generate arguments with the right ownership
          var funcExpr, _, recIdents := GenExpr(func, selfIdent, env, OwnershipBorrowed);
          readIdents := recIdents;
          var rArgs := [];
          for i := 0 to |args| {
            var argExpr, argOwned, argIdents := GenExpr(args[i], selfIdent, env, OwnershipBorrowed);
            rArgs := rArgs + [argExpr];
            readIdents := readIdents + argIdents;
          }
          r := funcExpr.Apply(rArgs);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          var dTypePath := GenPathType(dType + [Ident.Ident(variant)]);
          r := R.Identifier("matches!").Apply([exprGen.Sel("as_ref").Apply([]), R.RawExpr(dTypePath.ToString(IND) + "{ .. }")]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Is(expr, fromType, toType) => {
          var expr, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var fromType := GenType(fromType, GenTypeContext.default());
          var toType := GenType(toType, GenTypeContext.default());
          if fromType.IsObjectOrPointer() && toType.IsObjectOrPointer() {
            r := expr.Sel("is_instance_of").ApplyType([toType.ObjectOrPointerUnderlying()]).Apply([]);
          } else {
            error := Some("Source and/or target types of type test is/are not Object or Ptr");
            r := R.RawExpr(error.value);
            readIdents := {};
          }
          r, resultingOwnership := FromOwnership(r, recOwned, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case BoolBoundedPool() => {
          r := R.RawExpr("[false, true]");
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("iter").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case SeqBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("iter").Apply([]);
          if !includeDuplicates {
            r := R.dafny_runtime.MSel("itertools").MSel("Itertools").MSel("unique").AsExpr().Apply1(r);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MapBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("keys").Apply([]).Sel("iter").Apply([]);
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case IntRange(typ, lo, hi, up) => {
          var lo, _, recIdentsLo := GenExpr(lo, selfIdent, env, OwnershipOwned);
          var hi, _, recIdentsHi := GenExpr(hi, selfIdent, env, OwnershipOwned);
          if up {
            r := R.dafny_runtime.MSel("integer_range").AsExpr().Apply([lo, hi]);
          } else {
            r := R.dafny_runtime.MSel("integer_range_down").AsExpr().Apply([hi, lo]);
          }
          if !typ.Primitive? {
            var tpe := GenType(typ, GenTypeContext.default());
            r := r.Sel("map").Apply1(R.std.MSel("convert").MSel("Into").AsExpr().ApplyType([tpe]).FSel("into"));
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdentsLo + recIdentsHi;
          return;
        }
        case UnboundedIntRange(start, up) => {
          var start, _, recIdentStart := GenExpr(start, selfIdent, env, OwnershipOwned);
          if up {
            r := R.dafny_runtime.MSel("integer_range_unbounded").AsExpr().Apply1(start);
          } else {
            r := R.dafny_runtime.MSel("integer_range_down_unbounded").AsExpr().Apply1(start);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdentStart;
          return;
        }
        case MapBuilder(keyType, valueType) => {
          var kType := GenType(keyType, GenTypeContext.default());
          var vType := GenType(valueType, GenTypeContext.default());
          r := R.dafny_runtime.MSel("MapBuilder").AsExpr().ApplyType([kType, vType]).FSel("new").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBuilder(elemType) => {
          var eType := GenType(elemType, GenTypeContext.default());
          readIdents := {};
          r := R.dafny_runtime.MSel("SetBuilder").AsExpr().ApplyType([eType]).FSel("new").Apply([]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case Quantifier(elemType, collection, is_forall, lambda) => {
          var tpe := GenType(elemType, GenTypeContext.default());
          // Borrowed in this context means that the elements are iterated as borrowed,
          // because lambda expression takes them borrowed by default.
          var collectionGen, _, recIdents := GenExpr(collection, selfIdent, env, OwnershipOwned);
          // Integer collections are owned because they are computed number by number.
          // Sequence bounded pools are also owned
          var extraAttributes := [];
          if collection.IntRange? || collection.UnboundedIntRange? || collection.SeqBoundedPool? {
            extraAttributes := [AttributeOwned];
          }

          if lambda.Lambda? {
            // The lambda is supposed to be a raw lambda, arguments are borrowed
            var formals := lambda.params;
            var newFormals := [];
            for i := 0 to |formals| {
              newFormals := newFormals + [formals[i].(attributes := extraAttributes + formals[i].attributes)];
            }
            var newLambda := lambda.(params := newFormals);
            // TODO: We only add one attribute to each parameter.
            assume {:axiom} newLambda < lambda;
            var lambdaGen, _, recLambdaIdents := GenExpr(newLambda, selfIdent, env, OwnershipOwned);
            var fn := if is_forall then "all" else "any";
            r := collectionGen.Sel(fn).Apply1(lambdaGen.Sel("as_ref").Apply([]));
            readIdents := recIdents + recLambdaIdents;
          } else {
            error := Some("Quantifier without an inline lambda");
            r := R.RawExpr(error.value);
            readIdents := {};
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
      }
    }

    method Compile(p: seq<Module>, externalFiles: seq<string>) returns (s: string)
      modifies this
    {
      s := "#![allow(warnings, unconditional_panic)]\n";
      s := s + "#![allow(nonstandard_style)]\n";

      var externUseDecls := [];

      for i := 0 to |externalFiles| {
        var externalFile := externalFiles[i];
        var externalMod := externalFile;
        if |externalFile| > 3 && externalFile[|externalFile|-3..] == ".rs" {
          externalMod := externalFile[0..|externalFile|-3];
        } else {
          error := Some("Unrecognized external file " + externalFile + ". External file must be *.rs files");
        }
        var externMod := R.ExternMod(externalMod);
        s := s + externMod.ToString("") + "\n";
        externUseDecls := externUseDecls + [
          R.UseDecl(R.Use(R.PUB, R.crate.MSel(externalMod).MSel("*")))
        ];
      }

      if externUseDecls != [] {
        s := s + R.Mod(DAFNY_EXTERN_MODULE, externUseDecls).ToString("") + "\n";
      }

      var allModules := SeqMap<string, GatheringModule>.Empty();
      for i := 0 to |p| {
        var m := GenModule(p[i], []);
        allModules := GatheringModule.MergeSeqMap(allModules, m);
      }
      for i := 0 to |allModules.keys| {
        if allModules.keys[i] !in allModules.values { // Could be avoided with subset types
          continue;
        }
        var m := allModules.values[allModules.keys[i]].ToRust();
        for j := 0 to |optimizations| {
          m := optimizations[j](m);
        }
        s := s + "\n";
        s := s + m.ToString("");

      }
    }

    static method EmitCallToMain(fullName: seq<Name>) returns (s: string) {
      s := "\nfn main() {\n";
      var i := 0;
      while i < |fullName| {
        if i > 0 {
          s := s + "::";
        }
        s := s + escapeName(fullName[i]);
        i := i + 1;
      }
      s := s + "();\n}";
    }
  }
}