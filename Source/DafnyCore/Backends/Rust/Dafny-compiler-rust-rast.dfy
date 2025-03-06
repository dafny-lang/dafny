
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

  // Default Rust-like indentation
  const IND := "    "

  const DocStringPrefix: string := "/// "

  datatype RASTTopDownVisitor<!T(!new)> =
    RASTTopDownVisitor(
      nameonly VisitTypeSingle: (T, Type) -> T,
      nameonly VisitExprSingle: (T, Expr) -> T,
      nameonly VisitModDeclSingle: (T, ModDecl, Path) -> T,
      nameonly recurseSubmodules: bool := false
    )
  {
    function VisitMod(acc: T, mod: Mod, SelfPath: Path): T {
      mod.Fold(acc, (acc, modDecl) requires modDecl < mod => VisitModMapping(acc, modDecl, SelfPath))
    }
    function VisitTypeParams(acc: T, typeParams: seq<TypeParamDecl>): T {
      FoldLeft( (acc: T, t: TypeParamDecl) =>
                  FoldLeft( (acc: T, t: Type) =>
                              VisitType(acc, t),
                            acc, t.constraints),
                acc, typeParams)
    }
    function VisitFields(acc: T, fields: Fields): T {
      match fields {
        case NamedFields(sFields) =>
          FoldLeft( (acc: T, f: Field) =>
                      VisitType(acc, f.formal.tpe),
                    acc, sFields)
        case NamelessFields(sFields) =>
          FoldLeft( (acc: T, f: NamelessField) =>
                      VisitType(acc, f.tpe),
                    acc, sFields)
      }
    }

    function VisitModMapping(acc: T, modDecl: ModDecl, SelfPath: Path): T {
      var acc := VisitModDeclSingle(acc, modDecl, SelfPath);
      match modDecl {
        case ModDecl(mod) =>
          if recurseSubmodules then VisitMod(acc, mod, SelfPath.MSel(mod.name)) else acc
        case StructDecl(struct) =>
          VisitStructMapping(acc, struct)
        case TypeDecl(TypeSynonym(attributes, _, name, typeParams, tpe)) =>
          var acc := VisitTypeParams(acc, typeParams);
          var acc := VisitType(acc, tpe);
          acc
        case ConstDecl(Constant(attributes, _, name, tpe, value)) =>
          var acc := VisitType(acc, tpe);
          var acc := value.Fold(acc, VisitExprSingle, VisitTypeSingle);
          acc
        case EnumDecl(Enum(attributes, _, name, typeParams, variants)) =>
          FoldLeft(
            (acc: T, enumCase: EnumCase) requires enumCase in variants =>
              VisitFields(acc, enumCase.fields),
            VisitTypeParams(acc, typeParams),
            variants
          )
        case ImplDecl(impl) => VisitImplMapping(acc, impl)
        case TraitDecl(tr) => VisitTraitDecl(acc, tr)
        case TopFnDecl(fn) => VisitTopFn(acc, fn)
        case UseDecl(use) => VisitUse(acc, use)
      }
    }

    function VisitStructMapping(acc: T, struct: Struct): T {
      VisitTypeParams(acc, struct.typeParams)
    }

    function VisitTraitDecl(acc: T, tr: Trait): T {
      match tr {
        case Trait(_, _, typeParams, tpe, parents, body) =>
          var acc := VisitTypeParams(acc, typeParams);
          var acc := tpe.Fold(acc, VisitTypeSingle);
          var acc :=
            FoldLeft(
              (acc: T, parent: Type) =>
                parent.Fold(acc, VisitTypeSingle),
              acc,
              parents
            );
          VisitBody(acc, body)
      }
    }

    function VisitTopFn(acc: T, t: TopFnDecl): T {
      match t {
        case TopFn(_, attributes, visibility, fn) =>
          VisitFn(acc, fn)
      }
    }

    function VisitUse(acc: T, u: Use): T {
      acc // Nothing to visit for now
    }

    function VisitType(acc: T, tpe: Type): T {
      tpe.Fold(acc, (acc: T, t: Type) => VisitTypeSingle(acc, t))
    }

    function VisitImplMapping(acc: T, impl: Impl): T {
      match impl {
        case ImplFor(typeParams, tpe, forType, body) =>
          var acc := VisitTypeParams(acc, typeParams);
          var acc := VisitType(acc, tpe);
          var acc := VisitType(acc, forType);
          VisitBody(acc, body)
        // TODO: Add body
        case Impl(typeParams, tpe, body) =>
          var acc := VisitType(acc, tpe);
          VisitBody(acc, body)
      }
    }
    function VisitBody(acc: T, members: seq<ImplMember>): T {
      FoldLeft(
        (acc: T, member: ImplMember) requires member in members =>
          VisitMember(acc, member),
        acc,
        members
      )
    }
    function VisitMember(acc: T, member: ImplMember): T {
      match member {
        case RawImplMember(content) => acc
        case FnDecl(docString, attributes, pub, fun) =>
          VisitFn(acc, fun)
        case TypeDeclMember(name, tpe) =>
          VisitType(acc, tpe)
        case ImplMemberMacro(expr: Expr) =>
          expr.Fold(acc, VisitExprSingle, VisitTypeSingle)
      }
    }
    function VisitFn(acc: T, fn: Fn): T {
      match fn {
        case Fn(name, typeParams, formals, returnType, body) =>
          var acc := VisitTypeParams(acc, typeParams);
          var acc := FoldLeft(
                       (acc: T, f: Formal) requires f in formals => f.tpe.Fold(acc, VisitTypeSingle),
                       acc, formals
                     );
          var acc := if returnType.None? then acc else returnType.value.Fold(acc, VisitTypeSingle);
          var acc := if body.None? then acc else body.value.Fold(acc, VisitExprSingle, VisitTypeSingle);
          acc
      }
    }
  }

  datatype RASTBottomUpReplacer =
    RASTBottomUpReplacer(
      nameonly ReplaceModSingle: (Mod, Path) --> Mod := (m: Mod, p: Path) => m,
      nameonly ReplaceTypeSingle: Type -> Type := (t: Type) => t,
      nameonly ReplaceExprSingle: Expr -> Expr := (e: Expr) => e
    ) {
    function ReplaceMod(mod: Mod, SelfPath: Path): Mod
      requires forall m: Mod, p: Path | m < mod ::
                 ReplaceModSingle.requires(m, p)
    {
      if mod.ExternMod? then mod else
      var newModDeclarations := mod.Fold([], (current, modDecl) requires modDecl < mod =>
                                           assert forall mod: Mod, p: Path | mod < modDecl :: this.ReplaceModSingle.requires(mod, p);
                                           current + [ReplaceModDecl(modDecl, SelfPath)]
                                );
      mod.(body := newModDeclarations)
    }
    function ReplaceModDecl(modDecl: ModDecl, SelfPath: Path): ModDecl
      requires forall mod: Mod, p: Path | mod < modDecl ::
                 ReplaceModSingle.requires(mod, p)
    {
      match modDecl {
        case ModDecl(mod) =>
          ModDecl(ReplaceModSingle(mod, SelfPath.MSel(mod.name))) // We optimize independently submodules
        case StructDecl(struct) =>
          StructDecl(ReplaceStruct(struct))
        case TypeDecl(tpe) =>
          TypeDecl(ReplaceTypeDecl(tpe))
        case ConstDecl(c) =>
          ConstDecl(ReplaceConst(c))
        case EnumDecl(enum) =>
          EnumDecl(ReplaceEnum(enum))
        case ImplDecl(impl) =>
          ImplDecl(ReplaceImplDecl(impl))
        case TraitDecl(tr) =>
          TraitDecl(ReplaceTrait(tr))
        case TopFnDecl(fn) =>
          TopFnDecl(ReplaceTopFn(fn))
        case UseDecl(use) =>
          UseDecl(ReplaceUse(use))
      }
    }

    function ReplaceStruct(struct: Struct): Struct {
      match struct {
        case Struct(docString, attributes, name, typeParams, fields) =>
          Struct(docString, attributes, name,
                 ReplaceTypeParams(typeParams),
                 ReplaceFields(fields)
          )
      }
    }

    function ReplaceTypeDecl(t: TypeSynonym): TypeSynonym {
      match t {
        case TypeSynonym(docString, attributes, name, typeParams, tpe) =>
          TypeSynonym(docString, attributes, name, ReplaceTypeParams(typeParams), ReplaceType(tpe))
      }
    }

    function ReplaceConst(t: Constant): Constant {
      match t {
        case Constant(docString, attributes, name, tpe, value) =>
          Constant(docString, attributes, name, ReplaceType(tpe), ReplaceExpr(value))
      }
    }

    function ReplaceEnum(enum: Enum): Enum {
      match enum {
        case Enum(docString, attributes, name, typeParams, variants) =>
          Enum(docString, attributes, name,
               ReplaceTypeParams(typeParams),
               Std.Collections.Seq.Map(
                 (t: EnumCase) => ReplaceEnumCase(t), variants))
      }
    }

    function ReplaceEnumCase(enumCase: EnumCase): EnumCase {
      match enumCase {
        case EnumCase(docString, name, fields) =>
          EnumCase(docString, name, ReplaceFields(fields))
      }
    }

    function ReplaceImplDecl(impl: Impl): Impl {
      match impl {
        case ImplFor(typeParams, tpe, forType, body) =>
          ImplFor(
            ReplaceTypeParams(typeParams),
            ReplaceType(tpe),
            ReplaceType(forType),
            ReplaceBody(body))
        case Impl(typeParams, tpe, body) =>
          Impl(ReplaceTypeParams(typeParams), ReplaceType(tpe), ReplaceBody(body))
      }
    }

    function ReplaceTrait(tr: Trait): Trait {
      match tr {
        case Trait(docString, attributes, typeParams, tpe, parents, body) =>
          Trait(
            docString,
            attributes,
            ReplaceTypeParams(typeParams),
            ReplaceType(tpe),
            Std.Collections.Seq.Map(
              (t: Type) => ReplaceType(t), parents),
            ReplaceBody(body))
      }
    }

    function ReplaceTopFn(t: TopFnDecl): TopFnDecl {
      match t {
        case TopFn(docString, attributes, visibility, fn) =>
          TopFn(docString, attributes, visibility, ReplaceFn(fn))
      }
    }

    function ReplaceFn(t: Fn): Fn {
      match t {
        case Fn(name, typeParams, formals, returnType, body) =>
          Fn(
            name,
            ReplaceTypeParams(typeParams),
            Std.Collections.Seq.Map(
              (f: Formal) requires f in formals => f.Replace(ReplaceType),
              formals
            ),
            if returnType.None? then None else Some(returnType.value.Replace(ReplaceType)),
            if body.None? then None else Some(body.value.Replace(ReplaceExpr, ReplaceType))
          )
      }
    }

    function ReplaceUse(use: Use): Use {
      match use {
        case Use(visibility, path) =>
          Use(visibility, path)
      }
    }

    function ReplaceBody(decls: seq<ImplMember>): seq<ImplMember> {
      Std.Collections.Seq.Map(
        (t: ImplMember) => ReplaceImplMember(t), decls)
    }

    function ReplaceImplMember(t: ImplMember): ImplMember {
      match t {
        case RawImplMember(content) => t
        case FnDecl(docString, attributes, pub, fun) =>
          FnDecl(docString, attributes, pub, ReplaceFn(fun))
        case TypeDeclMember(name, tpe) =>
          TypeDeclMember(name, ReplaceType(tpe))
        case ImplMemberMacro(expr: Expr) =>
          ImplMemberMacro(ReplaceExpr(expr))
      }
    }
    function ReplaceExpr(e: Expr): Expr {
      e.Replace(ReplaceExprSingle, ReplaceTypeSingle)
    }
    function ReplaceTypeParams(typeParams: seq<TypeParamDecl>): seq<TypeParamDecl> {
      Std.Collections.Seq.Map(
        (t: TypeParamDecl) =>
          t.(constraints := Std.Collections.Seq.Map(
            (constraint: Type) =>
              ReplaceType(constraint), t.constraints)), typeParams)
    }
    function ReplaceType(t: Type): Type {
      t.Replace(this.ReplaceTypeSingle)
    }
    function ReplaceFields(fields: Fields): Fields {
      match fields {
        case NamedFields(sFields) =>
          NamedFields(
            Std.Collections.Seq.Map(
              (f: Field) =>
                f.(formal := f.formal.(tpe := ReplaceType(f.formal.tpe))), sFields
            ))
        case NamelessFields(sFields) =>
          NamelessFields(
            Std.Collections.Seq.Map(
              (f: NamelessField) =>
                f.(tpe := ReplaceType(f.tpe)), sFields))
      }
    }
  }

  opaque function FoldLeft<A(!new), T>(f: (A, T) --> A, init: A, xs: seq<T>): A
    requires forall t: T <- xs, a: A :: f.requires(a, t)
  {
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  function GatherSimpleQuotes(docstring: string, acc: string := ""): (r: string)
    ensures |r| <= |acc| + |docstring|
  {
    if |docstring| == 0 || docstring[0] != '`' then acc else
    GatherSimpleQuotes(docstring[1..], acc + "`")
  }

  // Converts Dafny docstring into Rust docstring that won't normally cause issue with `cargo doc`
  // - Escape blocks ```...``` to ```dafny ...``` but keep ```rs...``` intact
  // - Every line starting with 4 or more spaces gets its first space replaced by a `|`
  function ConvertDocstring(dafnyDocstring: string, ind: string, newlineStarted: bool := true, codeMarker: Option<string> := None): string {
    if |dafnyDocstring| == 0 then dafnyDocstring
    else if dafnyDocstring[0] == '\n' then
      "\n" + ind + DocStringPrefix + ConvertDocstring(dafnyDocstring[1..], ind, true, codeMarker)
    else if dafnyDocstring[0] == ' ' then
      if codeMarker.None? && newlineStarted && |dafnyDocstring| > 4 && dafnyDocstring[..4] == "    " then
        "|   " + ConvertDocstring(dafnyDocstring[4..], ind, false, codeMarker)
      else
        " " + ConvertDocstring(dafnyDocstring[1..], ind, newlineStarted, codeMarker)
    else if newlineStarted then
      if && codeMarker.Some?
         && |dafnyDocstring| >= |codeMarker.value| + 1
         && dafnyDocstring[..|codeMarker.value| + 1] == codeMarker.value + "\n" then
        // End of code delimiter
        codeMarker.value + ConvertDocstring(dafnyDocstring[|codeMarker.value|..], ind, false, None)
      else if codeMarker.None? && |dafnyDocstring| >= 3 then
        var prefix := dafnyDocstring[..3];
        if prefix == "```" then
          var prefix := GatherSimpleQuotes(dafnyDocstring);
          var remaining := dafnyDocstring[|prefix|..];
          if |remaining| == 0 || remaining[0] == ' ' || remaining[0] == '\n' then
            // ``` becomes ```dafny
            // It's Dafny docstring, we want to ensure we add the Dafny identifier there
            prefix + "dafny" + ConvertDocstring(dafnyDocstring[|prefix|..], ind, false, Some(prefix))
          else if && |remaining| >= 3
                  && remaining[..2] == "rs"
                  && (remaining[2] == ' ' || remaining[2] == '\n') then
            // ```rs becomes ```
            prefix + ConvertDocstring(dafnyDocstring[|prefix|+2..], ind, false, Some(prefix))
          else
            prefix + ConvertDocstring(dafnyDocstring[|prefix|..], ind, false, Some(prefix))
        else
          dafnyDocstring[..1] + ConvertDocstring(dafnyDocstring[1..], ind, false, codeMarker)
      else if && codeMarker.Some?
              && |codeMarker.value| <= |dafnyDocstring|
              && dafnyDocstring[..|codeMarker.value|] == codeMarker.value then
        codeMarker.value + ConvertDocstring(dafnyDocstring[|codeMarker.value|..], ind, false, None)
      else
        dafnyDocstring[..1] + ConvertDocstring(dafnyDocstring[1..], ind, false, codeMarker)
    else
      dafnyDocstring[..1] + ConvertDocstring(dafnyDocstring[1..], ind, false, codeMarker)
  }
  function ToDocstringPrefix(docString: string, ind: string): string {
    if docString == "" then "" else
    DocStringPrefix + ConvertDocstring(docString, ind) + "\n" + ind
  }

  datatype Mod =
      // Rust modules
    | Mod(
        docString: string,
        attributes: seq<Attribute>,
        name: string,
        body: seq<ModDecl>)
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
        case Mod(docString, attributes, name, body) =>
          ToDocstringPrefix(docString, ind) +
          Attribute.ToStringMultiple(attributes, ind) +
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
  datatype TopFnDecl = TopFn(
    docString: string,
    attributes: seq<Attribute>,
    visibility: Visibility, fn: Fn) {
    function ToString(ind: string): string {
      ToDocstringPrefix(docString, ind) +
      Attribute.ToStringMultiple(attributes, ind) +
      visibility.ToString() + fn.ToString(ind)
    }
  }
  datatype Attribute =
    | ApplyAttribute(name: string, derived: seq<string>) {
    static const DeriveClone :=
      ApplyAttribute("derive", ["Clone"])
    static const DeriveCloneAndCopy :=
      ApplyAttribute("derive", ["Clone", "Copy"])
    static const CfgTest :=
      ApplyAttribute("cfg", ["test"])
    static function Name(name: string): Attribute {
      ApplyAttribute(name, [])
    }

    function ToString(ind: string): string {
      match this {
        case ApplyAttribute(name, derived) =>
          var arguments := if |derived| != 0 then
                             "("+SeqToString(derived, (derived: string) => derived, ", ")+")"
                           else "";
          "#["+name+arguments+"]"
      }
    }
    static function ToStringMultiple(attributes: seq<Attribute>, ind: string): string {
      SeqToString(
        attributes,
        (attribute: Attribute) => attribute.ToString(ind) + "\n" + ind)
    }
  }

  datatype Struct =
    Struct(docString: string,
           attributes: seq<Attribute>,
           name: string, typeParams: seq<TypeParamDecl>, fields: Fields)
  {
    function ToString(ind: string): string {
      ToDocstringPrefix(docString, ind) +
      Attribute.ToStringMultiple(attributes, ind) +
      "pub struct " + name +
      TypeParamDecl.ToStringMultiple(typeParams, ind) +
      fields.ToString(ind, fields.NamedFields?) +
      (if fields.NamelessFields? then ";" else "")
    }
  }

  datatype TypeSynonym =
    TypeSynonym(
      docString: string,
      attributes: seq<Attribute>,
      name: string, typeParams: seq<TypeParamDecl>, tpe: Type)
  {
    function ToString(ind: string): string {
      ToDocstringPrefix(docString, ind) +
      Attribute.ToStringMultiple(attributes, ind) +
      "pub type " + name +
      TypeParamDecl.ToStringMultiple(typeParams, ind) + " = " +
      tpe.ToString(ind) + ";"
    }
  }

  datatype Constant =
    Constant(
      docString: string,
      attributes: seq<Attribute>,
      name: string, tpe: Type, value: Expr)
  {
    function ToString(ind: string): string {
      ToDocstringPrefix(docString, ind) +
      Attribute.ToStringMultiple(attributes, ind) +
      "pub const " + name + ": " + tpe.ToString(ind) + " = " +
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
    | EnumCase(docString: string, name: string, fields: Fields)
  {
    function ToString(ind: string, newLine: bool): string {
      ToDocstringPrefix(docString, ind) +
      name + fields.ToString(ind, newLine)
    }
  }

  datatype Enum =
    Enum(
      docString: string,
      attributes: seq<Attribute>,
      name: string, typeParams: seq<TypeParamDecl>,
      variants: seq<EnumCase>)
  {
    function ToString(ind: string): string {
      ToDocstringPrefix(docString, ind) +
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
    @TailRecursion
    static function AddConstraintsMultiple(
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
  const ArcPath := std.MSel("sync").MSel("Arc")

  const RcType := RcPath.AsType()
  const ArcType := ArcPath.AsType()

  const ObjectPath: Path := dafny_runtime.MSel("Object")

  const Object := ObjectPath.AsExpr()

  function ObjectType(underlying: Type): Type {
    ObjectPath.AsType().Apply([underlying])
  }

  const PtrPath: Path := dafny_runtime.MSel("Ptr")

  const BoxPath := std.MSel("boxed").MSel("Box")

  const BoxType := BoxPath.AsType()

  const Ptr := PtrPath.AsExpr()

  function PtrType(underlying: Type): Type {
    PtrPath.AsType().Apply([underlying])
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
    TypeApp(BoxPath.AsType(), [content])
  }
  function BoxNew(content: Expr): Expr {
    BoxPath.AsExpr().FSel("new").Apply([content])
  }

  datatype Path =
    | Global() // ::...   to access other crates
    | Crate()  // crate::... to access modules and imported modules in the same crate
    | Self()   // Self::...
    | PMemberSelect(base: Path, name: string)
  {
    static const DowncastPrefix := "_Downcast_"
    function ToDowncast(): Path {
      match this {
        case PMemberSelect(base, name) => PMemberSelect(base, DowncastPrefix + name)
        case _ => this
      }
    }
    function MSel(name: string): Path {
      PMemberSelect(this, name)
    }
    function MSels(names: seq<string>): Path
      decreases |names|
    {
      if |names| == 0 then this else
      this.MSel(names[0]).MSels(names[1..])
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
    | U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | USIZE
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
    | TMetaData(display: Type, nameonly copySemantics: bool, nameonly overflow: bool)
  {
    /** Removes the synonym and metadata elements of a type */
    function RemoveSynonyms(): (t: Type)
      ensures t == this || t < this
    {
      match this {
        case TSynonym(display, base) =>
          display.RemoveSynonyms()
        case TMetaData(display, _, _) =>
          display.RemoveSynonyms()
        case _ =>
          this
      }
    }
    /** Given a type, returns the _Downcast_* prefix version of that type */
    function ToDowncast(): Option<Type> {
      var t := this.RemoveSynonyms();
      if t.IsRc() then t.RcUnderlying().ToDowncast() else // For Rc-wrapped datatypes
      if t.IsBoxDyn() then t.BoxDynUnderlying().ToDowncast() else // For general traits
      match t {
        case TypeFromPath(path) => Some(TypeFromPath(path.ToDowncast()))
        case TypeApp(baseName, arguments) =>
          var baseNameExpr :- baseName.ToDowncast();
          Some(baseNameExpr.Apply(arguments))
        case TIdentifier(name) =>
          Some(TIdentifier(Path.DowncastPrefix + name))
        case _ => None
      }
    }
    /** Given a type, returns the _Downcast_* prefix version of that type but suitable to call methods */
    function ToDowncastExpr(): Option<Expr> {
      var tpe :- this.ToDowncast();
      tpe.ToExpr()
    }
    /** Converts Name<Args...> (the type) to Name::<Args...> (the expr) */
    function ToExpr(): Option<Expr> {
      match this {
        case TypeFromPath(path) => Some(ExprFromPath(path))
        case TypeApp(baseName, arguments) =>
          var baseNameExpr :- baseName.ToExpr();
          Some(baseNameExpr.ApplyType(arguments))
        case TSynonym(display, base) =>
          display.ToExpr()
        case TMetaData(display, _, _) =>
          display.ToExpr()
        case TIdentifier(name) =>
          Some(Identifier(name))
        case _ => None
      }
    }
    function Expand(): (r: Type)
      ensures !r.TSynonym? && !r.TMetaData? && (!TSynonym? && !TMetaData? ==> r == this)
    {
      if TSynonym? then base.Expand() else
      if TMetaData? then display.Expand() else this
    }
    predicate EndsWithNameThatCanAcceptGenerics() {
      || U8? || U16? || U32? || U64? || U128? || I8? || I16? || I32? || I64? || I128?
      || TIdentifier? || TypeFromPath?
      || (Borrowed? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (BorrowedMut? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (ImplType? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (DynType? && underlying.EndsWithNameThatCanAcceptGenerics())
      || (IntersectionType? && right.EndsWithNameThatCanAcceptGenerics())
      || ((TSynonym? || TMetaData?) && display.EndsWithNameThatCanAcceptGenerics())
    }
    function ReplaceMap(mapping: map<Type, Type>): Type {
      Replace((t: Type) => if t in mapping then mapping[t] else t)
    }
    function Replace(mapping: Type -> Type): Type {
      var r :=
        match this {
          case U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | USIZE | Bool => this
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
          case TMetaData(display, copySemantics, overflow) =>
            this.(display := display.Replace(mapping))
        };
      mapping(r)
    }

    function Fold<T(!new)>(acc: T, f: (T, Type) -> T): T
      // Traverses all types in a random order
    {
      var newAcc := f(acc, this);
      match this {
        case U8 | U16 | U32 | U64 | U128 | I8 | I16 | I32 | I64 | I128 | USIZE | Bool => newAcc
        case TIdentifier(_) => newAcc
        case TypeFromPath(path) => newAcc
        case TypeApp(baseName, arguments) =>
          var newAcc := baseName.Fold(newAcc, f);
          FoldLeft(
            (acc: T, argType: Type) requires argType in arguments => argType.Fold(acc, f),
            newAcc,
            arguments)
        case Borrowed(underlying) => underlying.Fold(newAcc, f)
        case BorrowedMut(underlying) => underlying.Fold(newAcc, f)
        case ImplType(underlying) => underlying.Fold(newAcc, f)
        case DynType(underlying) => underlying.Fold(newAcc, f)
        case TupleType(arguments) =>
          FoldLeft(
            (acc: T, argType: Type) requires argType in arguments => argType.Fold(acc, f),
            newAcc, arguments)
        case FnType(arguments, returnType) =>
          returnType.Fold(
            FoldLeft(
              (acc: T, argType: Type) requires argType in arguments => argType.Fold(acc, f),
              newAcc, arguments),
            f)
        case IntersectionType(left, right) =>
          right.Fold(left.Fold(newAcc, f), f)
        case Array(underlying, size) => underlying.Fold(newAcc, f)
        case TSynonym(display, base) => display.Fold(newAcc, f)
        case TMetaData(display, _, _) => display.Fold(newAcc, f)
      }
    }

    predicate IsAutoSize() {
      U8? || U16? || U32? || U64? || U128? || I8? || I16? || I32? || I64? || I128? || USIZE?
      || (TSynonym? && base.IsAutoSize())
      || (TMetaData? && display.IsAutoSize())
    }

    predicate CanReadWithoutClone() {
      IsAutoSize() || Bool?
      || IsPointer()
      || (TSynonym? && base.CanReadWithoutClone())
      || (TMetaData? && (copySemantics || display.CanReadWithoutClone()))
    }
    predicate IsRcOrBorrowedRc() {
      IsRc() ||
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
        case USIZE() => "usize"
        case Array(underlying, size) => "[" + underlying.ToString(ind) + (if size.Some? then "; " + size.value else "") + "]"
        case TSynonym(display, base) => display.ToString(ind)
        case TMetaData(display, _, _) => display.ToString(ind)
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
        Object.FSel("null").Apply0()
      else
        Ptr.FSel("null").Apply0()
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
    predicate IsBox() {
      match this {
        case TypeApp(TypeFromPath(o), elems1) =>
          o == BoxPath && |elems1| == 1
        case _ => false
      }
    }
    // Every type that needs to be .as_ref() to become purely borrowed
    predicate NeedsAsRefForBorrow() {
      if Borrowed? then
        underlying.IsBox() || underlying.IsRc()
      else
        IsBox() || IsRc()
    }
    function BoxUnderlying(): Type
      requires IsBox()
    {
      match this {
        case TypeApp(TypeFromPath(o), elems1) =>
          elems1[0]
      }
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

    /** Returns true if the type has the shape Rc<T>, so that one can extract T = .arguments[0]
      * Useful to detect rc-wrapped datatypes */
    predicate IsRc() {
      TypeApp? && (baseName == RcType || baseName == ArcType) && |arguments| == 1
    }
    function RcUnderlying(): (t: Type)
      requires IsRc()
      ensures t < this
    {
      arguments[0]
    }

    /** Returns true if the type has the shape Box<dyn T>, so that one can extract T = .arguments[0].underlying
      * Useful to detect general traits */
    predicate IsBoxDyn() {
      this.TypeApp? && this.baseName == BoxType && |arguments| == 1 && arguments[0].DynType?
    }

    function BoxDynUnderlying(): (t: Type)
      requires IsBoxDyn()
      ensures t < this
    {
      arguments[0].underlying
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
  const std_default_Default := std.MSel("default").MSel("Default")
  const DefaultTrait := std_default_Default.AsType()
  const AnyTrait := std.MSel("any").MSel("Any").AsType()
  const StaticTrait := RawType("'static")
  const DafnyType := dafny_runtime.MSel("DafnyType").AsType()
  const DafnyPrint := dafny_runtime.MSel("DafnyPrint").AsType()
  const DafnyTypeEq := dafny_runtime.MSel("DafnyTypeEq").AsType()
  const Eq := std.MSel("cmp").MSel("Eq").AsType()
  const Hash := std.MSel("hash").MSel("Hash").AsType()
  const PartialEq := std.MSel("cmp").MSel("PartialEq").AsType()
  const DafnyInt := dafny_runtime.MSel("DafnyInt").AsType()
  const SyncType := std.MSel("marker").MSel("Sync").AsType()
  const SendType := std.MSel("marker").MSel("Send").AsType()

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
    | Trait(
        docString: string,
        attributes: seq<Attribute>,
        typeParams: seq<TypeParamDecl>,
        tpe: Type,
        parents: seq<Type>,
        body: seq<ImplMember>)
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
      ToDocstringPrefix(docString, ind) +
      Attribute.ToStringMultiple(attributes, ind) +
      "pub trait " + tpe.ToString(ind) + parents + where
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }

  datatype Impl =
    | ImplFor(typeParams: seq<TypeParamDecl>, tpe: Type, forType: Type, body: seq<ImplMember>)
    | Impl(typeParams: seq<TypeParamDecl>, tpe: Type, body: seq<ImplMember>)
  {
    function ToString(ind: string): string {
      "impl" + TypeParamDecl.ToStringMultiple(typeParams, ind) + " " + tpe.ToString(ind)
      + (if ImplFor? then "\n" + ind + IND + "for " + forType.ToString(ind + IND) else "")
      + " {" +
      SeqToString(body, (member: ImplMember) => "\n" + ind + IND + member.ToString(ind + IND), "")
      + (if |body| == 0 then "" else "\n" + ind) + "}"
    }
  }
  datatype ImplMember =
    | RawImplMember(content: string)
    | TypeDeclMember(name: string, rhs: Type) // When implementing traits
    | FnDecl(docString: string, attributes: seq<Attribute>, pub: Visibility, fun: Fn)
    | ImplMemberMacro(expr: Expr)
  {
    function ToString(ind: string): string {
      if FnDecl? then
        ToDocstringPrefix(docString, ind) +
        Attribute.ToStringMultiple(attributes, ind) +
        pub.ToString() + fun.ToString(ind)
      else if ImplMemberMacro? then expr.ToString(ind) + ";"
      else if TypeDeclMember? then "type " + name + " = " + rhs.ToString(ind) + ";"
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
    static function ImplicitlyTyped(name: string): Formal {
      Formal(name, TIdentifier("_"))
    }
    function Replace(ft: Type -> Type): Formal {
      Formal(name, tpe.Replace(ft))
    }
    function Fold<T(!new)>(acc: T, ft: (T, Type) -> T): T {
      tpe.Fold(acc, ft)
    }
    function ToString(ind: string): string {
      if name == "self" && tpe.Expand() == SelfOwned then name
      else if name == "self" && tpe == SelfBorrowed then "&" + name
      else if name == "self" && tpe == SelfBorrowedMut then "&mut " + name
      else if tpe.TIdentifier? && tpe.name == "_" then
        name
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
    function Replace(mapping: Expr -> Expr, mappingType: Type -> Type): MatchCase {
      MatchCase(pattern, rhs.Replace(mapping, mappingType))
    }
    function Fold<T(!new)>(acc: T, f: (T, Expr) -> T, ft: (T, Type) -> T): T {
      rhs.Fold(acc, f, ft)
    }
    function ToString(ind: string): string
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
    function Replace(f: Expr -> Expr, ft: Type -> Type): AssignIdentifier {
      AssignIdentifier(identifier, rhs.Replace(f, ft))
    }
    function Fold<T(!new)>(acc: T, f: (T, Expr) -> T, ft: (T, Type) -> T): T {
      rhs.Fold(acc, f, ft)
    }
    function ToString(ind: string): string
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
    | TraitCast(leftTpe: Type, tpe: Type)            // < leftTpe as tpe >
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
    | CallType(obj: Expr, typeArguments: seq<Type>) // obj::<...type parameters>
    | Call(obj: Expr, arguments: seq<Expr>)          // obj(...arguments)
    | Select(obj: Expr, name: string)                // obj.name
    | SelectIndex(obj: Expr, range: Expr)            // obj[range]
    | ExprFromPath(path: Path)                       // ::dafny_runtime::int! for example
    | FunctionSelect(obj: Expr, name: string)        // objType::name
    | Lambda(params: seq<Formal>, retType: Option<Type>, body: Expr) // move |<params>| -> retType { body }
  {
    function Replace(f: Expr -> Expr, ft: Type -> Type): Expr {
      var r :=
        match this {
          case RawExpr(content) => this
          case ExprFromType(tpe) => ExprFromType(tpe.Replace(ft))
          case Identifier(name) => this
          case Match(matchee, cases) =>
            Match(matchee.Replace(f, ft),
                  Std.Collections.Seq.Map(
                    c requires c in cases => c.Replace(f, ft), cases))
          case StmtExpr(stmt, rhs) =>
            StmtExpr(stmt.Replace(f, ft), rhs.Replace(f, ft))
          case Block(underlying) =>
            Block(underlying.Replace(f, ft))
          case StructBuild(underlying, assignments) =>
            StructBuild(underlying.Replace(f, ft), Std.Collections.Seq.Map(
                          a requires a in assignments =>
                            a.Replace(f, ft),
                          assignments))
          case Tuple(arguments) =>
            Tuple(
              Std.Collections.Seq.Map(
                e requires e in arguments =>
                  e.Replace(f, ft), arguments))
          case UnaryOp(op1, underlying, format) =>
            UnaryOp(op1, underlying.Replace(f, ft), format)
          case BinaryOp(op2, left, right, format2) =>
            BinaryOp(op2, left.Replace(f, ft), right.Replace(f, ft), format2)
          case TypeAscription(left, tpe) => TypeAscription(left.Replace(f, ft), tpe.Replace(ft))
          case TraitCast(leftTpe, tpe) => TraitCast(leftTpe.Replace(ft), tpe.Replace(ft))
          case LiteralInt(value) => this
          case LiteralBool(bvalue) => this
          case LiteralString(value, binary, verbatim) => this
          case DeclareVar(declareType, name, optType, optRhs) =>
            DeclareVar(
              declareType, name,
              if optType.None? then optType else Some(optType.value.Replace(ft)),
              if optRhs.None? then optRhs else Some(optRhs.value.Replace(f, ft)))
          case Assign(names, rhs) => Assign(names, rhs.Replace(f, ft))
          case IfExpr(cond, thn, els) => IfExpr(cond.Replace(f, ft), thn.Replace(f, ft), els.Replace(f, ft))
          case Loop(optCond, underlying) =>
            Loop(if optCond.None? then None else Some(optCond.value.Replace(f, ft)), underlying.Replace(f, ft))
          case For(name, range, body) =>
            For(name, range.Replace(f, ft), body.Replace(f, ft))
          case Labelled(lbl, underlying) =>
            Labelled(lbl, underlying.Replace(f, ft))
          case Break(optLbl) => this
          case Continue(optLbl) => this
          case Return(optExpr) => Return(if optExpr.None? then None else Some(optExpr.value.Replace(f, ft)))
          case CallType(obj, typeArguments) =>
            CallType(obj.Replace(f, ft), Std.Collections.Seq.Map((tp: Type) => tp.Replace(ft), typeArguments))
          case Call(obj, arguments) =>
            Call(
              obj.Replace(f, ft),
              Std.Collections.Seq.Map((a: Expr) requires a < this => a.Replace(f, ft), arguments))
          case Select(obj, name) => Select(obj.Replace(f, ft), name)
          case SelectIndex(obj, range) => SelectIndex(obj.Replace(f, ft), range.Replace(f, ft))
          case ExprFromPath(path) => ExprFromPath(path)
          case FunctionSelect(obj, name) => FunctionSelect(obj.Replace(f, ft), name)
          case Lambda(params, retType, body) =>
            Lambda(
              Std.Collections.Seq.Map(
                (f: Formal) requires f < this => f.Replace(ft),
                params),
              if retType.None? then None else Some(retType.value.Replace(ft)),
              body.Replace(f, ft))
        };
      f(r)
    }
    function Fold<T(!new)>(acc: T, f: (T, Expr) -> T, ft: (T, Type) -> T): T {
      var acc := f(acc, this);
      match this {
        case RawExpr(content) => acc
        case ExprFromType(tpe) => tpe.Fold(acc, ft)
        case Identifier(name) => acc
        case Match(matchee, cases) =>
          var acc := matchee.Fold(acc, f, ft);
          FoldLeft(
            (acc: T, c: MatchCase) requires c in cases => c.Fold(acc, f, ft),
            acc,
            cases)
        case StmtExpr(stmt, rhs) =>
          rhs.Fold(stmt.Fold(acc, f, ft), f, ft)
        case Block(underlying) => underlying.Fold(acc, f, ft)
        case StructBuild(underlying, assignments) =>
          FoldLeft(
            (acc: T, c: AssignIdentifier) requires c in assignments => c.Fold(acc, f, ft),
            underlying.Fold(acc, f, ft),
            assignments
          )
        case Tuple(arguments) =>
          FoldLeft(
            (acc: T, e: Expr) requires e in arguments => e.Fold(acc, f, ft),
            acc,
            arguments
          )
        case UnaryOp(op1, underlying, format) => underlying.Fold(acc, f, ft)
        case BinaryOp(op2, left, right, format2) =>
          right.Fold(left.Fold(acc, f, ft), f, ft)
        case TypeAscription(left, tpe) => tpe.Fold(left.Fold(acc, f, ft), ft)
        case TraitCast(leftTpe, tpe) => tpe.Fold(leftTpe.Fold(acc, ft), ft)
        case LiteralInt(value) => acc
        case LiteralBool(bvalue) => acc
        case LiteralString(value, binary, verbatim) => acc
        case DeclareVar(declareType, name, optType, optRhs) =>
          var acc := if optType.None? then acc else optType.value.Fold(acc, ft);
          if optRhs.None? then acc else optRhs.value.Fold(acc, f, ft)
        case Assign(names, rhs) => rhs.Fold(acc, f, ft)
        case IfExpr(cond, thn, els) =>
          var acc := cond.Fold(acc, f, ft);
          var acc := thn.Fold(acc, f, ft);
          els.Fold(acc, f, ft)
        case Loop(optCond, underlying) =>
          var acc := if optCond.None? then acc else optCond.value.Fold(acc, f, ft);
          underlying.Fold(acc, f, ft)
        case For(name, range, body) =>
          var acc := range.Fold(acc, f, ft);
          body.Fold(acc, f, ft)
        case Labelled(lbl, underlying) => underlying.Fold(acc, f, ft)
        case Break(optLbl) => acc
        case Continue(optLbl) => acc
        case Return(optExpr) => if optExpr.None? then acc else optExpr.value.Fold(acc, f, ft)
        case CallType(obj, typeArguments) =>
          var acc := obj.Fold(acc, f, ft);
          FoldLeft(
            (acc: T, t: Type) requires t in typeArguments =>
              t.Fold(acc, ft),
            acc,
            typeArguments
          )
        case Call(obj, arguments) =>
          var acc := obj.Fold(acc, f, ft);
          FoldLeft(
            (acc: T, e: Expr) requires e in arguments =>
              e.Fold(acc, f, ft),
            acc,
            arguments
          )
        case Select(obj, name) =>
          obj.Fold(acc, f, ft)
        case SelectIndex(obj, range) =>
          range.Fold(obj.Fold(acc, f, ft), f, ft)
        case ExprFromPath(path) => acc
        case FunctionSelect(obj, name) =>
          obj.Fold(acc, f, ft)
        case Lambda(params, retType, body) =>
          var acc := FoldLeft(
                       (acc: T, param: Formal) requires param in params =>
                         param.Fold(acc, ft),
                       acc, params);
          var acc := if retType.None? then acc else retType.value.Fold(acc, ft);
          body.Fold(acc, f, ft)
      }
    }

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
        case TraitCast(leftTpe, tpe) => Precedence(1)
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
            case "=>" => // Not a Rust operation, used in the map macro syntax
              PrecedenceAssociativity(120, RightToLeft)
            case _ => PrecedenceAssociativity(0, RequiresParentheses)
          }
        case Lambda(_, _, _) => PrecedenceAssociativity(300, LeftToRight)
        case _ => UnknownPrecedence()
      }

    predicate LeftRequiresParentheses(left: Expr) {
      printingInfo.NeedParenthesesForLeft(left.printingInfo)
    }
    function LeftParentheses(left: Expr): (string, string) {
      if LeftRequiresParentheses(left) then
        ("(", ")")
      else
        ("", "")
    }

    predicate RightRequiresParentheses(right: Expr) {
      printingInfo.NeedParenthesesForRight(right.printingInfo)
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
        case Identifier(id) => Some(id)
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
    {
      match this {
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
                      (c: MatchCase) requires c in cases =>
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
                        requires assignment in assignments
                        =>
                          "\n" + ind + IND + assignment.rhs.ToString(ind + IND), ",") +
            (if |assignments| > 1 then "\n" + ind else "") + ")"
          else
            name.ToString(ind) + " {" +
            SeqToString(assignments, (assignment: AssignIdentifier)
                        requires assignment in assignments
                        =>
                          "\n" + ind + IND + assignment.ToString(ind + IND), ",") +
            (if |assignments| > 0 then "\n" + ind else "") + "}"
        case Tuple(arguments) =>
          "(" +
          SeqToString(arguments, (arg: Expr)
                      requires arg in arguments
                      =>
                        "\n" + ind + IND + arg.ToString(ind + IND), ",") +
          (if |arguments| > 0 then "\n" + ind else "") + ")"

        case UnaryOp(op, underlying, format) =>
          var isPattern := |op| >= 1 && op[0..1] == "{";
          var isUnsafe := op == "unsafe";
          var (leftP, rightP) :=
            if !isPattern && !isUnsafe && printingInfo.NeedParenthesesFor(underlying.printingInfo) then
              ("(", ")")
            else
              ("", "");
          var opToRight := op == "?" || (
                             |op| >= 2 && op[0..2] == "/*" // comment
                           ) || isPattern;
          var leftOp := if opToRight then "" else op;
          var leftOp := if (op == "&mut" || isUnsafe) && leftP != "(" then leftOp + " " else leftOp;
          var rightOp := if opToRight then op else "";
          leftOp + leftP  + underlying.ToString(ind) + rightP + rightOp
        case TypeAscription(left, tpe) =>
          var (leftLeftP, leftRightP) := LeftParentheses(left);
          leftLeftP + left.ToString(IND) + leftRightP + " as " + tpe.ToString(IND)
        case TraitCast(leftTpe, tpe) =>
          "<" + leftTpe.ToString(IND) + " as " + tpe.ToString(IND) + ">"
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
                                                                   (index: Expr) requires index in indices => index.ToString(ind + IND), "][")
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
          leftCallP + SeqToString(args, (arg: Expr) requires arg in args => arg.ToString(ind + IND), ", ")+ rightCallP
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
             "{\n" + ind + IND + body.ToString(ind + IND) + "\n" + ind + "}"
           else body.ToString(ind))
        case r =>
          assert r.RawExpr?; AddIndent(r.content, ind)
      }
    }
    function And(rhs2: Expr): Expr {
      if this == LiteralBool(true) then rhs2 else
      BinaryOp("&&", this, rhs2, Format.BinaryOpFormat.NoFormat)
    }
    function Equals(rhs2: Expr): Expr {
      BinaryOp("==", this, rhs2, Format.BinaryOpFormat.NoFormat)
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
    function ApplyType(typeArguments: seq<Type>): Expr {
      if |typeArguments| == 0 then this else
      CallType(this, typeArguments)
    }
    function ApplyType1(typeArgument: Type): Expr {
      CallType(this, [typeArgument])
    }
    function Apply(arguments: seq<Expr>): Expr {
      Call(this, arguments)
    }

    function Apply1(argument: Expr): Expr {
      Call(this, [argument])
    }

    function Apply0(): Expr {
      Call(this, [])
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
      Select(this, "clone").Apply0()
    }

    predicate IsBorrow() {
      UnaryOp? && op1 == "&"
    }
  }

  function Unsafe(underlying: Expr): Expr {
    UnaryOp("unsafe", underlying, Format.UnaryOpFormat.NoFormat)
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

  const std_default_Default_default := std_default_Default.FSel("default").Apply0()

  function IntoUsize(underlying: Expr): Expr {
    dafny_runtime.MSel("DafnyUsize").FSel("into_usize").Apply1(underlying)
  }

  datatype Fn =
    Fn(name: string, typeParams: seq<TypeParamDecl>, formals: seq<Formal>,
       returnType: Option<Type>,
       body: Option<Expr>)
  {
    function ToString(ind: string): string {
      "fn " + name + TypeParamDecl.ToStringMultiple(typeParams, ind) +
      "(" + SeqToString(formals, (formal: Formal) => formal.ToString(ind), ", ") + ")" +
      (match returnType case Some(t) => " -> " + t.ToString(ind) case _ => "") +
      match body {
        case None => ";"
        case Some(body) =>
          " {\n" + ind + IND +
          body.ToString(ind + IND) +
          "\n" + ind + "}"
      }
    }
  }
  predicate IsBorrowUpcastBox(r: Expr) {
    match r {
      case UnaryOp("&", Call(Call(CallType(name, targs0), args0), args1), _) =>
        name == dafny_runtime.MSel("upcast_box").AsExpr() && |args0| == 0 &&
        |args1| == 1 &&
        match args1[0] {
          case Call(Select(Identifier("self"), clone), args2) =>
            |args2| == 0
          case _ => false
        }
      case _ => false
    }
  }

  /** Placeholder when there is no Rust docstring */
  const NoDoc := ""

  /** Placeholder when there are no Rust attributes */
  const NoAttr: seq<Attribute> := []
}
