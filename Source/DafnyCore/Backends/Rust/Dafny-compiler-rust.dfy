include "../Dafny/AST.dfy"

// Dafny to Rust compilation tenets:
// - The Compiled Dafny AST should be minimal
// - The generated code should look idiomatic and close to the original Dafny file if possible
module {:extern "DCOMP"} DafnyToRustCompiler {
  import opened DafnyToRustCompilerDefinitions
  import FactorPathsOptimization
  import ExpressionOptimization

  import opened DAST
  import Strings = Std.Strings
  import Std
  import opened Std.Wrappers
  import R = RAST
  import opened DafnyCompilerRustUtils

  class COMP {
    const charType: CharType
    const pointerType: PointerType
    const rootType: RootType

    const thisFile: R.Path := if rootType.RootCrate? then R.crate else R.crate.MSel(rootType.moduleName)

    const DafnyChar := if charType.UTF32? then "DafnyChar" else "DafnyCharUTF16"
    const conversions := if charType.UTF32? then "unicode_chars_true" else "unicode_chars_false"
    const DafnyCharUnderlying := if charType.UTF32? then R.RawType("char") else R.RawType("u16")
    const string_of := if charType.UTF32? then "string_of" else "string_utf16_of"
    const allocate :=
      if pointerType.Raw? then "allocate" else "allocate_object"
    const allocate_fn := "_" + allocate
    const update_field_uninit_macro :=
      if pointerType.Raw? then "update_field_uninit!" else "update_field_uninit_object!"
    const update_field_mut_uninit_macro :=
      if pointerType.Raw? then "update_field_mut_uninit!" else "update_field_mut_uninit_object!"
    const thisInConstructor :=
      if pointerType.Raw? then R.Identifier("this") else R.Identifier("this").Clone()
    const array_construct :=
      if pointerType.Raw? then "construct" else "construct_object"
    const modify_macro := R.dafny_runtime.MSel(if pointerType.Raw? then "modify!" else "md!").AsExpr()
    const read_macro := R.dafny_runtime.MSel(if pointerType.Raw? then "read!" else "rd!").AsExpr()
    const modify_mutable_field_macro := R.dafny_runtime.MSel("modify_field!").AsExpr()
    const read_mutable_field_macro := R.dafny_runtime.MSel("read_field!").AsExpr()

    function Object(underlying: R.Type): R.Type {
      if pointerType.Raw? then R.PtrType(underlying) else R.ObjectType(underlying)
    }
    const placebos_usize := if pointerType.Raw? then "placebos_usize" else "placebos_usize_object"
    const update_field_if_uninit_macro :=
      if pointerType.Raw? then "update_field_if_uninit!" else "update_field_if_uninit_object!"
    const update_field_mut_if_uninit_macro :=
      if pointerType.Raw? then "update_field_mut_if_uninit!" else "update_field_mut_if_uninit_object!"
    const Upcast :=
      if pointerType.Raw? then "Upcast" else "UpcastObject"
    const UpcastFnMacro :=
      Upcast + "Fn!"
    const upcast :=
      if pointerType.Raw? then "upcast" else "upcast_object"

    const downcast :=
      if pointerType.Raw? then "cast!" else "cast_object!"


    var error: Option<string>

    var optimizations: seq<R.Mod -> R.Mod>

    constructor(charType: CharType, pointerType: PointerType, rootType: RootType) {
      this.charType := charType;
      this.pointerType := pointerType;
      this.rootType := rootType;
      this.error := None; // If error, then the generated code contains <i>Unsupported: .*</i>
      this.optimizations := [
        ExpressionOptimization.apply,
        FactorPathsOptimization.apply(thisFile)];
      new;
    }

    predicate HasAttribute(attributes: seq<Attribute>, name: string) {
      exists attribute <- attributes :: attribute.name == name && |attribute.args| == 0
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
        var attributes := [];
        if HasAttribute(mod.attributes, "rust_cfg_test") {
          attributes := [R.RawAttribute("#[cfg(test)]")];
        }
        var body, allmodules := GenModuleBody(mod, mod.body.value, containingPath + [Ident.Ident(innerName)]);
        if optExtern.SimpleExtern? {
          if mod.requiresExterns {
            body := [R.UseDecl(R.Use(R.PUB, thisFile.MSel(DAFNY_EXTERN_MODULE).MSels(SplitRustPathElement(ReplaceDotByDoubleColon(optExtern.overrideName))).MSel("*")))] + body;
          }
        } else if optExtern.AdvancedExtern? {
          error := Some("Externs on modules can only have 1 string argument");
        } else if optExtern.UnsupportedExtern? {
          error := Some(optExtern.reason);
        }
        s := GatheringModule.MergeSeqMap(
          GatheringModule.Wrap(ContainingPathToRust(containingPath), R.Mod(modName, attributes, body)),
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
        if !field.isConstant {
          fieldType := R.dafny_runtime.MSel("Field").AsType().Apply([fieldType]);
        }
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
            var default := R.std_default_Default_default;
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
            R.std.MSel("marker").MSel("PhantomData").AsExpr())];
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
                   R.dafny_runtime.MSel(allocate).AsExpr().ApplyType1(R.SelfOwned).Apply0()
                 ))
          )
        ] + implBody;
      }

      var selfTypeForImpl;
      if extern.NoExtern? || extern.UnsupportedExtern? {
        selfTypeForImpl := R.TIdentifier(className);
      } else if extern.AdvancedExtern? {
        selfTypeForImpl := R.crate.MSels(extern.enclosingModule).MSel(extern.overrideName).AsType();
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
      // Add test methods
      var testMethods := [];
      if className == "_default" {
        for i := 0 to |c.body| {
          var m := match c.body[i] case Method(m) => m;
          if HasAttribute(m.attributes, "test") && |m.params| == 0 {
            var fnName := escapeName(m.name);
            testMethods := testMethods + [
              R.TopFnDecl(
                R.TopFn(
                  [R.RawAttribute("#[test]")], R.PUB,
                  R.Fn(
                    fnName, [], [], None,
                    "",
                    Some(R.Identifier("_default").FSel(fnName).Apply([])))
                ))
            ];
          }
        }
        s := s + testMethods;
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
          fnBody := fnBody.Apply1(R.std_default_Default_default);
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
                    [ R.Formal.selfBorrowed,
                      R.Formal("_formatter", R.BorrowedMut(R.std.MSel("fmt").MSel("Formatter").AsType())),
                      R.Formal("in_seq", R.Type.Bool)],
                    Some(R.std.MSel("fmt").MSel("Result").AsType()),
                    "",
                    Some(R.dafny_runtime.MSel("DafnyPrint").AsExpr().FSel("fmt_print").Apply(
                           [ R.Borrow(R.self.Sel("0")),
                             R.Identifier("_formatter"),
                             R.Identifier("in_seq")])))
             )]))];
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
                    Some(R.Borrow(R.self.Sel("0")))))]))];
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

    function write(r: R.Expr, final: bool := false): R.Expr {
      var result :=
        R.Identifier("write!").Apply([
                                       R.Identifier("_formatter"),
                                       r]);
      if final then
        result
      else
        R.UnaryOp("?", result, Format.UnaryOpFormat.NoFormat)
    }

    function writeStr(s: string, final: bool := false): R.Expr {
      write(R.LiteralString(s, binary := false, verbatim := false))
    }

    method GenDatatype(c: Datatype) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls, whereConstraints := GenTypeParameters(c.typeParams);
      var datatypeName := escapeName(c.name);
      var ctors: seq<R.EnumCase> := [];
      var variances := Std.Collections.Seq.Map((typeParamDecl: TypeArgDecl) => typeParamDecl.variance, c.typeParams);
      var singletonConstructors := [];
      var usedTypeParams: set<string> := {};
      for i := 0 to |c.ctors| {
        var ctor := c.ctors[i];
        var ctorArgs: seq<R.Field> := [];
        var isNumeric := false;
        if |ctor.args| == 0 {
          var instantiation := R.StructBuild(R.Identifier(datatypeName).FSel(escapeName(ctor.name)), []);
          if IsRcWrapped(c.attributes) {
            instantiation := R.RcNew(instantiation);
          }
          singletonConstructors := singletonConstructors + [
            instantiation
          ];
        }
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
              var rhs: R.Expr;
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
                  rhs := R.std.MSel("ops").MSel("Deref").AsExpr().FSel("deref").Apply1(R.Borrow(R.Identifier(hasMatchingField.value).Sel("0")));
                } else {
                  rhs := R.Identifier(hasMatchingField.value);
                }
              } else {
                rhs := UnreachablePanicIfVerified(pointerType, "field does not exist on this variant");
              }
              var ctorMatch := R.MatchCase(R.RawPattern(pattern), rhs);
              cases := cases + [ctorMatch];
            }

            if |c.typeParams| > 0 && |unusedTypeParams| > 0 {
              cases := cases + [
                R.MatchCase(R.RawPattern(datatypeName + "::_PhantomVariant(..)"), UnreachablePanicIfVerified(pointerType, ""))
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
        var printRhs := writeStr(ctorName + (if ctor.hasAnyArgs then "(" else ""));
        var hashRhs := InitEmptyExpr();
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
              hashRhs.Then(R.std.MSel("hash").MSel("Hash").AsExpr().FSel("hash").Apply([R.Identifier(patternName), R.Identifier("_state")]));

          ctorMatchInner := ctorMatchInner + patternName + ", ";

          if (j > 0) {
            printRhs := printRhs.Then(writeStr(", "));
          }

          printRhs := printRhs.Then(
            if formalType.Arrow? then
              writeStr("<function>")
            else
              R.UnaryOp("?",
                        R.dafny_runtime.MSel("DafnyPrint").AsExpr().FSel("fmt_print").Apply([
                                                                                              R.Identifier(patternName),
                                                                                              R.Identifier("_formatter"),
                                                                                              R.LiteralBool(false)
                                                                                            ]), Format.UnaryOpFormat.NoFormat)
          );

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
          printRhs := printRhs.Then(writeStr(")"));
        }

        printRhs := printRhs.Then(R.Identifier("Ok").Apply([R.Tuple([])]));

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
          R.MatchCase(
            R.RawPattern(datatypeName + "::_PhantomVariant(..)"),
            R.Block(UnreachablePanicIfVerified(pointerType)))
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
      var datatypeType := R.TypeApp(R.TIdentifier(datatypeName), rTypeParams);
      s := s + [
        DebugImpl(rTypeParamsDecls, datatypeType, rTypeParams),
        PrintImpl(rTypeParamsDecls, datatypeType, rTypeParams, printImplBody)
      ];
      if |rCoerceTypeParams| > 0 {
        var coerceImplBody := R.Match(
          R.Identifier("this"),
          coerceImplBodyCases);
        s := s + [
          CoerceImpl(rTypeParamsDecls, datatypeName, datatypeType, rCoerceTypeParams, coerceArguments, coerceTypes, coerceImplBody)
        ];
      }

      if |singletonConstructors| == |c.ctors| {
        var instantiationType :=
          if IsRcWrapped(c.attributes) then
            R.Rc(datatypeType)
          else
            datatypeType;
        s := s + [
          SingletonsImpl(rTypeParamsDecls, datatypeType, instantiationType, singletonConstructors)];
      }

      // Implementation of Eq when c supports equality
      if cIsEq {
        s := s + [
          R.ImplDecl(
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
      s := s + [
        R.ImplDecl(
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
            R.AssignIdentifier(
              escapeVar(dtor.formal.name),
              R.std.MSel("default").MSel("Default").AsExpr().FSel("default").Apply0())
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

    method GenPath(p: seq<Ident>, escape: bool := true) returns (r: R.Path) {
      if |p| == 0 {
        return R.Self();
      } else {
        var p := p; // Make p mutable
        var name := p[0].id.dafny_name;
        if |name| >= 2 && name[0..2] == "::" {
          r := R.Global();
          p := p[0 := Ident.Ident(Name(name[2..]))];
        } else if p[0].id.dafny_name == "_System" {
          r := R.dafny_runtime;
        } else {
          r := thisFile;
        }
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
            r := r.MSels(SplitRustPathElement(ReplaceDotByDoubleColon(name.dafny_name)));
          }
        }
      }
    }

    method GenPathType(p: seq<Ident>) returns (t: R.Type) {
      var p := GenPath(p, true);
      t := p.AsType();
    }

    method GenPathExpr(p: seq<Ident>, escape: bool := true) returns (e: R.Expr) {
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
            case Native => s := R.Type.USIZE;
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
          var selfFormal := R.Formal.selfBorrowed;
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
              tpe := R.SelfBorrowed;
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
      var preBody := InitEmptyExpr();
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
      generated := InitEmptyExpr();
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

        case Select(on, field, isConstant) => {
          var fieldName := escapeVar(field);
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

          match onExpr { // Particular case of the constructor, we don't want the previous value to be dropped if it's assigned the first time
            case Call(Select(Identifier("this"), "clone"), _)
              | Identifier("this")
              | UnaryOp("&", Identifier("this"), _) =>
              var isAssignedVar := AddAssignedPrefix(fieldName);
              if isAssignedVar in newEnv.names {
                var update_field_uninit :=
                  if isConstant then
                    update_field_uninit_macro
                  else
                    update_field_mut_uninit_macro;
                generated := R.dafny_runtime.MSel(update_field_uninit).AsExpr().Apply(
                  [ thisInConstructor,
                    R.Identifier(fieldName),
                    R.Identifier(isAssignedVar),
                    rhs]);
                newEnv := newEnv.RemoveAssigned(isAssignedVar);
              } else {
                // Already assigned, safe to override
                generated := modify_mutable_field_macro.Apply([read_macro.Apply1(thisInConstructor).Sel(fieldName), rhs]);
              }
            case _ =>
              if onExpr != R.Identifier("self") {
                onExpr := read_macro.Apply1(onExpr);
              }
              generated := modify_mutable_field_macro.Apply([onExpr.Sel(fieldName), rhs]);
          }
          readIdents := recIdents;
          needsIIFE := false;
        }

        case Index(on, indices) => {
          // Retrieve the pointer to the array
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;

          onExpr := modify_macro.Apply1(onExpr);

          var r := InitEmptyExpr();

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
          generated := InitEmptyExpr();
          readIdents := {};
          newEnv := env;
          for i := 0 to |fields| {
            var field := fields[i];
            var fieldName := escapeVar(field.formal.name);
            var fieldTyp := GenType(field.formal.typ, GenTypeContext.default());
            var isAssignedVar := AddAssignedPrefix(fieldName);
            if isAssignedVar in newEnv.names {
              assume {:axiom} InitializationValue(field.formal.typ) < stmt; // Needed for termination
              var rhs, _, _ := GenExpr(InitializationValue(field.formal.typ), selfIdent, env, OwnershipOwned);
              readIdents := readIdents + {isAssignedVar};
              var update_if_uninit :=
                if field.isConstant then update_field_if_uninit_macro else update_field_mut_if_uninit_macro;
              generated := generated.Then(R.dafny_runtime.MSel(update_if_uninit).AsExpr().Apply(
                                            [ R.Identifier("this"), R.Identifier(fieldName), R.Identifier(isAssignedVar), rhs]));
              newEnv := newEnv.RemoveAssigned(isAssignedVar);
            }
          }
        }
        case DeclareVar(name, typ, Some(expression)) => {
          var tpe := GenType(typ, GenTypeContext.default());
          var varName := escapeVar(name);
          var hasCopySemantics := tpe.CanReadWithoutClone();
          if expression.InitializationValue? && !hasCopySemantics {
            generated := R.DeclareVar(R.MUT, varName, None, Some(R.MaybePlaceboPath.AsExpr().ApplyType1(tpe).FSel("new").Apply0()));
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
            over := over.Sel("cloned").Apply0();
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
          generated := InitEmptyExpr();

          if selfIdent != NoSelf {
            var selfClone, _, _ := GenIdent(selfIdent.rSelfName, selfIdent, Environment.Empty(), OwnershipOwned);
            generated := generated.Then(R.DeclareVar(R.MUT, "_this", None, Some(selfClone)));
          }
          newEnv := env;
          var loopBegin := R.RawExpr("");
          for paramI := 0 to |env.names| {
            var param := env.names[paramI];
            if param == "_accumulator" {
              continue; // This is an already mutable variable handled by SinglePassCodeGenerator
            }
            var paramInit, _, _ := GenIdent(param, selfIdent, env, OwnershipOwned);
            var recVar := TailRecursionPrefix + Strings.OfNat(paramI);
            generated := generated.Then(R.DeclareVar(R.MUT, recVar, None, Some(paramInit)));
            if param in env.types {
              // We made the input type owned by the variable.
              // so we can remove borrow annotations.
              var declaredType := env.types[param].ToOwned();
              newEnv := newEnv.AddAssigned(param, declaredType);
              newEnv := newEnv.AddAssigned(recVar, declaredType);
            }
            // Redeclare the input parameter, take ownership of the recursive value
            loopBegin := loopBegin.Then(R.DeclareVar(R.CONST, param, None, Some(R.Identifier(recVar))));
          }
          var bodyExpr, bodyIdents, bodyEnv := GenStmts(body, if selfIdent != NoSelf then ThisTyped("_this", selfIdent.dafnyType) else NoSelf, newEnv, false, earlyReturn);
          readIdents := bodyIdents;
          generated := generated.Then(
            R.Labelled("TAIL_CALL_START",
                       R.Loop(None,
                              loopBegin.Then(bodyExpr))));
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
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
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
                          onExpr := read_macro.Apply1(onExpr);
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

    method FromOwned(r: R.Expr, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      modifies this
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
        out := Error("Conversion from Borrowed or BorrowedMut to BorrowedMut", r);
        out := modify_macro.Apply1(out);
        resultingOwnership := OwnershipBorrowedMut;
      }
    }

    method FromOwnership(r: R.Expr, ownership: Ownership, expectedOwnership: Ownership)
      returns (out: R.Expr, resultingOwnership: Ownership)
      requires ownership != OwnershipAutoBorrowed
      modifies this
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
              r := R.TypeAscription(R.LiteralInt(i), genType);
            }
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              r := R.dafny_runtime.MSel("BigRational").AsExpr().FSel("new").Apply(
                [ R.dafny_runtime.MSel("BigInt").AsExpr().FSel("parse_bytes").Apply(
                    [ R.LiteralString(n, binary := true, verbatim := false),
                      R.LiteralInt("10")
                    ]).Sel("unwrap").Apply0(),
                  R.dafny_runtime.MSel("BigInt").AsExpr().FSel("parse_bytes").Apply(
                    [ R.LiteralString(d, binary := true, verbatim := false),
                      R.LiteralInt("10")
                    ]).Sel("unwrap").Apply0()
                ]);
            }
            case o => {
              var genType := GenType(o, GenTypeContext.default());
              r := R.TypeAscription(
                R.BinaryOp("/",
                           R.LiteralInt(n).Sel("0"),
                           R.LiteralInt(d).Sel("0"), Format.BinaryOpFormat.NoFormat), genType);
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
          if !charType.UTF32? {
            r := R.TypeAscription(r, R.U16);
          } else {
            r :=
              R.global.MSel("std").MSel("primitive")
              .MSel("char").FSel("from_u32")
              .Apply1(r).Sel("unwrap").Apply0();
          }
          r := R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case Literal(Null(tpe)) => {
          var tpeGen := GenType(tpe, GenTypeContext.default());
          if pointerType.Raw? {
            r := R.dafny_runtime.MSel("Ptr").AsExpr().FSel("null").Apply([]);
          } else {
            r := R.TypeAscription(R.dafny_runtime.MSel("Object").AsExpr().Apply1(R.Identifier("None")), tpeGen);
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
      var becomesLeftCallsRight := BecomesLeftCallsRight(op);
      var becomesRightCallsLeft := BecomesRightCallsLeft(op);
      var expectedLeftOwnership :=
        if becomesLeftCallsRight then OwnershipAutoBorrowed
        else if becomesRightCallsLeft then OwnershipBorrowed
        else OwnershipOwned;
      var expectedRightOwnership :=
        if becomesLeftCallsRight then OwnershipBorrowed
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
                    // Need to make comp/rust/traits.dfy to pass with --raw-pointer)
                    r := Error("Raw pointer comparison not properly implemented yet");
                  } else {
                    r := R.BinaryOp("==", left, right, DAST.Format.BinaryOpFormat.NoFormat());
                  }
                } else {
                  if rExpr.SeqValue? && |rExpr.elements| == 0 {
                    r := R.BinaryOp("==", left.Sel("to_array").Apply0().Sel("len").Apply0(), R.LiteralInt("0"), DAST.Format.BinaryOpFormat.NoFormat());
                  } else if lExpr.SeqValue? && |lExpr.elements| == 0 {
                    r := R.BinaryOp("==", R.LiteralInt("0"), right.Sel("to_array").Apply0().Sel("len").Apply0(), DAST.Format.BinaryOpFormat.NoFormat());
                  } else {
                    r := R.BinaryOp("==", left, right, DAST.Format.BinaryOpFormat.NoFormat());
                  }
                }
              }
              case EuclidianDiv() => {
                r := R.dafny_runtime.AsExpr().FSel("euclidian_division").Apply([left, right]);
              }
              case EuclidianMod() => {
                r := R.dafny_runtime.AsExpr().FSel("euclidian_modulo").Apply([left, right]);
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
              r := R.ExprFromType(rhsType).Apply1(recursiveGen);
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
        Success(R.dafny_runtime.MSel("upcast_id").AsExpr().ApplyType([fromTpe]).Apply0())
      else if fromTpe.IsObjectOrPointer() && toTpe.IsObjectOrPointer() then
        if !toTpe.ObjectOrPointerUnderlying().DynType? then Failure((fromType, fromTpe, toType, toTpe, typeParams)) else
        var fromTpeUnderlying := fromTpe.ObjectOrPointerUnderlying();
        var toTpeUnderlying := toTpe.ObjectOrPointerUnderlying();
        Success(R.dafny_runtime.MSel(upcast).AsExpr().ApplyType([fromTpeUnderlying, toTpeUnderlying]).Apply0())
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
        r := Error("<i>Coercion from " + fromTpeGen.ToString(IND) + " to " + toTpeGen.ToString(IND) + "</i> not yet implemented", recursiveGen);
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
            r := R.RcNew(R.dafny_runtime.MSel("BigRational").AsExpr().FSel("from_integer").Apply1(recursiveGen));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Real), Primitive(Int)) => {
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipBorrowed);
            r := R.dafny_runtime.AsExpr().FSel("dafny_rational_to_int").Apply1(recursiveGen);
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Passthrough(_)) => {
            var rhsType := GenType(toTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.TraitCast(rhsType, R.dafny_runtime.MSel("NumCast").AsType()).FSel("from").Apply1(recursiveGen).Sel("unwrap").Apply0();
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Passthrough(_), Primitive(Int)) => {
            var rhsType := GenType(fromTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            r := R.dafny_runtime.MSel("DafnyInt").AsExpr().FSel("new")
            .Apply1(R.std.MSel("rc").MSel("Rc").AsExpr().FSel("new")
                    .Apply1(R.dafny_runtime.MSel("BigInt").AsExpr().FSel("from").Apply1(recursiveGen)));
            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
          }
          case (Primitive(Int), Primitive(Char)) => {
            var rhsType := GenType(toTpe, GenTypeContext.default());
            var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
            var uType := if charType.UTF32? then R.U32 else R.U16;
            r := R.TraitCast(uType, R.dafny_runtime.MSel("NumCast").AsType());
            r := r.FSel("from").Apply1(
              recursiveGen
            ).Sel("unwrap").Apply0();
            if charType.UTF32? {
              r := R.Identifier("char").FSel("from_u32").Apply1(r.Sel("unwrap").Apply0());
            }
            r := R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(r);
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

            r := R.TypeAscription(recursiveGen, toTpeGen);

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
        r := r.Sel("read").Apply0();
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
            r := R.TraitCast(typExpr, R.DefaultTrait).FSel("default").Apply0();
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
            r := Error("Unsupported: Creation of arrays of more than 16 dimensions");
            readIdents := {};
          } else {
            r := InitEmptyExpr();
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
              r := Error("Finalize New Array with a pointer or object type to something that is not an array or a multi array: " + tpe.ToString(IND));
            }
          } else {
            r := Error("Finalize New Array with a type that is not a pointer or an object: " + tpe.ToString(IND));
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
              var allReadCloned := InitEmptyExpr();
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned.Then(
                  R.DeclareVar(R.CONST, next, None, Some(R.Identifier(next).Clone()))
                );
                recIdents := recIdents - {next};
              }
              var wasAssigned := R.dafny_runtime.MSel("LazyFieldWrapper").AsExpr().Apply1(
                R.dafny_runtime.MSel("Lazy").AsExpr().FSel("new").Apply1(
                  R.std.MSel("boxed").MSel("Box").AsExpr().FSel("new").Apply1(
                    allReadCloned.Then(
                      R.Lambda([], None, recursiveGen)
                    ))));
              assignments := assignments + [R.AssignIdentifier(escapeVar(name), wasAssigned)];
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
          // seq(length, elemFromIndex)
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var lengthGen, _, lengthIdents := GenExpr(length, selfIdent, env, OwnershipOwned);
          /* We will generate this
             {
              let _initializer = Some(elemFromIndex);
              integer_range(Zero::zero(), length).map(
                move |i| => _initializer(&i)
              ).collect::<Sequence<_>>()
             }
           */
          r := R.DeclareVar(R.CONST, "_initializer", None, Some(recursiveGen));
          var range := R.dafny_runtime.MSel("integer_range").AsExpr();
          range := range.Apply([
                                 R.dafny_runtime.MSel("Zero").AsExpr().FSel("zero").Apply0(),
                                 lengthGen
                               ]);
          range := range.Sel("map");
          var rangeMap := R.Lambda([R.Formal.ImplicitlyTyped("i")], None, R.Identifier("_initializer").Apply1(R.Borrow(R.Identifier("i"))));
          range := range.Apply1(
            rangeMap
          );
          range := range.Sel("collect").ApplyType([
                                                    R.dafny_runtime.MSel("Sequence").AsType().Apply([R.TIdentifier("_")])
                                                  ]).Apply0();
          r := R.Block(r.Then(range));

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
          r := recursiveGen.Sel("as_dafny_multiset").Apply0();
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
              r := Error("this outside of a method");
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

          r := recursiveGen.Sel("cardinality").Apply0();
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
            r := Error("Array length of something not an array but " + arrayType.ToString(IND));
          } else {
            var underlying := arrayType.ObjectOrPointerUnderlying();
            if dim == 0 && underlying.Array? {
              r := read_macro.Apply1(recursiveGen).Sel("len").Apply0();
            } else {
              if dim == 0 {
                r := read_macro.Apply1(recursiveGen).Sel("data").Sel("len").Apply0();
              } else {
                r := read_macro.Apply1(recursiveGen).Sel("length" + Strings.OfNat(dim) + "_usize").Apply0();
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
          r := recursiveGen.Sel("keys").Apply0();
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapValues(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := recursiveGen.Sel("values").Apply0();
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case MapItems(expr) => {
          var recursiveGen, _, recIdents := GenExpr(expr, selfIdent, env, OwnershipAutoBorrowed);
          readIdents := recIdents;
          r := recursiveGen.Sel("items").Apply0();
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        case SelectFn(on, field, isDatatype, isStatic, isConstant, arguments) => {
          // Transforms a function member into a lambda
          var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
          var onString := onExpr.ToString(IND);

          var lEnv := env;
          var args := [];
          var parameters := [];
          for i := 0 to |arguments| {
            var ty := GenType(arguments[i], GenTypeContext.default());
            var bTy := R.Borrowed(ty);
            var name := "x" + Strings.OfInt(i);
            lEnv := lEnv.AddAssigned(name, bTy);
            parameters := parameters + [R.Formal(name, bTy)];
            args := args + [(name, ty)];
          }
          var body :=
            if isStatic then
              onExpr.FSel(escapeVar(field))
            else
              R.Identifier("callTarget").Sel(escapeVar(field));
          if isConstant {
            body := body.Apply0();
          }
          var onExprArgs := [];
          for i := 0 to |args| {
            var (name, ty) := args[i];
            var rIdent, _, _ := GenIdent(name, selfIdent, lEnv, if ty.CanReadWithoutClone() then OwnershipOwned else OwnershipBorrowed);
            onExprArgs := onExprArgs + [rIdent];
          }
          body := body.Apply(onExprArgs);
          r := R.Lambda(parameters, None, body);
          if isStatic {
            // Generates |x0: &tp0, ...xn: &tpn| on::field(x0, .... xn) (possibly with some .clone())
          } else {
            // Generates
            // {
            //   let callTarget = (on); //or (on.clone()) if it was owned.
            //   move |x0, ...xn| callTarget.field(x0, .... xn) (possibly with some .clone())
            // }
            var target := if onOwned == OwnershipOwned then onExpr else onExpr.Clone();
            r := R.Block(
              R.DeclareVar(R.CONST, "callTarget", None, Some(target)).Then(
                r));
          }

          // as dyn ::std::ops::Fn(&_, ... &_) -> _
          var typeShapeArgs := [];
          for i := 0 to |arguments| {
            typeShapeArgs := typeShapeArgs + [R.Borrowed(R.TIdentifier("_"))];
          }

          var typeShape := R.DynType(R.FnType(typeShapeArgs, R.TIdentifier("_")));

          r := R.TypeAscription(
            R.std_rc_Rc_new.Apply1(r),
            R.std_rc_Rc.AsType().Apply([typeShape]));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Select(on, field, fieldMutability, isDatatype, fieldType) => {
          if on.Companion? || on.ExternCompanion? {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);

            // onExpr::field()
            r := onExpr.FSel(escapeVar(field)).Apply0();

            r, resultingOwnership := FromOwned(r, expectedOwnership);
            readIdents := recIdents;
            return;
          } else if isDatatype {
            var onExpr, onOwned, recIdents := GenExpr(on, selfIdent, env, OwnershipAutoBorrowed);
            // onExpr.field()
            r := onExpr.Sel(escapeVar(field)).Apply0();
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
              r := read_macro.Apply1(r);
            }
            r := r.Sel(escapeVar(field));
            match fieldMutability {
              case ConstantField() =>
                r := r.Apply0();
                r := r.Clone();
              case InternalClassConstantField() =>
                r := r.Clone();
              case ClassMutableField() =>
                r := read_mutable_field_macro.Apply1(r); // Already contains a clone.
            }
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
                onExpr := read_macro.Apply1(onExpr);
                readIdents := readIdents + recIdents;
              } else {
                onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
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
                          onExpr := read_macro.Apply1(onExpr);
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
          var allReadCloned := InitEmptyExpr();
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
          r := InitEmptyExpr();

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
          var variantExprPath := GenPathExpr(dType + [Ident.Ident(variant)]);
          r := R.Identifier("matches!").Apply(
            [ exprGen.Sel("as_ref").Apply0(),
              R.UnaryOp("{ .. }", variantExprPath, Format.UnaryOpFormat.NoFormat)]);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case Is(expr, fromType, toType) => {
          var expr, recOwned, recIdents := GenExpr(expr, selfIdent, env, OwnershipOwned);
          var fromType := GenType(fromType, GenTypeContext.default());
          var toType := GenType(toType, GenTypeContext.default());
          if fromType.IsObjectOrPointer() && toType.IsObjectOrPointer() {
            r := expr.Sel("is_instance_of").ApplyType([toType.ObjectOrPointerUnderlying()]).Apply0();
          } else {
            r := Error("Source and/or target types of type test is/are not Object or Ptr");
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
          r := exprGen.Sel("iter").Apply0();
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case SeqBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("iter").Apply0();
          if !includeDuplicates {
            r := R.dafny_runtime.MSel("itertools").MSel("Itertools").AsExpr().FSel("unique").Apply1(r);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MultisetBoundedPool(of, includeDuplicates) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("iter").Apply0();
          if !includeDuplicates {
            r := R.dafny_runtime.MSel("itertools").MSel("Itertools").AsExpr().FSel("unique").Apply1(r);
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := recIdents;
          return;
        }
        case MapBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipBorrowed);
          r := exprGen.Sel("keys").Apply0().Sel("iter").Apply0();
          readIdents := recIdents;
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case ExactBoundedPool(of) => {
          var exprGen, _, recIdents := GenExpr(of, selfIdent, env, OwnershipOwned);
          r := R.std.MSel("iter").AsExpr().FSel("once").Apply1(exprGen);
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
          r := R.dafny_runtime.MSel("MapBuilder").AsExpr().ApplyType([kType, vType]).FSel("new").Apply0();
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          readIdents := {};
          return;
        }
        case SetBuilder(elemType) => {
          var eType := GenType(elemType, GenTypeContext.default());
          readIdents := {};
          r := R.dafny_runtime.MSel("SetBuilder").AsExpr().ApplyType([eType]).FSel("new").Apply0();
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
          if collection.IntRange?
             || collection.UnboundedIntRange?
             || collection.SeqBoundedPool?
             || collection.ExactBoundedPool?
             || collection.MultisetBoundedPool? {
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
            r := collectionGen.Sel(fn).Apply1(lambdaGen.Sel("as_ref").Apply0());
            readIdents := recIdents + recLambdaIdents;
          } else {
            r := Error("Quantifier without an inline lambda");
            readIdents := {};
          }
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
      }
    }

    function InitEmptyExpr(): R.Expr {
      R.RawExpr("")
    }

    method Error(message: string, defaultExpr: R.Expr := InitEmptyExpr()) returns (r: R.Expr)
      modifies this
    {
      if error.None? {
        error := Some(message);
      }
      r := R.UnaryOp("/*" + message + "*/", defaultExpr, Format.UnaryOpFormat.NoFormat);
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
        if rootType.RootCrate? {
          var externMod := R.ExternMod(externalMod);
          s := s + externMod.ToString("") + "\n";
        }
        externUseDecls := externUseDecls + [
          R.UseDecl(R.Use(R.PUB, R.crate.MSel(externalMod).MSel("*")))
        ];
      }

      if externUseDecls != [] {
        s := s + R.Mod(DAFNY_EXTERN_MODULE, [], externUseDecls).ToString("") + "\n";
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

    method EmitCallToMain(companion: Expression, mainMethodName: string, hasArgs: bool) returns (s: string)
      modifies this
    {
      s := "\nfn main() {";
      if hasArgs {
        s := s + @"
  let args: Vec<String> = ::std::env::args().collect();
  let dafny_args =
    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(
    &args, |s| 
  ::dafny_runtime::dafny_runtime_conversions::" + conversions + @"::string_to_dafny_string(s));
  ";
      }
      var call, _, _ := GenExpr(companion, NoSelf, Environment.Empty(), OwnershipOwned);
      call := call.FSel(mainMethodName);
      if hasArgs {
        call := call.Apply1(R.Borrow(R.Identifier("dafny_args")));
      } else {
        call := call.Apply([]);
      }
      s := s + call.ToString("") + ";\n}";
    }
  }
}