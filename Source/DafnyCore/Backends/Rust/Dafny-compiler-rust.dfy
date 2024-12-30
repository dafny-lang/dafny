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
          GatheringModule.Wrap(ContainingPathToRust(containingPath), R.Mod(mod.docString, attributes, modName, body)),
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
            generated := GenNewtype(n, containingPath + [Ident.Ident(n.name)]);
          case SynonymType(s) =>
            generated := GenSynonymType(s);
          case Datatype(d) =>
            generated := GenDatatype(d, containingPath + [Ident.Ident(d.name)]);
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
        rTypeParams: seq<R.Type>,
        rTypeParamsDecls: seq<R.TypeParamDecl>)
    {
      typeParamsSeq := [];
      rTypeParams := [];
      rTypeParamsDecls := [];
      if |params| > 0 {
        for tpI := 0 to |params| {
          var tp := params[tpI];
          var typeArg, typeParam := GenTypeParam(tp);
          var rType := GenType(typeArg, GenTypeContext.default());
          typeParamsSeq := typeParamsSeq + [typeArg];
          rTypeParams := rTypeParams + [rType];
          rTypeParamsDecls := rTypeParamsDecls + [typeParam];
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

    method GenField(field: Field) returns (
        rfield: R.Field, fieldInit: R.AssignIdentifier, usedTypeParams: set<string>)
      modifies this
    {
      usedTypeParams := {};
      var fieldType := GenType(field.formal.typ, GenTypeContext.default());
      if !field.isConstant {
        fieldType := R.dafny_runtime.MSel("Field").AsType().Apply([fieldType]);
      }
      usedTypeParams := GatherTypeParamNames(usedTypeParams, fieldType);
      var fieldRustName := escapeVar(field.formal.name);
      rfield := R.Field(R.PUB, R.Formal(fieldRustName, fieldType));

      match field.defaultValue {
        case Some(e) => {
          // TODO(mikael): Fields must be initialized before the code of the constructor if possible
          var expr, _, _ := GenExpr(e, NoSelf, Environment.Empty(), OwnershipOwned);

          fieldInit := R.AssignIdentifier(
            fieldRustName, expr);
        }
        case None => {
          // TODO(mikael) Use type descriptors for default values if generics
          var default := R.std_default_Default_default;
          if fieldType.IsObjectOrPointer() {
            default := fieldType.ToNullExpr();
          }
          fieldInit := R.AssignIdentifier(
            fieldRustName, default);
        }
      }
    }

    method GetName(attributes: seq<Attribute>, name: Name, kind: string) returns (rName: string, extern: ExternAttribute)
      modifies this
    {
      extern := ExtractExtern(attributes, name);

      if extern.SimpleExtern? {
        rName := extern.overrideName;
      } else {
        rName := escapeName(name);
        if extern.AdvancedExtern? {
          error := Some("Multi-argument externs not supported for "+kind+" yet");
        }
      }
    }

    method GenTraitImplementations(
      path: seq<Ident>,
      rTypeParams: seq<R.Type>,
      rTypeParamsDecls: seq<R.TypeParamDecl>,
      superTraitTypes: seq<Type>,
      traitBodies: map<seq<Ident>, seq<R.ImplMember>>,
      extern: ExternAttribute,
      kind: string)
      returns (s: seq<R.ModDecl>)
      modifies this
    {
      s := [];
      var genPath := GenPath(path);
      var genSelfPath := genPath.AsType();
      var genPathExpr := genPath.AsExpr();
      for i := 0 to |superTraitTypes| {
        var superTraitType := superTraitTypes[i];
        match superTraitType {
          case UserDefined(ResolvedType(traitPath, typeArgs, Trait(traitType), _, properMethods, _)) => {
            var pathStr := GenPathType(traitPath);
            var typeArgs := GenTypeArgs(typeArgs, GenTypeContext.default());
            var body: seq<R.ImplMember> := [];
            if traitPath in traitBodies {
              body := traitBodies[traitPath];
            }

            var fullTraitPath := R.TypeApp(pathStr, typeArgs);
            if !extern.NoExtern? { // An extern of some kind
              // Either the Dafny code implements all the methods of the trait or none,
              if |body| == 0 && |properMethods| != 0 {
                continue; // We assume everything is implemented externally
              }
              if |body| != |properMethods| {
                error := Some("Error: In the "+kind+" " + R.SeqToString(path, (s: Ident) => s.id.dafny_name, ".") + ", some proper methods of " +
                              fullTraitPath.ToString("") + " are marked {:extern} and some are not." +
                              " For the Rust compiler, please make all methods (" + R.SeqToString(properMethods, (s: Name) => s.dafny_name, ", ") +
                              ")  bodiless and mark as {:extern} and implement them in a Rust file, "+
                              "or mark none of them as {:extern} and implement them in Dafny. " +
                              "Alternatively, you can insert an intermediate trait that performs the partial implementation if feasible.");
              }
            }
            if |body| == 0 {
              // Extern type, we assume
            }
            if traitType.GeneralTrait? {
              // One more method: Cloning when boxed
              /*impl Test for Wrapper {
                  fn _clone(&self) -> Box<dyn Test> {
                      Box::new(self.clone())
                  }
              }*/
              body := body + [
                R.FnDecl(
                  R.NoDoc, R.NoAttr,
                  R.PRIV,
                  R.Fn(
                    "_clone", [], [R.Formal.selfBorrowed], Some(R.Box(R.DynType(fullTraitPath))),
                    Some(R.BoxNew(R.self.Sel("clone").Apply0()))))
              ];
            } else {
              if kind == "datatype" || kind == "newtype" {
                var dummy := Error("Cannot extend non-general traits");
              }
            }

            var x := R.ImplDecl(
              R.ImplFor(
                rTypeParamsDecls,
                fullTraitPath,
                R.TypeApp(genSelfPath, rTypeParams),
                body
              ));
            s := s + [x];

            var upcastTraitToImplement, upcastTraitFn;
            if traitType.GeneralTrait? {
              upcastTraitToImplement, upcastTraitFn := "UpcastBox", "UpcastStructBoxFn!";
              s := s + [
                R.ImplDecl(
                  R.ImplFor(
                    rTypeParamsDecls,
                    R.dafny_runtime.MSel("UpcastBox").AsType().Apply1(R.DynType(fullTraitPath)),
                    R.TypeApp(genSelfPath, rTypeParams),
                    [ R.FnDecl(
                        R.NoDoc, R.NoAttr,
                        R.PRIV,
                        R.Fn(
                          "upcast",
                          [], [R.Formal.selfBorrowed],
                          Some(R.Box(R.DynType(fullTraitPath))),
                          Some(genPathExpr.ApplyType(rTypeParams).FSel("_clone").Apply1(R.self))) // Difference with UpcastStructBox is that there is no .as_ref()
                      ) ]))
              ];
            } else {
              s := s + [
                R.ImplDecl(
                  R.ImplFor(
                    rTypeParamsDecls,
                    R.dafny_runtime.MSel(Upcast).AsType().Apply([
                                                                  R.DynType(fullTraitPath)]),
                    R.TypeApp(genSelfPath, rTypeParams),
                    [
                      R.ImplMemberMacro(
                        R.dafny_runtime
                        .MSel(UpcastFnMacro).AsExpr()
                        .Apply1(R.ExprFromType(R.DynType(fullTraitPath))))
                    ]
                  )
                )
              ];
            }

          }
          case _ => {}
        }
      }
    }

    method GenClass(c: Class, path: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParamDecl.ToStringMultiple(rTypeParamsDecls, R.IND + R.IND);

      var fields: seq<R.Field> := [];
      var fieldInits: seq<R.AssignIdentifier> := [];
      var usedTypeParams: set<string> := {};
      for fieldI := 0 to |c.fields| {
        var field := c.fields[fieldI];
        var rfield, fieldInit, fieldUsedTypeParams := GenField(field);
        fields := fields + [rfield];
        fieldInits := fieldInits + [fieldInit];
        usedTypeParams := usedTypeParams + fieldUsedTypeParams;
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

      var className, extern := GetName(c.attributes, c.name, "classes");

      var struct := R.Struct(c.docString, [], className, rTypeParamsDecls, R.NamedFields(fields));
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
            "Allocates an UNINITIALIZED instance. Only the Dafny compiler should use that.", R.NoAttr,
            R.PUB,
            R.Fn(
              allocate_fn,
              [], [], Some(Object(R.SelfOwned)),
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
                  m.docString,
                  [R.RawAttribute("#[test]")], R.PUB,
                  R.Fn(
                    fnName, [], [], None,
                    Some(R.Identifier("_default").FSel(fnName).Apply([])))
                ))
            ];
          }
        }
        s := s + testMethods;
      }
      var genSelfPath := GenPathType(path);
      if className != "_default" {
        s := s + [
          R.ImplDecl(
            R.ImplFor(
              rTypeParamsDecls,
              R.dafny_runtime.MSel(Upcast).AsType().Apply([R.DynType(R.AnyTrait)]),
              R.TypeApp(genSelfPath, rTypeParams),
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
      var superTraitTypes := if className == "_default" then [] else c.superTraitTypes;
      var superTraitImplementations := GenTraitImplementations(
        path,
        rTypeParams,
        rTypeParamsDecls,
        superTraitTypes,
        traitBodies,
        extern,
        "class");
      s := s + superTraitImplementations;
    }

    method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq := [];
      var rTypeParamsDecls: seq<R.TypeParamDecl> := [];
      var typeParams: seq<R.Type> := [];
      if |t.typeParams| > 0 {
        for tpI := 0 to |t.typeParams| {
          var tp := t.typeParams[tpI];
          var typeArg, typeParamDecl := GenTypeParam(tp);
          typeParamsSeq := typeParamsSeq + [typeArg];
          rTypeParamsDecls := rTypeParamsDecls + [typeParamDecl];
          var typeParam := GenType(typeArg, GenTypeContext.default());
          typeParams := typeParams + [typeParam];
        }
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var name := escapeName(t.name);
      var traitFulltype := R.TIdentifier(name).Apply(typeParams);
      var traitFullExpr := R.Identifier(name).ApplyType(typeParams);
      var implBody, _ := GenClassImplBody(
        t.body, true,
        UserDefined(
          ResolvedType(
            fullPath, [],
            ResolvedTypeBase.Trait(t.traitType), t.attributes,
            [], [])),
        typeParamsSeq);
      if t.traitType.GeneralTrait? { // Cloning is boxed
        // fn _clone(&self) -> Box<dyn Test>;
        implBody := implBody + [
          R.FnDecl(
            R.NoDoc, R.NoAttr,
            R.PRIV,
            R.Fn(
              "_clone", [], [R.Formal.selfBorrowed], Some(R.Box(R.DynType(traitFulltype))),
              None
            ))
        ];
      }
      var parents := [];
      var upcastImplemented := [];
      for i := 0 to |t.parents| {
        var parentTyp := t.parents[i];
        var parentTpe := GenType(parentTyp, GenTypeContext.ForTraitParents());
        parents := parents + [parentTpe];
        var upcastTrait := if parentTyp.IsGeneralTrait() then "UpcastBox" else Upcast;
        parents := parents + [R.dafny_runtime.MSel(upcastTrait).AsType().Apply1(R.DynType(parentTpe))];
        if parentTyp.IsGeneralTrait() {
          /*impl UpcastBox<dyn GeneralTraitSuper> for Box<dyn GeneralTrait> {
              fn upcast(&self) -> ::std::boxed::Box<dyn GeneralTraitSuper> {
                GeneralTrait::<GeneralTraitSuper>::_clone(self.as_ref())
              }
            }*/
          upcastImplemented := upcastImplemented + [
            R.ImplDecl(
              R.ImplFor(
                rTypeParamsDecls,
                R.dafny_runtime.MSel("UpcastBox").AsType().Apply1(R.DynType(parentTpe)),
                R.Box(R.DynType(traitFulltype)),
                [ R.FnDecl(
                    R.NoDoc, R.NoAttr,
                    R.PRIV,
                    R.Fn(
                      "upcast",
                      [], [R.Formal.selfBorrowed],
                      Some(R.Box(R.DynType(parentTpe))),
                      Some(traitFullExpr.FSel("_clone").Apply1(R.self.FSel("as_ref").Apply0()))
                    )
                  )]))
          ];
        }
      }
      s := [
        R.TraitDecl(
          R.Trait(
            t.docString, [],
            rTypeParamsDecls, traitFulltype,
            parents,
            implBody
          ))];
      if t.traitType.GeneralTrait? {
        /*impl Clone for Box<dyn Test> {
            fn clone(&self) -> Box<dyn Test> {
              Test::_clone(self.as_ref())
            }
          }*/
        s := s + [
          R.ImplDecl(
            R.ImplFor(
              rTypeParamsDecls,
              R.std.MSel("clone").MSel("Clone").AsType(),
              R.Box(R.DynType(traitFulltype)),
              [R.FnDecl(
                 R.NoDoc, R.NoAttr,
                 R.PRIV,
                 R.Fn("clone", [],
                      [ R.Formal.selfBorrowed ],
                      Some(R.SelfOwned),
                      Some(traitFullExpr.FSel("_clone").Apply1(R.self.Sel("as_ref").Apply0()))
                 ))]))];
      }
      s := s + upcastImplemented;
    }

    method GenNewtype(c: Newtype, path: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls := GenTypeParameters(c.typeParams);
      var constrainedTypeParams := R.TypeParamDecl.ToStringMultiple(rTypeParamsDecls, R.IND + R.IND);

      var wrappedType;
      var rustType := NewtypeRangeToUnwrappedBoundedRustType(c.base, c.range);
      if rustType.Some? {
        wrappedType := rustType.value;
      } else {
        wrappedType := GenType(c.base, GenTypeContext.default());
      }
      var newtypeType: Type :=
        UserDefined(
          ResolvedType(
            path, typeParamsSeq,
            ResolvedTypeBase.Newtype(c.base, c.range, false),
            c.attributes, [], []));
      var newtypeName := escapeName(c.name);
      var resultingType := R.TypeApp(R.TIdentifier(newtypeName), rTypeParams);
      var attributes: string;
      if IsNewtypeCopy(c.range) {
        attributes := "#[derive(Clone, PartialEq, Copy)]";
      } else {
        attributes := "#[derive(Clone, PartialEq)]";
      }
      s := [
        R.StructDecl(
          R.Struct(
            c.docString,
            [
              R.RawAttribute(attributes),
              R.RawAttribute("#[repr(transparent)]")
            ],
            newtypeName,
            rTypeParamsDecls,
            R.NamelessFields([R.NamelessField(R.PUB, wrappedType)])
          ))];

      var fnBody;

      match c.witnessExpr {
        case Some(e) => {
          var e := Convert(e, c.base, newtypeType);
          // TODO(Mikael): generate statements if any
          var r, _, _ := GenExpr(e, NoSelf, Environment.Empty(), OwnershipOwned);
          fnBody := r;
        }
        case None => {
          fnBody := R.Identifier(newtypeName).Apply1(R.std_default_Default_default);
        }
      }

      var body :=
        R.FnDecl(
          "An element of " + newtypeName, [],
          R.PRIV,
          R.Fn(
            "default", [], [], Some(R.SelfOwned),
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
                resultingType,
                [
                  R.FnDecl(
                    "Constraint check", R.NoAttr,
                    R.PUB,
                    R.Fn(
                      "is", [], rFormals, Some(R.Bool()),
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
            resultingType,
            [body]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.DafnyPrint,
            resultingType,
            [R.FnDecl(
               "For Dafny print statements", R.NoAttr,
               R.PRIV,
               R.Fn("fmt_print", [],
                    [ R.Formal.selfBorrowed,
                      R.Formal("_formatter", R.BorrowedMut(R.std.MSel("fmt").MSel("Formatter").AsType())),
                      R.Formal("in_seq", R.Type.Bool)],
                    Some(R.std.MSel("fmt").MSel("Result").AsType()),
                    Some(R.dafny_runtime.MSel("DafnyPrint").AsExpr().FSel("fmt_print").Apply(
                           [ R.Borrow(R.self.Sel("0")),
                             R.Identifier("_formatter"),
                             R.Identifier("in_seq")])))
             )]))];
      s := s + [
        R.ImplDecl(
          R.ImplFor(
            rTypeParamsDecls,
            R.std.MSel("ops").MSel("Deref").AsType(),
            resultingType,
            [R.TypeDeclMember("Target", wrappedType),
             R.FnDecl(
               R.NoDoc, R.NoAttr,
               R.PRIV,
               R.Fn("deref", [],
                    [R.Formal.selfBorrowed], Some(R.Borrowed(R.Self().MSel("Target").AsType())),
                    Some(R.Borrow(R.self.Sel("0")))))]))];

      // Convert a ref to the underlying type to a ref of the wrapped newtype
      s := s + [
        R.ImplDecl(
          R.Impl(
            rTypeParamsDecls,
            resultingType,
            [R.FnDecl(
               "SAFETY: The newtype is marked as transparent", R.NoAttr,
               R.PUB,
               R.Fn(
                 "_from_ref", [],
                 [R.Formal("o", R.Borrowed(wrappedType))],
                 Some(R.Borrowed(R.Self().AsType())),
                 Some(
                   R.Unsafe(
                     R.Block(
                       //"The newtype is marked as transparent",
                       R.std.MSel("mem").MSel("transmute").AsExpr().Apply1(R.Identifier("o")))))))]))];
      var rTypeParamsDeclsWithHash := R.TypeParamDecl.AddConstraintsMultiple(
        rTypeParamsDecls, [R.Hash]
      );
      s := s + [
        HashImpl(
          rTypeParamsDeclsWithHash,
          resultingType,
          R.Identifier("self").Sel("0").Sel("hash").Apply1(R.Identifier("_state"))
        )];
      if c.range.HasArithmeticOperations() {
        s := s + [
          OpsImpl('+', rTypeParamsDecls, resultingType, newtypeName),
          OpsImpl('-', rTypeParamsDecls, resultingType, newtypeName),
          OpsImpl('*', rTypeParamsDecls, resultingType, newtypeName),
          OpsImpl('/', rTypeParamsDecls, resultingType, newtypeName),
          PartialOrdImpl(rTypeParamsDecls, resultingType, newtypeName)
        ];
      }
      if c.range.Bool? {
        s := s + [
          UnaryOpsImpl('!', rTypeParamsDecls, resultingType, newtypeName)
        ];
      }
      var implementation, traitBodies := GenClassImplBody(c.classItems, false, newtypeType, typeParamsSeq);
      if |traitBodies| > 0 {
        error := Some("No support for trait in newtypes yet");
      }
      if |implementation| > 0 {
        s := s + [
          R.ImplDecl(
            R.Impl(
              rTypeParamsDecls,
              R.TypeApp(R.TIdentifier(newtypeName), rTypeParams),
              implementation
            )
          )];
      }
    }

    method GenSynonymType(c: SynonymType) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls := GenTypeParameters(c.typeParams);
      var synonymTypeName := escapeName(c.name);
      var resultingType := GenType(c.base, GenTypeContext.default());

      s := [
        R.TypeDecl(
          R.TypeSynonym(
            c.docString,
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
                "An element of " + synonymTypeName,
                [], R.PUB,
                R.Fn(
                  constantName, defaultConstrainedTypeParams, [], Some(resultingType),
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

    method GenDatatype(c: Datatype, path: seq<Ident>) returns (s: seq<R.ModDecl>)
      modifies this
    {
      var typeParamsSeq, rTypeParams, rTypeParamsDecls := GenTypeParameters(c.typeParams);
      var datatypeName, extern := GetName(c.attributes, c.name, "datatypes");
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
        ctors := ctors + [R.EnumCase(ctor.docString, escapeName(ctor.name), namedFields)];
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
                if |c.ctors| == 1 then
                  "Returns a borrow of the field " + callName
                else
                  "Gets the field " + callName + " for all enum members which have it",
                [],
                R.PUB,
                R.Fn(
                  callName,
                  [], [R.Formal.selfBorrowed], Some(R.Borrowed(formalType)),
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
              "",
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
             c.docString,
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
              []
            )
          )];
      }

      // Implementation of Hash trait
      s := s + [
        HashImpl(
          rTypeParamsDeclsWithHash,
          R.TypeApp(R.TIdentifier(datatypeName), rTypeParams),
          hashImplBody)];

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
        var fullType := R.TypeApp(R.TIdentifier(datatypeName), rTypeParams);

        // Implementation of Default trait when c supports equality
        if cIsEq {
          s := s +
          [ DefaultDatatypeImpl(
              rTypeParamsDecls,
              fullType,
              structName,
              structAssignments)];
        }

        // Implementation of AsRef trait
        s := s + [
          AsRefDatatypeImpl(
            rTypeParamsDecls,
            fullType
          )];
      }
      var superTraitImplementations := GenTraitImplementations(
        path,
        rTypeParams,
        rTypeParamsDecls,
        c.superTraitTypes,
        traitBodies,
        extern,
        "datatype");
      s := s + superTraitImplementations;
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
          s := if |typeArgs| > 0 then R.TypeApp(t, typeArgs) else t;

          match resolved.kind {
            case Class() => {
              s := Object(s);
            }
            case Datatype(_) => {
              if IsRcWrapped(resolved.attributes) {
                s := R.Rc(s);
              }
            }
            case Trait(GeneralTrait()) => {
              if !genTypeContext.forTraitParents {
                s := R.Box(R.DynType(s));
              }
            }
            case Trait(ObjectTrait()) => {
              if resolved.path == [Ident.Ident(Name("_System")), Ident.Ident(Name("object"))] {
                s := R.AnyTrait;
              }
              if !genTypeContext.forTraitParents {
                s := Object(R.DynType(s));
              }
            }
            case SynonymType(base) => {
              var underlying := GenType(base, GenTypeContext.default());
              s := R.TSynonym(s, underlying);
            }
            case Newtype(base, range, erased) => {
              if erased {
                var unwrappedType := NewtypeRangeToUnwrappedBoundedRustType(base, range);
                if unwrappedType.Some? {
                  s := unwrappedType.value;
                } else {
                  var unwrappedType := GenType(base, GenTypeContext.default());
                  s := unwrappedType;
                }
              } else if IsNewtypeCopy(range) {
                s := R.TMetaData(s, copySemantics := true, overflow := range.CanOverflow());
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
              } else if enclosingType.UserDefined? && enclosingType.resolved.kind.Newtype?
                        && IsNewtypeCopy(enclosingType.resolved.kind.range) {
                tpe := R.TMetaData(
                  R.SelfOwned,
                  copySemantics := true,
                  overflow := enclosingType.resolved.kind.range.CanOverflow());
              } else { // For raw-defined datatypes, non-copy newtypes
                tpe := R.SelfBorrowed;
              }
            }
          }
          var formal := R.Formal(selfId, tpe);
          params := [formal] + params;
          var name := formal.name;
          paramNames := [name] + paramNames;
          paramTypes := paramTypes[name := formal.tpe];
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
              var isTailRecursive := |m.body| == 1 && m.body[0].TailRecursive?;

              for outI := 0 to |outVars| {
                var outVar := outVars[outI];
                var outTyp := m.outTypes[outI];
                var outType := GenType(outTyp, GenTypeContext.default());
                var outName := escapeVar(outVar);
                if !isTailRecursive {// Out parameters are assigned in the inner block
                  paramNames := paramNames + [outName];
                  var outMaybeType := if outType.CanReadWithoutClone() then outType else R.MaybePlaceboType(outType);
                  paramTypes := paramTypes[outName := outMaybeType];
                }
                tupleArgs := tupleArgs + [outName];
              }
              earlyReturn := Some(tupleArgs);
            }
          }
          case None => {}
        }
        env := Environment(preAssignNames + paramNames, preAssignTypes + paramTypes, {});

        var body, _, _ := GenStmts(m.body, selfIdent, env, true, earlyReturn);

        fBody := Some(preBody.Then(body));
      } else {
        env := Environment(paramNames, paramTypes, {});
        fBody := None;
      }
      s := R.FnDecl(
        m.docString, R.NoAttr,
        visibility,
        R.Fn(
          fnName,
          typeParams,
          params,
          Some(if |retTypeArgs| == 1 then retTypeArgs[0] else R.TupleType(retTypeArgs)),
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
      while i < |stmts| {
        var stmt := stmts[i];
        // Special case "var x: T; x = ...". We need to merge them
        // because normally x can read a variable named x, and with two statements
        // this is not possible.
        if stmt.DeclareVar? && stmt.maybeValue.None? &&
           i + 1 < |stmts| &&
           stmts[i + 1].Assign? &&
           stmts[i + 1].lhs.Ident? &&
           stmts[i + 1].lhs.ident == stmt.name {
          var name := stmt.name;
          var typ := stmt.typ;
          var stmtExpr, recIdents, newEnv2 := GenDeclareVarAssign(name, typ, stmts[i + 1].value, selfIdent, newEnv);
          newEnv := newEnv2;
          readIdents := readIdents + (recIdents - declarations);
          declarations := declarations + {escapeVar(name)};
          generated := generated.Then(stmtExpr);
          i := i + 2;
        } else {
          // Avoid maybe placebo wrapping if not necessary
          match stmt {
            case DeclareVar(name, optType, None) =>
              var laterAssignmentStatus := DetectAssignmentStatus(stmts[i + 1..], name);
              newEnv := newEnv.AddAssignmentStatus(escapeVar(name), laterAssignmentStatus);
            case DeclareVar(name, optType, Some(InitializationValue(typ))) =>
              var tpe := GenType(typ, GenTypeContext.default());
              var varName := escapeVar(name);
              var laterAssignmentStatus := DetectAssignmentStatus(stmts[i + 1..], name);
              newEnv := newEnv.AddAssignmentStatus(varName, laterAssignmentStatus);
            case _ =>
          }
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
          if stmtExpr.Return? { // The rest of statements is unreachable
            break;
          }

          i := i + 1;
        }
      }
    }

    method GenDeclareVarAssign(name: VarName, typ: Type, rhs: Expression, selfIdent: SelfInfo, env: Environment)
      returns (generated: R.Expr, readIdents: set<string>, newEnv: Environment)
      decreases rhs
      modifies this
    {
      var tpe := GenType(typ, GenTypeContext.default());
      var varName := escapeVar(name);
      var exprRhs;
      if rhs.InitializationValue? &&
         tpe.IsObjectOrPointer() {
        readIdents := {};
        tpe := if rhs.NewUninitArray? then tpe.TypeAtInitialization() else tpe;
        exprRhs := tpe.ToNullExpr();
      } else {
        var expr, exprOwnership;
        expr, exprOwnership, readIdents := GenExpr(rhs, selfIdent, env, OwnershipOwned);
        tpe := if rhs.NewUninitArray? then tpe.TypeAtInitialization() else tpe;
        exprRhs := expr;
      }
      generated := R.DeclareVar(R.MUT, varName, Some(tpe), Some(exprRhs));
      newEnv := env.AddAssigned(varName, tpe);
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

    @IsolateAssertions @ResourceLimit("1e6")
    method GenOwnedCallPart(ghost e: Expression, on: Expression, selfIdent: SelfInfo, name: CallName, typeArgs: seq<Type>, args: seq<Expression>, env: Environment) returns (r: R.Expr, readIdents: set<string>)
      requires forall a <- args :: a < e
      requires on < e
      modifies this
      decreases e, 1, 1
    {
      var argExprs, recIdents, typeExprs, fullNameQualifier := GenArgs(e, selfIdent, name, typeArgs, args, env);
      readIdents := recIdents;

      match fullNameQualifier {
        // Trait calls are fully specified as we can't guarantee traits will be in context
        case Some(ResolvedType(path, onTypeArgs, base, _, _, _)) =>
          var fullPath := GenPathExpr(path);
          var onTypeExprs := GenTypeArgs(onTypeArgs, GenTypeContext.default());
          var onExpr, recOwnership, recIdents;
          if (base.Trait? && base.traitType.ObjectTrait?) || base.Class? {
            // First we own a pointer, then we read it
            onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipOwned);
            onExpr := read_macro.Apply1(onExpr);
            readIdents := readIdents + recIdents;
          } else if base.Trait? && base.traitType.GeneralTrait? {
            // General traits borrow their self, from a Box<dyn TraitName>
            // The underlying type is a Box<dyn TraitName>, self: Datatype or Rc<Datatype>
            // 'on' is going to return an owned version of this box.
            onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
            if onExpr.Identifier? && env.NeedsAsRefForBorrow(onExpr.name) {
              onExpr := onExpr.Sel("as_ref").Apply0();
            } else if onExpr.IsBorrow() {
              // If the resulting expression is a borrow, e.g. &something(), it means the trait was owned.
              // In our case we want dynamic dispatch, so we need to get the bare reference.
              // Because "on" is a general trait, we need to call as_ref() instead to get the bare expression
              // If the onExpr is an identifier but not "self", we apply the same treatment
              onExpr := R.std.MSel("convert").MSel("AsRef").AsExpr().FSel("as_ref").Apply1(onExpr);
            }
            readIdents := readIdents + recIdents;
          } else if base.Newtype? && IsNewtypeCopy(base.range) {
            // The self type of a newtype that is copy is also copy
            onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipOwned);
            readIdents := readIdents + recIdents;
          } else {
            // The self type of any other type is borrowed
            onExpr, recOwnership, recIdents := GenExpr(on, selfIdent, env, OwnershipBorrowed);
            readIdents := readIdents + recIdents;
          }
          r := fullPath.ApplyType(onTypeExprs).FSel(escapeName(name.name)).ApplyType(typeExprs).Apply([onExpr] + argExprs);
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
                    if typ.IsObjectOrPointer() && onExpr != R.Identifier("self") {
                      onExpr := read_macro.Apply1(onExpr);
                    }
                  case _ =>
                }
              }
              onExpr := onExpr.Sel(renderedName);
            }
          }
          r := onExpr.ApplyType(typeExprs).Apply(argExprs);
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
            // We might be able to just let the variable uninitialized.
            if env.IsAssignmentStatusKnown(varName) {
              generated := R.DeclareVar(R.MUT, varName, Some(tpe), None);
            } else {
              generated := R.DeclareVar(R.MUT, varName, None, Some(R.MaybePlaceboPath.AsExpr().ApplyType1(tpe).FSel("new").Apply0()));
              tpe := R.MaybePlaceboType(tpe);
            }
            readIdents := {};
            newEnv := env.AddAssigned(varName, tpe);
          } else {
            generated, readIdents, newEnv := GenDeclareVarAssign(name, typ, expression, selfIdent, env);
            return;
          }
        }
        case DeclareVar(name, typ, None) => {
          var varName := escapeVar(name);
          if env.IsAssignmentStatusKnown(varName) {
            var tpe := GenType(typ, GenTypeContext.default());
            generated := R.DeclareVar(R.MUT, varName, Some(tpe), None);
            readIdents := {};
            newEnv := env.AddAssigned(varName, tpe);
          } else {
            var newStmt := DeclareVar(name, typ, Some(InitializationValue(typ)));
            assume {:axiom} newStmt < stmt;
            generated, readIdents, newEnv := GenStmt(newStmt, selfIdent, env, isLast, earlyReturn);
          }
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

          var oldEnv := env;
          if selfIdent != NoSelf {
            var selfClone, _, _ := GenIdent(selfIdent.rSelfName, selfIdent, Environment.Empty(), OwnershipOwned);
            generated := generated.Then(R.DeclareVar(R.MUT, "_this", None, Some(selfClone)));
            if selfIdent.rSelfName in oldEnv.names {
              oldEnv := oldEnv.RemoveAssigned(selfIdent.rSelfName);
            }
          }
          var loopBegin := R.RawExpr("");
          newEnv := env;
          for paramI := 0 to |oldEnv.names| {
            var param := oldEnv.names[paramI];
            if param == "_accumulator" {
              continue; // This is an already mutable variable handled by SinglePassCodeGenerator
            }
            var paramInit, _, _ := GenIdent(param, selfIdent, oldEnv, OwnershipOwned);
            var recVar := TailRecursionPrefix + Strings.OfNat(paramI);
            generated := generated.Then(R.DeclareVar(R.MUT, recVar, None, Some(paramInit)));
            if param in oldEnv.types {
              // We made the input type owned by the variable.
              // so we can remove borrow annotations.
              var declaredType := oldEnv.types[param].ToOwned();
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
          assume {:axiom} Expression.Call(on, name, typeArgs, args) < stmt;
          generated, readIdents := GenOwnedCallPart(Expression.Call(on, name, typeArgs, args), on, selfIdent, name, typeArgs, args, env);

          newEnv := env;
          if maybeOutVars.Some? && |maybeOutVars.value| == 1 {
            var outVar := escapeVar(maybeOutVars.value[0]);
            if env.IsMaybePlacebo(outVar) {
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
              if env.IsMaybePlacebo(outVar) {
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
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      if expectedOwnership == OwnershipOwned || expectedOwnership == OwnershipAutoBorrowed {
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
      } else if ownership == OwnershipBorrowed || ownership == OwnershipBorrowedMut {
        if expectedOwnership == OwnershipOwned{
          resultingOwnership := OwnershipOwned;
          out := r.Clone();
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
        return;
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

    method ToPrimitive(r: R.Expr, typ: Type, primitiveType: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := r;
      if typ != primitiveType {
        var dummy;
        out, dummy := GenExprConvertTo(r, OwnershipOwned, typ, primitiveType, env, OwnershipOwned);
      }
    }

    method ToBool(r: R.Expr, typ: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := ToPrimitive(r, typ, Primitive(Primitive.Bool), env);
    }

    method ToInt(r: R.Expr, typ: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := ToPrimitive(r, typ, Primitive(Primitive.Int), env);
    }

    method FromPrimitive(r: R.Expr, primitiveType: Type, typ: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := r;
      if typ != primitiveType {
        var dummy;
        out, dummy := GenExprConvertTo(r, OwnershipOwned, primitiveType, typ, env, OwnershipOwned);
      }
    }

    method FromBool(r: R.Expr, typ: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := FromPrimitive(r, Primitive(Primitive.Bool), typ, env);
    }

    method FromInt(r: R.Expr, typ: Type, env: Environment) returns (out: R.Expr)
      modifies this
    {
      out := FromPrimitive(r, Primitive(Primitive.Int), typ, env);
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
      var BinOp(TypedBinOp(op, lType, rType, resType), lExpr, rExpr, format) := e;
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
            if IsBooleanOperator(op) {
              left := ToBool(left, lType, env);
              right := ToBool(right, rType, env);
            }
            r := R.Expr.BinaryOp(
              OpTable[op],
              left,
              right,
              format);
            if IsBooleanOperator(op) {
              r := FromBool(r, resType, env);
            }
          } else {
            if IsComplexArithmetic(op) {
              left := ToInt(left, lType, env);
              right := ToInt(right, rType, env);
            }
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
                    if resType != Primitive(Primitive.Bool) {
                      r, resultingOwnership := GenExprConvertTo(r, OwnershipOwned, Primitive(Primitive.Bool), resType, env, OwnershipOwned);
                    }
                  }
                }
              }
              case Div(true) =>
                r := left.Sel("wrapping_div").Apply1(right);
              case Plus(true) =>
                r := left.Sel("wrapping_add").Apply1(right);
              case Times(true) =>
                r := left.Sel("wrapping_mul").Apply1(right);
              case Minus(true) =>
                r := left.Sel("wrapping_sub").Apply1(right);
              case EuclidianDiv() => {
                r := R.dafny_runtime.MSel("euclidian_division").AsExpr().Apply([left, right]);
              }
              case EuclidianMod() => {
                r := R.dafny_runtime.MSel("euclidian_modulo").AsExpr().Apply([left, right]);
              }
              case Passthrough(op) => {
                r := R.Expr.BinaryOp(op, left, right, format);
              }
            }
            if IsComplexArithmetic(op) {
              r := FromInt(r, resType, env);
            }
          }
        }
      }
      r, resultingOwnership := FromOwned(r, expectedOwnership);
      readIdents := recIdentsL + recIdentsR;
      return;
    }

    // Given an expression that is a newtype, returns the underlying value
    // Preserves ownership
    method UnwrapNewtype(
      expr: R.Expr,
      exprOwnership: Ownership,
      fromTpe: Type
    ) returns (r: R.Expr)
      requires IsNewtype(fromTpe)
    {
      r := expr;
      if !fromTpe.resolved.kind.erase {
        r := r.Sel("0");
        if exprOwnership == OwnershipBorrowed {
          r := R.Borrow(r);
        }
      }
    }

    // Given an expression that is the underlying value of a newtype, returns the newtype
    // Preserves ownership
    method WrapWithNewtype(
      expr: R.Expr,
      exprOwnership: Ownership,
      toTpe: Type
    ) returns (r: R.Expr)
      requires IsNewtype(toTpe)
    {
      r := expr;
      var toKind := toTpe.resolved.kind;
      if !toKind.erase {
        var fullPath := GenPathExpr(toTpe.resolved.path);
        if exprOwnership == OwnershipOwned {
          r := fullPath.Apply1(r);
        } else {
          r := fullPath.FSel("_from_ref").Apply1(r); // Keep borrowbility
        }
      }
    }

    // To use when we know that the expression is a Convert(_, _, toTpe)
    // and toTpe is a newtype
    method GenExprConvertTo(
      expr: R.Expr,
      exprOwnership: Ownership,
      fromTpe: Type,
      toTpe: Type,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership)
      requires exprOwnership != OwnershipAutoBorrowed
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
      decreases fromTpe, toTpe // We unwrap newtypes
    {
      r := expr;
      if fromTpe == toTpe {
        r, resultingOwnership := FromOwnership(r, exprOwnership, expectedOwnership);
        return;
      }
      if fromTpe.UserDefined? && fromTpe.resolved.kind.SynonymType? {
        r, resultingOwnership := GenExprConvertTo(expr, exprOwnership, fromTpe.resolved.kind.baseType, toTpe, env, expectedOwnership);
        return;
      }
      if toTpe.UserDefined? && toTpe.resolved.kind.SynonymType? {
        r, resultingOwnership := GenExprConvertTo(expr, exprOwnership, fromTpe, toTpe.resolved.kind.baseType, env, expectedOwnership);
        return;
      }
      if NeedsUnwrappingConversion(fromTpe) {
        // From type is a newtype but it's not a primitive one.
        r := UnwrapNewtype(r, exprOwnership, fromTpe);
        r, resultingOwnership :=
          GenExprConvertTo(r, exprOwnership, fromTpe.resolved.kind.baseType, toTpe, env, expectedOwnership);
        return;
      }
      if NeedsUnwrappingConversion(toTpe) {
        var toKind := toTpe.resolved.kind;
        r, resultingOwnership :=
          GenExprConvertTo(r, exprOwnership, fromTpe, toKind.baseType, env, expectedOwnership);
        r := WrapWithNewtype(r, resultingOwnership, toTpe);
        r, resultingOwnership := FromOwnership(r, resultingOwnership, expectedOwnership);
        return;
      }
      // At this point, our newtypes are either primitives or we have other types.
      var unwrappedFromType := GetUnwrappedBoundedRustType(fromTpe);
      var unwrappedToType := GetUnwrappedBoundedRustType(toTpe);
      if unwrappedToType.Some? {
        var boundedToType := unwrappedToType.value;
        if unwrappedFromType.Some? {
          r := UnwrapNewtype(r, exprOwnership, fromTpe);
          var inOwnership := exprOwnership;
          if unwrappedFromType.value != unwrappedToType.value {
            var asType := boundedToType;
            if inOwnership == OwnershipBorrowed {
              match r {
                case UnaryOp("&", underlying, _) =>
                  r := underlying;
                case _ => r := r.Clone();
              }
            }
            r := R.TypeAscription(r, asType);
            inOwnership := OwnershipOwned;
          }
          r := WrapWithNewtype(r, OwnershipOwned, toTpe);
          r, resultingOwnership := FromOwnership(r, inOwnership, expectedOwnership);
          return;
        }
        assert !IsNewtype(fromTpe);
        if fromTpe.IsPrimitiveInt() {
          if exprOwnership == OwnershipBorrowed {
            r := r.Clone();
          }
          r := R.dafny_runtime.MSel("truncate!").AsExpr().Apply([r, R.ExprFromType(boundedToType)]);
          r := WrapWithNewtype(r, OwnershipOwned, toTpe);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        if fromTpe == Primitive(Char) {
          r := R.TypeAscription(r.Sel("0"), boundedToType);
          r := WrapWithNewtype(r, OwnershipOwned, toTpe);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        var fromTpeRust := GenType(fromTpe, GenTypeContext.default());
        r := Error("No conversion available from "+fromTpeRust.ToString("")+" to " + boundedToType.ToString(""));
        r, resultingOwnership := FromOwned(r, expectedOwnership);
        return;
      }
      assert !IsNewtype(toTpe);
      if unwrappedFromType.Some? {
        if !fromTpe.resolved.kind.erase {
          r := r.Sel("0");
        }
        // Now r is of type unwrappedFromType.value
        if toTpe == Primitive(Char) {
          r, resultingOwnership := FromOwnership(
            R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(
              R.TypeAscription(r, DafnyCharUnderlying)
            ), exprOwnership, expectedOwnership);
          return;
        }
        if toTpe.IsPrimitiveInt() {
          r, resultingOwnership := FromOwnership(r, exprOwnership, OwnershipOwned);
          r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
        }
        var toTpeRust := GenType(toTpe, GenTypeContext.default());
        r := Error("No conversion available from "+unwrappedFromType.value.ToString("")+" to " + toTpeRust.ToString(""));
        r, resultingOwnership := FromOwned(r, expectedOwnership);
        return;
      }
      assert !IsNewtype(fromTpe);
      match (fromTpe, toTpe) {
        case (Primitive(Int), Primitive(Real)) => {
          r := R.RcNew(R.dafny_runtime.MSel("BigRational").AsExpr().FSel("from_integer").Apply1(r));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case (Primitive(Real), Primitive(Int)) => {
          r := R.dafny_runtime.AsExpr().FSel("dafny_rational_to_int").Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case (Primitive(Int), Primitive(Char)) => {
          var rhsType := GenType(toTpe, GenTypeContext.default());
          var uType := if charType.UTF32? then R.U32 else R.U16;
          if exprOwnership != OwnershipOwned {
            r := r.Clone();
          }
          r := R.TraitCast(uType, R.dafny_runtime.MSel("NumCast").AsType()).FSel("from").Apply1(
            r
          ).Sel("unwrap").Apply0();
          if charType.UTF32? {
            r := R.Identifier("char").FSel("from_u32").Apply1(r).Sel("unwrap").Apply0();
          }
          r := R.dafny_runtime.MSel(DafnyChar).AsExpr().Apply1(r);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case (Primitive(Char), Primitive(Int)) => {
          var rhsType := GenType(fromTpe, GenTypeContext.default());
          r := R.dafny_runtime.MSel("int!").AsExpr().Apply1(r.Sel("0"));
          r, resultingOwnership := FromOwned(r, expectedOwnership);
        }
        case _ => {
          r, resultingOwnership := GenExprConvertOther(expr, exprOwnership, fromTpe, toTpe, env, expectedOwnership);
        }
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
    opaque function SeqResultToResultSeq<T, E>(xs: seq<Result<T, E>>): (result: Result<seq<T>, E>)
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
      else if toTpe.IsBox() then // General trait
        var toTpeUnderlying := toTpe.BoxUnderlying();
        if !toTpeUnderlying.DynType? then Failure((fromType, fromTpe, toType, toTpe, typeParams)) else
        if fromTpe.IsBox() then
          var fromTpeUnderlying := fromTpe.BoxUnderlying();
          if !fromTpeUnderlying.DynType? then Failure((fromType, fromTpe, toType, toTpe, typeParams)) else
          Success(R.dafny_runtime.MSel("upcast_box_box").AsExpr().ApplyType([fromTpeUnderlying, toTpeUnderlying]).Apply0())
        else
          Success(R.dafny_runtime.MSel("upcast_box").AsExpr().ApplyType([fromTpe, toTpeUnderlying]).Apply0())
      else if fromTpe.IsObjectOrPointer() && toTpe.IsObjectOrPointer() then
        var toTpeUnderlying := toTpe.ObjectOrPointerUnderlying();
        if !toTpeUnderlying.DynType? then Failure((fromType, fromTpe, toType, toTpe, typeParams)) else
        var fromTpeUnderlying := fromTpe.ObjectOrPointerUnderlying();
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

    // Assumes expr to be borrowed. Will return and expression that is owned instead
    function BorrowedToOwned(expr: R.Expr, env: Environment): (out: R.Expr) {
      match expr
      case UnaryOp("&", underlying, _) =>
        // We need to clone underlying unless it has borrow semantics.
        if underlying.Identifier? && env.CanReadWithoutClone(underlying.name) then
          underlying
        else
          underlying.Clone() // Auto-borrow allows for implicit code
      case _ => expr.Clone()
    }

    method GenExprConvertOther(
      expr: R.Expr,
      exprOwnership: Ownership,
      fromTpe: Type,
      toTpe: Type,
      env: Environment,
      expectedOwnership: Ownership
    ) returns (r: R.Expr, resultingOwnership: Ownership)
      requires exprOwnership != OwnershipAutoBorrowed
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
    {
      r := expr;
      resultingOwnership := exprOwnership;
      var fromTpeGen := GenType(fromTpe, GenTypeContext.default());
      var toTpeGen := GenType(toTpe, GenTypeContext.default());
      var upcastConverter := UpcastConversionLambda(fromTpe, fromTpeGen, toTpe, toTpeGen, map[]);
      if upcastConverter.Success? {
        var conversionLambda := upcastConverter.value;
        if resultingOwnership == OwnershipBorrowed {
          // we need the value to be owned for conversion
          r := BorrowedToOwned(r, env);
          resultingOwnership := OwnershipOwned;
        }
        r := conversionLambda.Apply1(r);
        r, resultingOwnership := FromOwnership(r, resultingOwnership, expectedOwnership);
      } else if IsDowncastConversion(fromTpeGen, toTpeGen) {
        assert toTpeGen.IsObjectOrPointer();
        toTpeGen := toTpeGen.ObjectOrPointerUnderlying();
        if resultingOwnership == OwnershipBorrowed {
          // we need the value to be owned for conversion
          r := BorrowedToOwned(r, env);
          resultingOwnership := OwnershipOwned;
        }
        r := R.dafny_runtime
        .MSel(downcast).AsExpr().Apply([r, R.ExprFromType(toTpeGen)]);
        r, resultingOwnership := FromOwnership(r, OwnershipOwned, expectedOwnership);
      } else {
        var Failure((fromType, fromTpeGen, toType, toTpeGen, m)) := upcastConverter;
        r := Error("<i>Coercion from " + fromTpeGen.ToString(IND) + " to " + toTpeGen.ToString(IND) + "</i> not yet implemented", r);
        r, resultingOwnership := FromOwned(r, expectedOwnership);
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
      var argumentOwnership := expectedOwnership;
      if argumentOwnership == OwnershipAutoBorrowed {
        argumentOwnership := OwnershipBorrowed;
        // Otherwise we risk moving a value if it's not borrowed.
      }
      var recursiveGen, recOwned, recIdents := GenExpr(expr, selfIdent, env, argumentOwnership);
      r := recursiveGen;
      readIdents := recIdents;
      r, resultingOwnership := GenExprConvertTo(r, recOwned, fromTpe, toTpe, env, expectedOwnership);
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
      var isSelf := selfIdent.ThisTyped? && selfIdent.IsSelf() && selfIdent.rSelfName == rName;
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
          isSelf &&
          match selfIdent.dafnyType {
            case UserDefined(ResolvedType(_, _, base, attributes, _, _)) =>
              base.Class? || (base.Trait? && base.traitType.ObjectTrait?)
            case _ => false
          };
        if needObjectFromRef {
          r := R.dafny_runtime.MSel("Object").AsExpr().ApplyType([R.TIdentifier("_")]).FSel("from_ref").Apply([r]);
        } else {
          if !noNeedOfClone {
            r := r.Clone(); // We don't transfer the ownership of an identifier
          }
        }
        resultingOwnership := OwnershipOwned;
      } else if currentlyBorrowed {
        assert expectedOwnership == OwnershipBorrowed;
        resultingOwnership := OwnershipBorrowed;
      } else {
        assert expectedOwnership == OwnershipBorrowed;
        var selfIsGeneralTrait :=
          isSelf &&
          match selfIdent.dafnyType {
            case UserDefined(ResolvedType(_, _, base, attributes, _, _)) =>
              base.Trait? && base.traitType.GeneralTrait?
            case _ => false
          };
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
      ghost e: Expression,
      selfIdent: SelfInfo,
      name: CallName,
      typeArgs: seq<Type>,
      args: seq<Expression>,
      env: Environment
    ) returns (argExprs: seq<R.Expr>, readIdents: set<string>, typeExprs: seq<R.Type>, fullNameQualifier: Option<ResolvedType>)
      modifies this
      requires forall a <- args :: a < e
      decreases e, 1, 1, 1
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
        assert args[i] in args;
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
          if resolvedType.kind.Trait? ||
             nameIdent.dafny_name in builtin_trait_preferred_methods ||
             forall m <- resolvedType.properMethods :: m != nameIdent {
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
      modifies this
      ensures OwnershipGuarantee(expectedOwnership, resultingOwnership)
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
          r := R.TraitCast(typExpr, R.DefaultTrait).FSel("default").Apply0();
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
            r := R.TypeAscription(
              r,
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

          r := R.UnaryOp("!", recursiveGen, format);
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
            var rIdent, _, _ := GenIdent(name, selfIdent, lEnv, if !isConstant && ty.CanReadWithoutClone() then OwnershipOwned else OwnershipBorrowed);
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
            var originalMutability := OwnershipOwned;
            match fieldMutability {
              case ConstantField() => // Good
              case InternalClassConstantFieldOrDatatypeDestructor() =>
                originalMutability := OwnershipBorrowed;
              case ClassMutableField() =>
                r := Error("datatypes don't have mutable fields");
            }
            var typ := GenType(fieldType, GenTypeContext.default());
            // All fields are returned as addresses for now until we have something more clever
            r, resultingOwnership := FromOwnership(r, originalMutability, expectedOwnership);
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
              case InternalClassConstantFieldOrDatatypeDestructor() =>
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
          r, readIdents := GenOwnedCallPart(e, on, selfIdent, name, typeArgs, args, env);
          r, resultingOwnership := FromOwned(r, expectedOwnership);
          return;
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
          var subEnv := env.ToOwned().merge(Environment(paramNames, paramTypesMap, {}));

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

          var newEnv := Environment(paramNames, paramTypes, {});

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
        s := s + R.Mod(
          "Flattens all imported externs so that they can be accessed from this module",
          [],
          DAFNY_EXTERN_MODULE, externUseDecls).ToString("") + "\n";
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