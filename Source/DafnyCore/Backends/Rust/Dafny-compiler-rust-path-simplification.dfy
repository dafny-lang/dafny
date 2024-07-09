module FactorPathsOptimizationTest {
  export provides TestApply
  import opened RAST
  import opened FactorPathsOptimization

  method TestApply() {
    var T_Decl := TypeParamDecl("T", [DafnyType]);
    var T_Decl_simp := TypeParamDecl("T", [TIdentifier("DafnyType")]);
    var T := TIdentifier("T");
    var std_any_Any := global.MSel("std").MSel("any").MSel("Any");
    var Any := TIdentifier("Any");
    expect apply(
      Mod("onemodule", [
          StructDecl(Struct([], "test", [T_Decl],
            NamedFields([Field(PUB, Formal("a", std_any_Any.AsType()))]))),
          //                                   ::std::any::Any ==> Any
          ImplDecl(Impl([T_Decl], TIdentifier("test").Apply([T]), "", [])),
          ImplDecl(
            ImplFor(
              [T_Decl], std_any_Any.AsType(), crate.MSel("onemodule").MSel("test").AsType().Apply([T]), "", []))
          //         ::std::any::Any ==> Any  crate::onemodule::test ==> test
        ])).ToString("") ==
      Mod("onemodule", [
          UseDecl(Use(PUB, std_any_Any)),
          StructDecl(Struct([], "test", [T_Decl_simp], NamedFields([Field(PUB, Formal("a", Any))]))),
          ImplDecl(Impl([T_Decl_simp], TIdentifier("test").Apply([T]), "", [])),
          ImplDecl(ImplFor([T_Decl_simp], Any, TIdentifier("test").Apply([T]), "", []))
        ]).ToString("");
    expect apply(
      Mod("onemodule", [
          ImplDecl(
            ImplFor(
              [T_Decl], dafny_runtime.MSel("UpcastObject").AsType().Apply([TIdentifier("x")]),
                TIdentifier("test").Apply([T]), "", []))
        ])).ToString("") ==
      Mod("onemodule", [
          UseDecl(Use(PUB, dafny_runtime.MSel("UpcastObject"))),
          ImplDecl(
            ImplFor(
              [T_Decl_simp], TIdentifier("UpcastObject").Apply([TIdentifier("x")]),
                TIdentifier("test").Apply([T]), "", []))
        ]).ToString("");
  }
}

module FactorPathsOptimization {
  export provides apply, RAST
  import Std
  import opened RAST
  export Std

  /*function Debug<T>(s: T, msg: string): T {
    s
  } by method {
    print msg, ":", s, "\n";
    return s;
  }*/

  function apply(mod: Mod): Mod {
    if mod.ExternMod? then mod else
    var SelfPath := crate.MSel(mod.name);
    var initialMapping: Mapping := Mapping(map[], []);
    var mappings: Mapping :=
      mod.Fold(initialMapping, (current, modDecl) => GatherModMapping(SelfPath, modDecl, current));
    //var _ := Debug(mappings, "Mappings");
    var pathsToRemove := mappings.ToFinalReplacement();
    var imports := mappings.ToUseStatements(pathsToRemove, SelfPath);
    var rewrittenDeclarations := 
      mod.Fold([], (current, modDecl) requires modDecl < mod =>
        current + [ReplaceModDecl(modDecl, pathsToRemove)]
      );
    var newBody: seq<ModDecl> :=
      imports + rewrittenDeclarations;
    mod.(body := newBody)
  }

  opaque function UniqueElementOf<T>(s: set<T>): (r: T)
    requires |s| == 1
    ensures r in s
  {
    assert forall e: T, e': T | e in s && e' in s :: e == e' by {
      forall e: T, e': T | e in s && e' in s ensures e == e' {
        if e != e' {
          assert e' in (s - {e});
          assert |s - {e}| == 0;
        }
      }
    }
    var e :| e in s;
    e
  }

  datatype Mapping = Mapping(
    provenance: map<string, set<Path>>,
    keys: seq<string>
  ) {
    function Add(k: string, path: Path): Mapping {
      if k in provenance then
        this.(provenance := provenance[k := provenance[k] + {path}])
      else
        this.(provenance := provenance[k := {path}], keys := keys + [k])
    }

    function ToFinalReplacement(): FinalReplacement {
      map identifier <- provenance, paths
      | paths == provenance[identifier] &&
        (|| |paths| == 1
         || exists p <- paths :: p == dafny_runtime)
      ::
        identifier := if |paths| == 1 then UniqueElementOf(paths) else dafny_runtime
    }
    function ToUseStatements(finalReplacement: FinalReplacement, SelfPath: Path): seq<ModDecl>
      requires finalReplacement == ToFinalReplacement()
    {
      var toUse := Std.Collections.Seq.Filter(
        (key: string) => key in finalReplacement && finalReplacement[key] != SelfPath, keys);
      seq(|toUse|, i requires 0 <= i < |toUse| =>
        UseDecl(Use(PUB, finalReplacement[toUse[i]].MSel(toUse[i]))))
    }
  }

  type FinalReplacement = map<string, Path>

  function GatherModMapping(prefix: Path, modDecl: ModDecl, current: Mapping): Mapping {
    match modDecl {
      case ModDecl(mod) =>
        current.Add(mod.name, prefix) // Modules must be handled independently 
      case StructDecl(struct) =>
        current.Add(struct.name, prefix)
      case TypeDecl(tpe) =>
        current.Add(tpe.name, prefix)
      case ConstDecl(c) =>
        current.Add(c.name, prefix)
      case EnumDecl(enum) =>
        current.Add(enum.name, prefix)
      case ImplDecl(impl) =>
        GatherImplMapping(impl, current)
      case TraitDecl(tr) =>
        current
      case TopFnDecl(fn) =>
        current.Add(fn.fn.name, prefix)
      case UseDecl(use) => // Used for externs with *, we can't extract any name
        current
    }
  }

  function GatherTypeMapping(tpe: Type, current: Mapping): Mapping {
    tpe.Fold(current, (current: Mapping, t: Type) =>
      match t {
        case TypeFromPath(PMemberSelect(base, name)) => current.Add(name, base)
        case _ => current
      }
    )
  }

  function GatherImplMapping(impl: Impl, current: Mapping): Mapping {
    match impl {
      case ImplFor(typeParams, tpe, forType, where, body) =>
        GatherTypeMapping(forType, GatherTypeMapping(tpe, current))
        // TODO: Add body
      case Impl(typeParams, tpe, where, body) =>
        GatherTypeMapping(tpe, current)
    }
  }

  function ReplaceModDecl(modDecl: ModDecl, replacement: FinalReplacement): ModDecl {
    match modDecl {
      case ModDecl(mod) =>
        ModDecl(apply(mod)) // We optimize independently submodules
      case StructDecl(struct) => StructDecl(ReplaceStruct(struct, replacement))
      case TypeDecl(tpe) => modDecl // TODO
      case ConstDecl(c) => modDecl // TODO
      case EnumDecl(enum) => modDecl // TODO
      case ImplDecl(impl) => ImplDecl(ReplaceImplDecl(impl, replacement))
      case TraitDecl(tr) => modDecl // TODO
      case TopFnDecl(fn) => modDecl // TODO
      case UseDecl(use) => modDecl
    }
  }

  function ReplaceType(t: Type, replacement: FinalReplacement): Type {
    match t {
      case TypeFromPath(PMemberSelect(base, id)) =>
        if id in replacement && replacement[id] == base then
          TSynonym(TIdentifier(id), t)
        else
          t
      case _ => t              
    }
  }

  const typeReplacer: FinalReplacement -> Type -> Type :=
    (replacement: FinalReplacement) => (t: Type) => ReplaceType(t, replacement)
  
  function ReplaceTypeParams(typeParams: seq<TypeParamDecl>, replacement: FinalReplacement): seq<TypeParamDecl> {
    Std.Collections.Seq.Map((t: TypeParamDecl) =>
      t.(constraints := Std.Collections.Seq.Map((constraint: Type) =>
        ReplaceType(constraint, replacement), t.constraints)),
      typeParams)
  }

  function ReplaceImplDecl(impl: Impl, replacement: FinalReplacement): Impl {
    match impl {
      case ImplFor(typeParams, tpe, forType, where, body) =>
        ImplFor(ReplaceTypeParams(typeParams, replacement), tpe.Replace(typeReplacer(replacement)), forType.Replace(typeReplacer(replacement)), where, body)
        // TODO: Replace body
      case Impl(typeParams, tpe, where, body) =>
        Impl(ReplaceTypeParams(typeParams, replacement), tpe.Replace(typeReplacer(replacement)), where, body)
    }
  }

  function ReplaceStruct(struct: Struct, replacement: FinalReplacement): Struct {
    match struct {
      case Struct(attributes, name, typeParams, fields) =>
        Struct(attributes, name, ReplaceTypeParams(typeParams, replacement), 
          ReplaceFields(fields, replacement)
        )
    }
  }
  function ReplaceFields(fields: Fields, replacement: FinalReplacement): Fields {
    match fields {
      case NamedFields(sFields) =>
        NamedFields(Std.Collections.Seq.Map((f: Field) =>
          f.(formal := f.formal.(tpe := ReplaceType(f.formal.tpe, replacement))), sFields
        ))
      case NamelessFields(sFields) =>
        NamelessFields(Std.Collections.Seq.Map((f: NamelessField) =>
          f.(tpe := ReplaceType(f.tpe, replacement)), sFields))
    }
  }
}
