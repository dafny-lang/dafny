module FactorPathsOptimizationTest {
  export provides TestApply
  import opened RAST
  import opened FactorPathsOptimization
  import opened Std.Wrappers

  method ShouldBeEqual(a: Mod, b: Mod) {
    var sA := a.ToString("");
    var sB := b.ToString("");
    if sA != sB {
      print "Got:\n" + sA + "\n";
      print "Expected:\n" + sB + "\n";
      expect sA == sB;
    }
  }

  method TestApply() {
    var T_Decl := TypeParamDecl("T", [DafnyType]);
    var T_Decl_simp := TypeParamDecl("T", [TIdentifier("DafnyType")]);
    var T := TIdentifier("T");
    var std_any_Any := global.MSel("std").MSel("any").MSel("Any");
    var Any := TIdentifier("Any");
    ShouldBeEqual(
      apply(crate)(
        Mod(
          NoDoc, NoAttr,
          "onemodule", [
            StructDecl(
              Struct(NoDoc, [], "test", [T_Decl],
                     NamedFields([Field(PUB, Formal("a", std_any_Any.AsType()))]))),
            //                                   ::std::any::Any ==> Any
            ImplDecl(Impl([T_Decl], TIdentifier("test").Apply([T]), [])),
            ImplDecl(
              ImplFor(
                [T_Decl], std_any_Any.AsType(), crate.MSel("onemodule").MSel("test").AsType().Apply([T]), []))
            //         ::std::any::Any ==> Any  crate::onemodule::test ==> test
          ])),
      Mod(
        NoDoc, NoAttr,
        "onemodule", [
          UseDecl(Use(PUB, dafny_runtime.MSel("DafnyType"))),
          UseDecl(Use(PUB, std_any_Any)),
          StructDecl(
            Struct(NoDoc, [], "test", [T_Decl_simp],
                   NamedFields([Field(PUB, Formal("a", Any))]))),
          ImplDecl(Impl([T_Decl_simp], TIdentifier("test").Apply([T]), [])),
          ImplDecl(ImplFor([T_Decl_simp], Any, TIdentifier("test").Apply([T]), []))
        ]));
    ShouldBeEqual(
      apply(crate)(
        Mod(
          NoDoc, NoAttr,
          "onemodule", [
            ImplDecl(
              ImplFor(
                [T_Decl], dafny_runtime.MSel("UpcastObject").AsType().Apply([TIdentifier("x")]),
                TIdentifier("test").Apply([T]), []))
          ])),
      Mod(
        NoDoc, NoAttr,
        "onemodule", [
          UseDecl(Use(PUB, dafny_runtime.MSel("DafnyType"))),
          UseDecl(Use(PUB, dafny_runtime.MSel("UpcastObject"))),
          ImplDecl(
            ImplFor(
              [T_Decl_simp], TIdentifier("UpcastObject").Apply([TIdentifier("x")]),
              TIdentifier("test").Apply([T]), []))
        ]));
    ShouldBeEqual(
      apply(crate)(
        Mod(
          NoDoc, NoAttr,
          "onemodule", [
            ConstDecl(
              Constant(
                NoDoc, NoAttr,
                "dummy", std_any_Any.AsType(),
                StmtExpr(
                  DeclareVar(
                    MUT, "doit", Some(std_rc_Rc.AsType().Apply1(TIdentifier("unknown"))),
                    Some(
                      Identifier("something").ApplyType(
                        [ DynType(std_default_Default.AsType())
                        ]).Apply([
                                 std_default_Default_default,
                                 dafny_runtime.MSel("rd!").AsExpr().Apply1(Identifier("obj"))
                               ])
                    )),
                  TypeAscription(
                    ExprFromType(
                      dafny_runtime.MSel("DafnyString").AsType()),
                    dafny_runtime.MSel("DafnyType").AsType()))))
          ])),
      Mod(
        NoDoc, NoAttr,
        "onemodule", [
          UseDecl(Use(PUB, std_any_Any)),
          UseDecl(Use(PUB, std_rc_Rc)),
          UseDecl(Use(PUB, std_default_Default)),
          UseDecl(Use(PUB, dafny_runtime.MSel("rd"))),
          UseDecl(Use(PUB, dafny_runtime.MSel("DafnyString"))),
          UseDecl(Use(PUB, dafny_runtime.MSel("DafnyType"))),
          ConstDecl(
            Constant(
              NoDoc, NoAttr,
              "dummy", TIdentifier("Any"),
              StmtExpr(
                DeclareVar(
                  MUT, "doit", Some(TIdentifier("Rc").Apply1(TIdentifier("unknown"))),
                  Some(
                    Identifier("something").ApplyType(
                      [ DynType(TIdentifier("Default"))
                      ]).Apply([
                               Identifier("Default").FSel("default").Apply([]),
                               Identifier("rd!").Apply1(Identifier("obj"))
                             ])
                  )),
                TypeAscription(
                  ExprFromType(
                    TIdentifier("DafnyString")),
                  TIdentifier("DafnyType")))))
        ]));

    // Edge case: There is a trait in the current module
    // And we have a constant of the type of this trait
    // and another the type of another trait in another module but with the same name.
    ShouldBeEqual(
      apply(crate)(
        Mod(
          NoDoc, NoAttr,
          "onemodule", [
            TraitDecl(
              Trait(
                NoDoc, NoAttr, [],
                TIdentifier("Something"), [], [])
            ),
            ConstDecl(
              Constant(
                NoDoc, NoAttr,
                "dummyExtern", crate.MSel("anothermodule").MSel("Something").AsType(),
                RawExpr("nothing"))),
            ConstDecl(
              Constant(
                NoDoc, NoAttr,
                "dummyIntern", crate.MSel("onemodule").MSel("Something").AsType(),
                RawExpr("nothing")))
          ])),
      Mod(
        NoDoc, NoAttr,
        "onemodule", [
          TraitDecl(
            Trait(NoDoc, NoAttr, [], TIdentifier("Something"), [], [])
          ),
          ConstDecl(
            Constant(
              NoDoc, NoAttr,
              "dummyExtern", crate.MSel("anothermodule").MSel("Something").AsType(), // No simplification
              RawExpr("nothing"))),
          ConstDecl(
            Constant(
              NoDoc, NoAttr,
              "dummyIntern", TIdentifier("Something"),
              RawExpr("nothing")))
        ])
    );
  }
}

module FactorPathsOptimization {
  export provides apply, RAST
  import Std
  import opened RAST
  export Std

  function apply(root: Path): Mod -> Mod {
    (mod: Mod) => applyPrefix(mod, root.MSel(mod.name))
  }

  function applyPrefix(mod: Mod, SelfPath: Path): Mod
    decreases mod, 1
  {
    if mod.ExternMod? then mod else
    var mappings: Mapping := PathsVisitor().VisitMod(Mapping(map[], []), mod, SelfPath);
    var pathsToRemove := mappings.ToFinalReplacement(SelfPath);
    var imports := mappings.ToUseStatements(pathsToRemove, SelfPath);
    var mod := PathSimplifier(mod, pathsToRemove).ReplaceMod(mod, SelfPath);
    mod.(body := imports + mod.body)
  }

  // Retrieves the unique element of a singleton set
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

  type FinalReplacement = map<string, Path>

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

    // For any mapping identifier -> full paths,
    // we will perform the replacement either if there is exactly one full path,
    // or if the path is the dafny runtime (in which cases, all other homonyms remain fully prefixed)
    function ToFinalReplacement(SelfPath: Path): FinalReplacement {
      map identifier <- provenance, paths
        | paths == provenance[identifier] &&
          (|| |paths| == 1
           || SelfPath in paths
           || dafny_runtime in paths)
        ::
          identifier := if |paths| == 1 then UniqueElementOf(paths) else
                        if SelfPath in paths then SelfPath else dafny_runtime
    }
    // Given a final replacement map,
    // creates a sequence of use statements to be inserted at the beginning of the module
    function ToUseStatements(finalReplacement: FinalReplacement, SelfPath: Path): seq<ModDecl>
      requires finalReplacement == ToFinalReplacement(SelfPath)
    {
      var toUse :=
        Std.Collections.Seq.Filter(
          (key: string) => key in finalReplacement && finalReplacement[key] != SelfPath,
          keys);
      seq(|toUse|, i requires 0 <= i < |toUse| =>
        UseDecl(Use(PUB, finalReplacement[toUse[i]].MSel(toUse[i]))))
    }
  }

  function PathsVisitor(): RASTTopDownVisitor<Mapping> {
    RASTTopDownVisitor(
      VisitTypeSingle := (current: Mapping, t: Type) =>
        match t {
          case TypeFromPath(PMemberSelect(base, name)) =>
            if base == Self() then current else current.Add(name, base)
          case _ => current
        },
      VisitExprSingle := (current: Mapping, e: Expr) =>
        match e {
          case ExprFromPath(PMemberSelect(base, id)) =>
            if base == Self() then current else
            if |id| > 0 && id[|id|-1] == '!' then
              current.Add(id[..|id|-1], base)
            else
              current.Add(id, base)
          case _ => current
        }
    ,
      VisitModDeclSingle := (current: Mapping, modDecl: ModDecl, prefix: Path) =>
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
            current
          case TraitDecl(tr) =>
            match tr.tpe {
              case TypeApp(TIdentifier(name), _) =>
                current.Add(name, prefix)
              case TIdentifier(name) =>
                current.Add(name, prefix)
              case _ =>
                current
            }
          case TopFnDecl(fn) =>
            current.Add(fn.fn.name, prefix)
          case UseDecl(use) => // Used for externs with *, we can't extract any name
            current
        },
      recurseSubmodules := false // Recursion is done manually
    )
  }

  function PathSimplifier(ghost mParent: Mod, replacement: FinalReplacement): RASTBottomUpReplacer
    decreases mParent, 0
  {
    RASTBottomUpReplacer(
      ReplaceModSingle :=
        (m: Mod, SelfPath: Path) requires m < mParent =>
          applyPrefix(m, SelfPath.MSel(m.name)),
      ReplaceTypeSingle := (t: Type) =>
        match t {
          case TypeFromPath(PMemberSelect(base, id)) =>
            if id in replacement && replacement[id] == base then
              TSynonym(TIdentifier(id), t)
            else
              t
          case _ => t
        },
      ReplaceExprSingle :=
        (e: Expr) =>
          match e {
            case ExprFromPath(PMemberSelect(base, id)) =>
              if id in replacement && replacement[id] == base then
                Identifier(id)
              else if |id| > 0 && id[|id|-1] == '!' then
                var macro_id := id[..|id|-1];
                if macro_id in replacement && replacement[macro_id] == base then
                  Identifier(id)
                else e
              else e
            case _ => e
          }

    )
  }
}
