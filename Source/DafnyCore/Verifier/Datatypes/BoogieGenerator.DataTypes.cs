
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using System.Text;
using Microsoft.Boogie;
using static Microsoft.Dafny.Util;

namespace Microsoft.Dafny {
  partial class BoogieGenerator {
    void AddDatatype(DatatypeDecl dt) {
      Contract.Requires(dt != null);
      Contract.Requires(sink != null && Predef != null);

      var mayInvolveReferences = UserDefinedType.FromTopLevelDecl(dt.Origin, dt).MayInvolveReferences;
      var constructorFunctions = dt.Ctors.ToDictionary(ctor => ctor, ctor => AddDataTypeConstructor(dt, ctor, mayInvolveReferences));
      if (!mayInvolveReferences) {
        AddCommonIsAllocConstructorAxiom(dt);
      }

      AddDepthOneCaseSplitFunction(dt);

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
        MkIsPredicateForDatatype(dt, out var boundVariables, out var d, out _, out var isPredicate);
        Bpl.Expr cases_body = Bpl.Expr.False;
        Bpl.Trigger tr = null;
        foreach (DatatypeCtor ctor in dt.Ctors) {
          var disj = FunctionCall(ctor.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, d);
          cases_body = BplOr(cases_body, disj);
          tr = new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { disj, isPredicate }, tr);
        }
        var body = BplImp(isPredicate, cases_body);
        var ax = BplForall(boundVariables, tr, body);
        var axiom = new Bpl.Axiom(dt.Origin, ax, "Questionmark data type disjunctivity");
        sink.AddTopLevelDeclaration(axiom);
      }

      if (dt is IndDatatypeDecl indDatatypeDecl) {
        AddInductiveDatatypeAxioms(constructorFunctions, indDatatypeDecl);
        AddExtensionalityAxiom(indDatatypeDecl);
      }

      if (dt is CoDatatypeDecl coDatatypeDecl) {
        AddCoDatatypeDeclAxioms(coDatatypeDecl);
      }
    }

    /// <summary>
    /// Add function Dt#Equal(DatatypeType, DatatypeType): bool;
    /// For each constructor Ctor(x: X, y: Y), add an axiom of the form
    ///     forall a, b ::
    ///       { Dt#Equal(a, b), Ctor?(a) }
    ///       { Dt#Equal(a, b), Ctor?(b) }
    ///       Ctor?(a) && Ctor?(b)
    ///       ==>
    ///       (Dt#Equal(a, b) <==>
    ///           X#Equal(a.x, b.x) &&
    ///           Y#Equal(a.y, b.y)
    ///       )
    /// where X#Equal is the equality predicate for type X and a.x denotes Dtor#x(a), and similarly
    /// for Y and b.
    /// Except, in the event that the datatype has exactly one constructor, then instead generate:
    ///     forall a, b ::
    ///       { Dt#Equal(a, b) }
    ///       true
    ///       ==>
    ///       ...as before
    /// </summary>
    private void AddInductiveDatatypeAxioms(Dictionary<DatatypeCtor, Bpl.Function> constructorFunctions,
      IndDatatypeDecl dt) {
      var dtEqualName = DtEqualName(dt);

      var args = new List<Variable>();
      args.Add(new Bpl.Formal(dt.Origin, new Bpl.TypedIdent(dt.Origin, Bpl.TypedIdent.NoName, Predef.DatatypeType), false));
      args.Add(new Bpl.Formal(dt.Origin, new Bpl.TypedIdent(dt.Origin, Bpl.TypedIdent.NoName, Predef.DatatypeType), false));
      var ctorEqualResult =
        new Bpl.Formal(dt.Origin, new Bpl.TypedIdent(dt.Origin, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
      sink.AddTopLevelDeclaration(new Bpl.Function(dt.Origin, dtEqualName, args, ctorEqualResult,
        "Datatype extensional equality declaration"));

      var aVar = BplBoundVar("a", Predef.DatatypeType, out var a);
      var bVar = BplBoundVar("b", Predef.DatatypeType, out var b);

      var dtEqual = FunctionCall(dt.Origin, dtEqualName, Bpl.Type.Bool, a, b);

      foreach (var ctor in dt.Ctors) {
        Bpl.Trigger trigger;
        Bpl.Expr ante;
        if (dt.Ctors.Count == 1) {
          ante = Bpl.Expr.True;
          trigger = BplTrigger(dtEqual);
        } else {
          var ctorQ = GetReadonlyField(ctor.QueryField);
          var ctorQa = FunctionCall(ctor.Origin, ctorQ.Name, Bpl.Type.Bool, a);
          var ctorQb = FunctionCall(ctor.Origin, ctorQ.Name, Bpl.Type.Bool, b);
          ante = BplAnd(ctorQa, ctorQb);
          trigger = dt.Ctors.Count == 1
            ? BplTrigger(dtEqual)
            : new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { dtEqual, ctorQa },
              new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { dtEqual, ctorQb }));
        }

        Bpl.Expr eqs = Bpl.Expr.True;
        for (var i = 0; i < ctor.Formals.Count; i++) {
          var arg = ctor.Formals[i];
          var dtor = GetReadonlyField(ctor.Destructors[i]);
          var dtorA = FunctionCall(ctor.Origin, dtor.Name, TrType(arg.Type), a);
          var dtorB = FunctionCall(ctor.Origin, dtor.Name, TrType(arg.Type), b);
          var eq = TypeSpecificEqual(ctor.Origin, arg.Type, dtorA, dtorB);
          eqs = BplAnd(eqs, eq);
        }

        var ax = BplForall(new List<Variable> { aVar, bVar }, trigger, BplImp(ante, BplIff(dtEqual, eqs)));
        AddOtherDefinition(constructorFunctions[ctor], new Bpl.Axiom(dt.Origin, ax, $"Datatype extensional equality definition: {ctor.FullName}"));
      }
    }

    private static string DtEqualName(IndDatatypeDecl dt) {
      return dt.FullSanitizedName + "#Equal";
    }

    // Add extensionality axiom: forall a, b :: { Dt#Equal(a, b) } Dt#Equal(a, b) <==> a == b
    private void AddExtensionalityAxiom(IndDatatypeDecl dt) {
      var dtEqualName = DtEqualName(dt);
      {
        var aVar = BplBoundVar("a", Predef.DatatypeType, out var a);
        var bVar = BplBoundVar("b", Predef.DatatypeType, out var b);

        var lhs = FunctionCall(dt.Origin, dtEqualName, Bpl.Type.Bool, a, b);
        var rhs = Bpl.Expr.Eq(a, b);

        var ax = BplForall(new List<Variable> { aVar, bVar }, BplTrigger(lhs), BplIff(lhs, rhs));
        sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.Origin, ax, $"Datatype extensionality axiom: {dt.FullName}"));
      }
    }

    private void AddCoDatatypeDeclAxioms(CoDatatypeDecl codecl) {
      Func<Bpl.Expr, Bpl.Expr> MinusOne = k => {
        if (k == null) {
          return null;
        } else if (k.Type.IsInt) {
          return Bpl.Expr.Sub(k, Bpl.Expr.Literal(1));
        } else {
          return FunctionCall(k.tok, "ORD#Minus", k.Type, k,
            FunctionCall(k.tok, "ORD#FromNat", k.Type, Bpl.Expr.Literal(1)));
        }
      };

      Action<Bpl.Type, Action<Tuple<List<Type>, List<Type>>, List<Bpl.Variable>, List<Bpl.Expr>, List<Bpl.Expr>,
        Bpl.Variable, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr, Bpl.Expr>> CoAxHelper =
        (typeOfK, K) => {
          List<TypeParameter> Renew(string s) => Map(codecl.TypeArgs, tp => new TypeParameter(tp.Origin, tp.NameNode.Append("#" + s), tp.PositionalIndex, tp.Parent));
          List<TypeParameter> typaramsL = Renew("l"), typaramsR = Renew("r");
          var lvars = MkTyParamBinders(typaramsL, out var lexprs);
          var rvars = MkTyParamBinders(typaramsR, out var rexprs);
          Func<List<TypeParameter>, List<Type>> Types = l => Map(l, tp => (Type)new UserDefinedType(tp));
          var tyargs = Tuple.Create(Types(typaramsL), Types(typaramsR));

          var vars = Concat(lvars, rvars);

          Bpl.Expr k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit;
          Bpl.Variable kVar;
          if (typeOfK != null) {
            kVar = BplBoundVar("k", typeOfK, out k);
            vars.Add(kVar);
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
            kVar = null;
            k = null;
            kIsValid = Bpl.Expr.True;
            kIsNonZero = Bpl.Expr.True;
            kHasSuccessor = Bpl.Expr.True;
            kIsLimit = Bpl.Expr.True;
          }

          var ly = BplBoundVar("ly", Predef.LayerType, vars);
          var d0 = BplBoundVar("d0", Predef.DatatypeType, vars);
          var d1 = BplBoundVar("d1", Predef.DatatypeType, vars);

          K(tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1);
        };

      Action<Bpl.Type> AddAxioms = typeOfK => {
        {
          // Add two copies of the type parameter lists!
          var args = MkTyParamFormals(Concat(GetTypeParams(codecl), GetTypeParams(codecl)), false, false);
          if (typeOfK != null) {
            args.Add(BplFormalVar(null, typeOfK, true));
          }

          args.Add(BplFormalVar(null, Predef.LayerType, true));
          args.Add(BplFormalVar(null, Predef.DatatypeType, true));
          args.Add(BplFormalVar(null, Predef.DatatypeType, true));
          var r = BplFormalVar(null, Bpl.Type.Bool, false);
          var fn_nm = typeOfK != null ? CoPrefixName(codecl) : CoEqualName(codecl);
          var fn = new Bpl.Function(codecl.Origin, fn_nm, args, r);
          if (InsertChecksums) {
            InsertChecksum(codecl, fn);
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
        CoAxHelper(typeOfK,
          (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var eqDt = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var iss = BplAnd(MkIs(d0, ClassTyCon(codecl, lexprs)), MkIs(d1, ClassTyCon(codecl, rexprs)));
            var body = BplImp(
              iss,
              BplIff(eqDt,
                BplAnd(
                  BplImp(kHasSuccessor,
                    BplOr(CoPrefixEquality(codecl.Origin, codecl, tyargs.Item1, tyargs.Item2, MinusOne(k), ly, d0, d1))),
                  k == null
                    ? Bpl.Expr.True
                    : BplImp(BplAnd(kIsNonZero, kIsLimit),
                      CoEqualCall(codecl, tyargs.Item1, tyargs.Item2, null, ly, d0, d1)))));
            var ax = BplForall(vars, BplTrigger(eqDt), body);
            AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Bpl.Axiom(codecl.Origin, ax, "Layered co-equality axiom"));
          });

        // axiom (forall G0,...,Gn : Ty, k: int, ly : Layer, d0, d1: DatatypeType ::
        //  { Eq(G0, .., Gn, S(ly), k, d0, d1) }
        //    0 < k ==>
        //      (Eq(G0, .., Gn, S(ly), k, d0, d1) <==>
        //       Eq(G0, .., Gn, ly, k, d0, d))
        CoAxHelper(typeOfK,
          (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var eqDtSL = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
            var eqDtL = CoEqualCall(codecl, lexprs, rexprs, k, ly, d0, d1);
            var body = BplImp(kIsNonZero, BplIff(eqDtSL, eqDtL));
            var ax = BplForall(vars, BplTrigger(eqDtSL), body);
            AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Bpl.Axiom(codecl.Origin, ax, "Unbump layer co-equality axiom"));
          });
      };

      AddAxioms(null); // Add the above axioms for $Equal

      // axiom (forall d0, d1: DatatypeType, k: int :: { $Equal(d0, d1) } :: Equal(d0, d1) <==> d0 == d1);
      CoAxHelper(null, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
        var Eq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
        var equal = Bpl.Expr.Eq(d0, d1);
        AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Axiom(codecl.Origin,
          BplForall(vars, BplTrigger(Eq), BplIff(Eq, equal)),
          "Equality for codatatypes"));
      });

      Bpl.Type theTypeOfK = Predef.BigOrdinalType;
      AddAxioms(Predef.BigOrdinalType); // Add the above axioms for $PrefixEqual

      // The connection between the full codatatype equality and its prefix version
      // axiom (forall d0, d1: DatatypeType :: $Eq#Dt(d0, d1) <==>
      //                                       (forall k: int :: 0 <= k ==> $PrefixEqual#Dt(k, d0, d1)));
      CoAxHelper(theTypeOfK, (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
        var Eq = CoEqualCall(codecl, lexprs, rexprs, null, LayerSucc(ly), d0, d1);
        var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
        vars.Remove(kVar);
        AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Axiom(codecl.Origin,
          BplForall(vars, BplTrigger(Eq), BplIff(Eq, BplForall(kVar, BplTrigger(PEq), BplImp(kIsValid, PEq)))),
          "Coequality and prefix equality connection"));
      });
      // In addition, the following special case holds for $Eq#Dt:
      // axiom (forall d0, d1: DatatypeType :: $Eq#Dt(d0, d1) <==
      //                                       (forall k: int :: 0 <= k ==> $PrefixEqual#Dt(ORD#FromNat(k), d0, d1)));
      if (!theTypeOfK.IsInt) {
        CoAxHelper(Bpl.Type.Int,
          (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
            var Eq = CoEqualCall(codecl, lexprs, rexprs, null, LayerSucc(ly), d0, d1);
            var PEq = CoEqualCall(codecl, lexprs, rexprs, FunctionCall(k.tok, "ORD#FromNat", Predef.BigOrdinalType, k),
              LayerSucc(ly), d0, d1);
            vars.Remove(kVar);
            AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Axiom(codecl.Origin,
              BplForall(vars, BplTrigger(Eq), BplImp(BplForall(kVar, BplTrigger(PEq), BplImp(kIsValid, PEq)), Eq)),
              "Coequality and prefix equality connection"));
          });
      }

      // A consequence of the definition of prefix equalities is the following:
      // axiom (forall k, m: int, d0, d1: DatatypeType :: 0 <= k <= m && $PrefixEq#Dt(m, d0, d1) ==> $PrefixEq#0#Dt(k, d0, d1));
      CoAxHelper(theTypeOfK,
        (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var m = BplBoundVar("m", k.Type, vars);
          var PEqK = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var PEqM = CoEqualCall(codecl, lexprs, rexprs, m, LayerSucc(ly), d0, d1);
          Bpl.Expr kLtM;
          if (k.Type.IsInt) {
            kLtM = Bpl.Expr.Lt(k, m);
          } else {
            kLtM = FunctionCall(codecl.Origin, "ORD#Less", Bpl.Type.Bool, k, m);
          }
          AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Axiom(codecl.Origin,
            BplForall(vars,
              new Bpl.Trigger(codecl.Origin, true, new List<Bpl.Expr> { PEqK, PEqM }),
              BplImp(BplAnd(BplAnd(kIsValid, kLtM), PEqM), PEqK)),
            "Prefix equality consequence"));
        });

      // With the axioms above, going from d0==d1 to a prefix equality requires going via the full codatatype
      // equality, which in turn requires the full codatatype equality to be present.  The following axiom
      // provides a shortcut:
      // axiom (forall d0, d1: DatatypeType, k: int :: d0 == d1 && 0 <= k ==> $PrefixEqual#_module.Stream(k, d0, d1));
      CoAxHelper(theTypeOfK,
        (tyargs, vars, lexprs, rexprs, kVar, k, kIsValid, kIsNonZero, kHasSuccessor, kIsLimit, ly, d0, d1) => {
          var equal = Bpl.Expr.Eq(d0, d1);
          var PEq = CoEqualCall(codecl, lexprs, rexprs, k, LayerSucc(ly), d0, d1);
          var trigger = BplTrigger(PEq);
          AddOtherDefinition(GetOrCreateTypeConstructor(codecl), new Axiom(codecl.Origin,
            BplForall(vars, trigger, BplImp(BplAnd(equal, kIsValid), PEq)), "Prefix equality shortcut"));
        });
    }

    private void AddDepthOneCaseSplitFunction(DatatypeDecl dt) {
      // Add:
      //   function $IsA#Dt(G: Ty,d: DatatypeType): bool {
      //     Dt.Ctor0?(G, d) || Dt.Ctor1?(G, d) || ...
      //   }
      var cases_dBv = new Bpl.Formal(dt.Origin, new Bpl.TypedIdent(dt.Origin, Bpl.TypedIdent.NoName, Predef.DatatypeType), true);
      var cases_resType = new Bpl.Formal(dt.Origin, new Bpl.TypedIdent(dt.Origin, Bpl.TypedIdent.NoName, Bpl.Type.Bool), false);
      var cases_fn = new Bpl.Function(dt.Origin, "$IsA#" + dt.FullSanitizedName,
        new List<Variable> { cases_dBv },
        cases_resType,
        "Depth-one case-split function");

      if (InsertChecksums) {
        InsertChecksum(dt, cases_fn);
      }

      sink.AddTopLevelDeclaration(cases_fn);
      // and here comes the actual axiom:
      var dVar = BplBoundVar("d", Predef.DatatypeType, out var d);
      var lhs = FunctionCall(dt.Origin, cases_fn.Name, Bpl.Type.Bool, d);
      Bpl.Expr cases_body = Bpl.Expr.False;
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var disj = FunctionCall(ctor.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, d);
        cases_body = BplOr(cases_body, disj);
      }

      var ax = BplForall(new List<Variable> { dVar }, BplTrigger(lhs), BplImp(lhs, cases_body));
      sink.AddTopLevelDeclaration(new Bpl.Axiom(dt.Origin, ax, "Depth-one case-split axiom"));
    }

    private Bpl.Function AddDataTypeConstructor(DatatypeDecl dt, DatatypeCtor ctor, bool includeIsAllocAxiom) {
      // Add:  function #dt.ctor(tyVars, paramTypes) returns (DatatypeType);

      List<Bpl.Variable> argTypes = new List<Bpl.Variable>();
      foreach (Formal arg in ctor.Formals) {
        Bpl.Variable a = new Bpl.Formal(arg.Origin, new Bpl.TypedIdent(arg.Origin, Bpl.TypedIdent.NoName, TrType(arg.Type)),
          true);
        argTypes.Add(a);
      }

      Bpl.Variable resType = new Bpl.Formal(ctor.Origin,
        new Bpl.TypedIdent(ctor.Origin, Bpl.TypedIdent.NoName, Predef.DatatypeType), false);
      Bpl.Function fn;
      if (dt is TupleTypeDecl ttd && ttd.Dims == 2 && ttd.NonGhostDims == 2) {
        fn = Predef.Tuple2Constructor;
      } else {
        fn = new Bpl.Function(ctor.Origin, ctor.FullName, argTypes, resType, "Constructor function declaration");
        sink.AddTopLevelDeclaration(fn);
      }

      if (InsertChecksums) {
        InsertChecksum(dt, fn);
      }


      {
        // Add:  const unique ##dt.ctor: DtCtorId;
        var definitionAxioms = new List<Axiom>();
        Bpl.Constant constructorId = new Bpl.Constant(ctor.Origin,
          new Bpl.TypedIdent(ctor.Origin, "#" + ctor.FullName, Predef.DtCtorId), true,
          definitionAxioms: definitionAxioms);
        Bpl.Expr constructorIdReference = new Bpl.IdentifierExpr(ctor.Origin, constructorId);
        var constructorIdentifierAxiom = CreateConstructorIdentifierAxiom(ctor, constructorIdReference);
        AddOtherDefinition(fn, constructorIdentifierAxiom);
        definitionAxioms.Add(constructorIdentifierAxiom);
        sink.AddTopLevelDeclaration(constructorId);

        {
          // Add:  function dt.ctor?(this: DatatypeType): bool { DatatypeCtorId(this) == ##dt.ctor }
          var queryField = GetReadonlyField(ctor.QueryField);
          sink.AddTopLevelDeclaration(queryField);

          // and here comes the associated axiom:

          var thVar = BplBoundVar("d", Predef.DatatypeType, out var th);
          var queryPredicate = FunctionCall(ctor.Origin, queryField.Name, Bpl.Type.Bool, th);
          var ctorId = FunctionCall(ctor.Origin, BuiltinFunction.DatatypeCtorId, null, th);
          var rhs = Bpl.Expr.Eq(ctorId, constructorIdReference);
          var body = BplIff(queryPredicate, rhs);
          var tr = BplTrigger(queryPredicate);
          var ax = BplForall(thVar, tr, body);
          sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, ax, "Questionmark and identifier"));
        }

        // check well-formedness of any default-value expressions
        AddWellformednessCheck(ctor);
      }


      {
        // Add:  axiom (forall d: DatatypeType :: dt.ctor?(d) ==> (exists params :: d == #dt.ctor(params));
        CreateBoundVariables(ctor.Formals, out var bvs, out var args);
        Bpl.Expr rhs = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
        var dBv = BplBoundVar("d", Predef.DatatypeType, out var dId);
        Bpl.Expr q = Bpl.Expr.Eq(dId, rhs);
        if (bvs.Count != 0) {
          q = new Bpl.ExistsExpr(ctor.Origin, bvs, null /*always in a Skolemization context*/, q);
        }

        Bpl.Expr dtq = FunctionCall(ctor.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, dId);
        var trigger = BplTrigger(dtq);
        q = BplForall(dBv, trigger, BplImp(dtq, q));
        sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Constructor questionmark has arguments"));
      }

      AddConstructorAxioms(dt, ctor, fn, includeIsAllocAxiom);

      if (dt is IndDatatypeDecl) {
        // Add Lit axiom:
        // axiom (forall p0, ..., pn :: #dt.ctor(Lit(p0), ..., Lit(pn)) == Lit(#dt.ctor(p0, .., pn)));
        CreateBoundVariables(ctor.Formals, out var bvs, out var args);
        var litargs = new List<Bpl.Expr>();
        foreach (Bpl.Expr arg in args) {
          litargs.Add(Lit(arg));
        }

        Bpl.Expr lhs = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, litargs);
        Bpl.Expr rhs = Lit(FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args), Predef.DatatypeType);
        Bpl.Expr q = BplForall(bvs, BplTrigger(lhs), Bpl.Expr.Eq(lhs, rhs));
        var constructorLiteralAxiom = new Bpl.Axiom(ctor.Origin, q, "Constructor literal");
        AddOtherDefinition(fn, constructorLiteralAxiom);
      }

      // Injectivity axioms for normal arguments
      for (int i = 0; i < ctor.Formals.Count; i++) {
        var arg = ctor.Formals[i];
        // function ##dt.ctor#i(DatatypeType) returns (Ti);
        var sf = ctor.Destructors[i];
        Contract.Assert(sf != null);
        fn = GetReadonlyField(sf);
        if (fn == Predef.Tuple2Destructors0 || fn == Predef.Tuple2Destructors1) {
          // the two destructors for 2-tuples are predefined in Prelude for use
          // by the Map#Items axiom
        } else if (sf.EnclosingCtors[0] != ctor) {
          // this special field, which comes from a shared destructor, is being declared in a different iteration of this loop
        } else {
          sink.AddTopLevelDeclaration(fn);
        }

        // axiom (forall params :: ##dt.ctor#i(#dt.ctor(params)) == params_i);
        CreateBoundVariables(ctor.Formals, out var bvs, out var args);
        var inner = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
        var outer = FunctionCall(ctor.Origin, fn.Name, TrType(arg.Type), inner);
        var q = BplForall(bvs, BplTrigger(inner), Bpl.Expr.Eq(outer, args[i]));
        AddOtherDefinition(fn, (new Bpl.Axiom(ctor.Origin, q, "Constructor injectivity")));

        if (dt is IndDatatypeDecl) {
          var argType = arg.Type.NormalizeExpand();
          if (argType.IsDatatype || argType.IsTypeParameter) {
            // for datatype:             axiom (forall params :: {#dt.ctor(params)} DtRank(params_i) < DtRank(#dt.ctor(params)));
            // for type-parameter type:  axiom (forall params :: {#dt.ctor(params)} BoxRank(params_i) < DtRank(#dt.ctor(params)));
            CreateBoundVariables(ctor.Formals, out bvs, out args);
            Bpl.Expr lhs = FunctionCall(ctor.Origin, arg.Type.IsDatatype ? BuiltinFunction.DtRank : BuiltinFunction.BoxRank,
              null, args[i]);
            /* CHECK
              Bpl.Expr lhs = FunctionCall(ctor.Tok, BuiltinFunction.DtRank, null,
                argType.IsDatatype ? args[i] : FunctionCall(ctor.Tok, BuiltinFunction.Unbox, predef.DatatypeType, args[i]));
              */
            Bpl.Expr ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
            var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
            var trigger = BplTrigger(ct);
            q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, Bpl.Expr.Lt(lhs, rhs));
            AddOtherDefinition(fn, new Bpl.Axiom(ctor.Origin, q, "Inductive rank"));
          } else if (argType is SeqType) {
            // axiom (forall params, i: int {#dt.ctor(params)} :: 0 <= i && i < |arg| ==> DtRank(arg[i]) < DtRank(#dt.ctor(params)));
            // that is:
            // axiom (forall params, i: int {#dt.ctor(params)} :: 0 <= i && i < |arg| ==> DtRank(Unbox(Seq#Index(arg,i))) < DtRank(#dt.ctor(params)));
            {
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              Bpl.Variable iVar = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, "i", Bpl.Type.Int));
              bvs.Add(iVar);
              Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.Origin, iVar);
              Bpl.Expr ante = BplAnd(
                Bpl.Expr.Le(Bpl.Expr.Literal(0), ie),
                Bpl.Expr.Lt(ie, FunctionCall(arg.Origin, BuiltinFunction.SeqLength, null, args[i])));
              var seqIndex = FunctionCall(arg.Origin, BuiltinFunction.SeqIndex, Predef.DatatypeType, args[i], ie);
              Bpl.Expr lhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null,
                FunctionCall(arg.Origin, BuiltinFunction.Unbox, Predef.DatatypeType, seqIndex));
              var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
              q = new Bpl.ForallExpr(ctor.Origin, bvs, new Trigger(lhs.tok, true, new List<Bpl.Expr> { seqIndex, ct }),
                BplImp(ante, Bpl.Expr.Lt(lhs, rhs)));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Inductive seq element rank"));
            }

            // axiom (forall params {#dt.ctor(params)} :: SeqRank(arg) < DtRank(#dt.ctor(params)));
            {
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              var lhs = FunctionCall(ctor.Origin, BuiltinFunction.SeqRank, null, args[i]);
              var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
              var trigger = BplTrigger(ct);
              q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, Bpl.Expr.Lt(lhs, rhs));
              AddOtherDefinition(fn, new Bpl.Axiom(ctor.Origin, q, "Inductive seq rank"));
            }
          } else if (argType is SetType) {
            // axiom (forall params, d: Datatype {arg[d], #dt.ctor(params)}  :: arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
            // that is:
            // axiom (forall params, d: Datatype {arg[Box(d)], #dt.ctor(params)} :: arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
            CreateBoundVariables(ctor.Formals, out bvs, out args);
            Bpl.Variable dVar = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, "d", Predef.DatatypeType));
            bvs.Add(dVar);
            Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.Origin, dVar);
            var inSet = IsSetMember(arg.Origin, args[i], FunctionCall(arg.Origin, BuiltinFunction.Box, null, ie), argType.NormalizeToAncestorType().AsSetType.Finite);
            Bpl.Expr lhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ie);
            var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
            var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
            var trigger = new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { inSet, ct });
            q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, BplImp(inSet, Bpl.Expr.Lt(lhs, rhs)));
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Inductive set element rank"));
          } else if (argType is MultiSetType) {
            // axiom (forall params, d: Datatype {arg[d], #dt.ctor(params)} :: 0 < arg[d] ==> DtRank(d) < DtRank(#dt.ctor(params)));
            // that is:
            // axiom (forall params, d: Datatype {arg[Box(d)], #dt.ctor(params)} :: 0 < arg[Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
            CreateBoundVariables(ctor.Formals, out bvs, out args);
            Bpl.Variable dVar = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, "d", Predef.DatatypeType));
            bvs.Add(dVar);
            Bpl.IdentifierExpr ie = new Bpl.IdentifierExpr(arg.Origin, dVar);
            var multiplicity = MultisetMultiplicity(arg.Origin, args[i], FunctionCall(arg.Origin, BuiltinFunction.Box, null, ie));
            Bpl.Expr ante = Bpl.Expr.Gt(multiplicity, Bpl.Expr.Literal(0));
            Bpl.Expr lhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ie);
            var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
            var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
            var trigger = new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { multiplicity, ct });
            q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, BplImp(ante, Bpl.Expr.Lt(lhs, rhs)));
            sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Inductive multiset element rank"));
          } else if (argType is MapType) {
            var finite = ((MapType)argType).Finite;
            {
              // axiom (forall params, d: DatatypeType
              //   { Map#Domain(arg)[$Box(d)], #dt.ctor(params) }
              //   Map#Domain(arg)[$Box(d)] ==> DtRank(d) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              var dVar = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, "d", Predef.DatatypeType));
              bvs.Add(dVar);
              var ie = new Bpl.IdentifierExpr(arg.Origin, dVar);
              var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
              var domain = FunctionCall(arg.Origin, f, finite ? Predef.MapType : Predef.IMapType,
                args[i]);
              var inDomain = IsSetMember(arg.Origin, domain, FunctionCall(arg.Origin, BuiltinFunction.Box, null, ie), finite);
              var lhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ie);
              var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
              var trigger = new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { inDomain, ct });
              q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, BplImp(inDomain, Bpl.Expr.Lt(lhs, rhs)));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Inductive map key rank"));
            }
            {
              // axiom(forall params, bx: Box ::
              //   { Map#Elements(arg)[bx], #dt.ctor(params) }
              //   Map#Domain(arg)[bx] ==> DtRank($Unbox(Map#Elements(arg)[bx]): DatatypeType) < DtRank(#dt.ctor(params)));
              CreateBoundVariables(ctor.Formals, out bvs, out args);
              var bxVar = new Bpl.BoundVariable(arg.Origin, new Bpl.TypedIdent(arg.Origin, "bx", Predef.BoxType));
              bvs.Add(bxVar);
              var ie = new Bpl.IdentifierExpr(arg.Origin, bxVar);
              var f = finite ? BuiltinFunction.MapDomain : BuiltinFunction.IMapDomain;
              var domain = FunctionCall(arg.Origin, f, finite ? Predef.MapType : Predef.IMapType,
                args[i]);
              var inDomain = IsSetMember(arg.Origin, domain, ie, finite);
              var ef = finite ? BuiltinFunction.MapElements : BuiltinFunction.IMapElements;
              var element = FunctionCall(arg.Origin, ef, finite ? Predef.MapType : Predef.IMapType,
                args[i]);
              var elmt = Bpl.Expr.SelectTok(arg.Origin, element, ie);
              var unboxElmt = FunctionCall(arg.Origin, BuiltinFunction.Unbox, Predef.DatatypeType, elmt);
              var lhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, unboxElmt);
              var ct = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
              var rhs = FunctionCall(ctor.Origin, BuiltinFunction.DtRank, null, ct);
              var trigger = new Bpl.Trigger(ctor.Origin, true, new List<Bpl.Expr> { inDomain, ct });
              q = new Bpl.ForallExpr(ctor.Origin, bvs, trigger, BplImp(inDomain, Bpl.Expr.Lt(lhs, rhs)));
              sink.AddTopLevelDeclaration(new Bpl.Axiom(ctor.Origin, q, "Inductive map value rank"));
            }
          }
        }
      }

      return fn;
    }

    private void AddConstructorAxioms(DatatypeDecl dt, DatatypeCtor ctor, Bpl.Function ctorFunction, bool includeIsAllocAxiom) {
      var tyvars = MkTyParamBinders(dt.TypeArgs, out var tyexprs);
      CreateBoundVariables(ctor.Formals, out var bvs, out var args);
      bvs.InsertRange(0, tyvars);
      var c_params = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
      var c_ty = ClassTyCon(dt, tyexprs);
      AddsIsConstructorAxiom(ctor, ctorFunction, args, bvs, c_params, c_ty);
      if (includeIsAllocAxiom) {
        AddIsAllocConstructorAxiom(dt, ctor, ctorFunction, args, bvs, c_params, c_ty);
      }
      AddDestructorAxiom(dt, ctor, ctorFunction, tyvars, c_ty);
    }

    /*
          (forall x0 : C0, ..., xn : Cn, G : Ty, H : Heap •
              { $IsAlloc(C(G, x0,...,xn), T(G), H) }
              IsGoodHeap(H) ==>
                 ($IsAlloc(C(G, x0,...,xn), T(G), H) <==>
                  $IsAlloc[Box](x0, C0(G), H) && ... && $IsAlloc[Box](xn, Cn(G), H)));
        */
    private void AddIsAllocConstructorAxiom(DatatypeDecl dt, DatatypeCtor ctor, Bpl.Function ctorFunction,
      List<Expr> args, List<Variable> bvs, NAryExpr c_params, Expr c_ty) {
      var hVar = BplBoundVar("$h", Predef.HeapType, out var h);

      Bpl.Expr conj = Bpl.Expr.True;
      for (var i = 0; i < ctor.Formals.Count; i++) {
        var arg = ctor.Formals[i];
        conj = BplAnd(conj, MkIsAlloc(args[i], arg.Type, h));
      }

      {
        var isGoodHeap = FunctionCall(ctor.Origin, BuiltinFunction.IsGoodHeap, null, h);
        var c_alloc = MkIsAlloc(c_params, c_ty, h);
        bvs.Add(hVar);
        var constructorIsAllocAxiom = new Bpl.Axiom(ctor.Origin,
          BplForall(bvs, BplTrigger(c_alloc),
            BplImp(isGoodHeap, BplIff(c_alloc, conj))),
          "Constructor $IsAlloc");
        AddOtherDefinition(ctorFunction, constructorIsAllocAxiom);
      }
    }

    /// <summary>
    /// If no value of the datatype depends on allocation, then this axiom states the property
    /// for all datatype values. It can be used in place of one axiom per constructor.
    ///
    /// (forall d: DatatypeValue, T0,T1,...: Ty, H: Heap •
    ///   { $IsAlloc(d, T(T0,T1,...), H) }
    ///   IsGoodHeap(H) && $Is(d, T(T0,T1,...)) ==>
    ///     $IsAlloc(d, T(T0,T1,...), H))
    /// </summary>
    private void AddCommonIsAllocConstructorAxiom(DatatypeDecl dt) {

      MkIsPredicateForDatatype(dt, out var boundVariables, out var d, out var tyExpr, out var isPredicate);

      var hVar = BplBoundVar("$h", Predef.HeapType, out var h);
      var isGoodHeap = FunctionCall(dt.Origin, BuiltinFunction.IsGoodHeap, null, h);

      var isAlloc = MkIsAlloc(d, tyExpr, h);

      var body = BplImp(BplAnd(isGoodHeap, isPredicate), isAlloc);

      {
        var tr = BplTrigger(isAlloc);
        var ax = new Bpl.Axiom(dt.Origin, BplForall(Snoc(boundVariables, hVar), tr, body), "Datatype $IsAlloc");
        sink.AddTopLevelDeclaration(ax);
      }
    }

    /// <summary>
    /// Return list of variables
    ///     d: DatatypeValue, T0,T1,...: Ty  // in out-parameter "boundVariables"
    /// expression
    ///     d                                // in out-parameter "varExpression"
    /// expression
    ///     T(T0,T1,...)                     // in out-parameter "typeExpression"
    /// and predicate
    ///     $Is(d, T(T0,T1,...))             // in out-parameter "isPredicate"
    /// </summary>
    private void MkIsPredicateForDatatype(DatatypeDecl datatypeDecl, out List<Bpl.Variable> boundVariables,
      out Bpl.Expr varExpression, out Bpl.Expr typeExpression, out Bpl.Expr isPredicate) {
      var typeVariables = MkTyParamBinders(datatypeDecl.TypeArgs, out var typeExpressions);
      var dVar = BplBoundVar("d", Predef.DatatypeType, out varExpression);
      boundVariables = Snoc(typeVariables, dVar);
      typeExpression = ClassTyCon(datatypeDecl, typeExpressions);
      isPredicate = MkIs(varExpression, typeExpression);
    }

    /* (forall d : DatatypeType, G : Ty, H : Heap •
               { $IsAlloc[Box](Dtor(d), D(G), H) }
               IsGoodHeap(H) &&
               C?(d) &&
               (exists G' : Ty :: $IsAlloc(d, T(G,G'), H))
               ==>
                   $IsAlloc[Box](Dtor(d), D(G), H))
         */
    private void AddDestructorAxiom(DatatypeDecl dt, DatatypeCtor ctor, Bpl.Function ctorFunction, List<Variable> tyvars, Expr c_ty) {

      var hVar = BplBoundVar("$h", Predef.HeapType, out var h);
      for (int i = 0; i < ctor.Formals.Count; i++) {
        var arg = ctor.Formals[i];
        var dtor = GetReadonlyField(ctor.Destructors[i]);
        var dBv = BplBoundVar("d", Predef.DatatypeType, out var dId);
        var isGoodHeap = FunctionCall(ctor.Origin, BuiltinFunction.IsGoodHeap, null, h);
        Bpl.Expr dtq = FunctionCall(ctor.Origin, ctor.QueryField.FullSanitizedName, Bpl.Type.Bool, dId);
        var c_alloc = MkIsAlloc(dId, c_ty, h);
        var dtorD = FunctionCall(ctor.Origin, dtor.Name, TrType(arg.Type), dId);
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

        var bvs = new List<Bpl.Variable>();
        bvs.Add(dBv);
        bvs.AddRange(tyvarsG);
        bvs.Add(hVar);
        if (tyvarsGprime.Count != 0) {
          c_alloc = new Bpl.ExistsExpr(ctor.Origin, tyvarsGprime, BplTrigger(c_alloc), c_alloc);
        }

        var destructorAxiom = new Bpl.Axiom(ctor.Origin,
          BplForall(bvs, BplTrigger(d_alloc),
            BplImp(BplAnd(isGoodHeap, BplAnd(dtq, c_alloc)), d_alloc)),
          "Destructor $IsAlloc");
        AddOtherDefinition(ctorFunction, destructorAxiom);
      }
    }

    /*
        (forall x0 : C0, ..., xn : Cn, G : Ty •
          { $Is(C(x0,...,xn), T(G)) }
          $Is(C(x0,...,xn), T(G)) <==>
          $Is[Box](x0, C0(G)) && ... && $Is[Box](xn, Cn(G)));
      */
    private void AddsIsConstructorAxiom(DatatypeCtor ctor, Bpl.Function ctorFunction, List<Expr> args, List<Variable> bvs, NAryExpr c_params, Expr c_ty) {
      Bpl.Expr conj = Bpl.Expr.True;
      for (var i = 0; i < ctor.Formals.Count; i++) {
        var arg = ctor.Formals[i];
        conj = BplAnd(conj, MkIs(args[i], arg.Type));
      }

      var isCall = MkIs(c_params, c_ty);
      var constructorIsAxiom = new Bpl.Axiom(ctor.Origin,
        BplForall(bvs, BplTrigger(isCall), BplIff(isCall, conj)),
        "Constructor $Is");
      AddOtherDefinition(ctorFunction, constructorIsAxiom);
    }

    private Axiom CreateConstructorIdentifierAxiom(DatatypeCtor ctor, Expr c) {
      // Add:  axiom (forall params :: DatatypeCtorId(#dt.ctor(params)) == ##dt.ctor);
      CreateBoundVariables(ctor.Formals, out var bvs, out var args);
      var constructorCall = FunctionCall(ctor.Origin, ctor.FullName, Predef.DatatypeType, args);
      var lhs = FunctionCall(ctor.Origin, BuiltinFunction.DatatypeCtorId, null, constructorCall);
      Bpl.Expr q = Bpl.Expr.Eq(lhs, c);
      var trigger = BplTrigger(constructorCall);
      var axiom = new Bpl.Axiom(ctor.Origin, BplForall(bvs, trigger, q), "Constructor identifier");
      return axiom;
    }

    void AddWellformednessCheck(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Requires(sink != null && Predef != null);
      Contract.Requires(currentModule == null && codeContext == null && IsAllocContext == null && fuelContext == null);
      Contract.Ensures(currentModule == null && codeContext == null && IsAllocContext == null && fuelContext == null);

      proofDependencies.SetCurrentDefinition(MethodVerboseName(ctor.FullName, MethodTranslationKind.SpecWellformedness), ctor.EnclosingDatatype);

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
      var etran = new ExpressionTranslator(this, Predef, ctor.Origin, null);

      // parameters of the procedure
      List<Variable> inParams = MkTyParamFormals(GetTypeParams(ctor.EnclosingDatatype), true);
      foreach (var p in ctor.Formals) {
        Bpl.Type varType = TrType(p.Type);
        Bpl.Expr wh = GetWhereClause(p.Origin, new Bpl.IdentifierExpr(p.Origin, p.AssignUniqueName(ctor.IdGenerator), varType), p.Type, etran, NOALLOC);
        inParams.Add(new Bpl.Formal(p.Origin, new Bpl.TypedIdent(p.Origin, p.AssignUniqueName(ctor.IdGenerator), varType, wh), true));
      }

      // the procedure itself
      var req = new List<Bpl.Requires>();
      var heapVar = new Bpl.IdentifierExpr(ctor.Origin, "$Heap", false);
      var varlist = new List<Bpl.IdentifierExpr> { heapVar };
      var proc = new Bpl.Procedure(ctor.Origin, "CheckWellformed" + NameSeparator + ctor.FullName, new List<Bpl.TypeVariable>(),
        inParams, new List<Variable>(),
        false, req, varlist, new List<Bpl.Ensures>(), etran.TrAttributes(ctor.Attributes, null));
      AddVerboseNameAttribute(proc, ctor.FullName, MethodTranslationKind.SpecWellformedness);
      sink.AddTopLevelDeclaration(proc);

      var implInParams = Bpl.Formal.StripWhereClauses(inParams);
      var locals = new Variables();
      var builder = new BoogieStmtListBuilder(this, options, new BodyTranslationContext(false));
      builder.Add(new CommentCmd($"AddWellformednessCheck for datatype constructor {ctor}"));
      builder.AddCaptureState(ctor.Origin, false, "initial state");
      IsAllocContext = new IsAllocContext(options, true);

      DefineFrame(ctor.Origin, etran.ReadsFrame(ctor.Origin), new List<FrameExpression>(), builder, locals, null);

      // check well-formedness of each default-value expression
      foreach (var formal in ctor.Formals.Where(formal => formal.DefaultValue != null)) {
        var e = formal.DefaultValue;
        CheckWellformedWithResult(e, new WFOptions(null, true,
            false, true), locals, builder, etran, (returnBuilder, result) => {
              builder.Add(new Bpl.AssumeCmd(e.Origin, etran.CanCallAssumption(e)));
              CheckSubrange(result.Origin, etran.TrExpr(result), e.Type, formal.Type, e, returnBuilder);
            });
      }

      if (EmitImplementation(ctor.Attributes)) {
        // emit the impl only when there are proof obligations.
        QKeyValue kv = etran.TrAttributes(ctor.Attributes, null);
        var implBody = builder.Collect(ctor.Origin);
        AddImplementationWithAttributes(GetToken(ctor), proc, implInParams,
          new List<Variable>(), locals, implBody, kv);
      }

      Contract.Assert(currentModule == ctor.EnclosingDatatype.EnclosingModuleDefinition);
      Contract.Assert(codeContext == ctor.EnclosingDatatype);
      IsAllocContext = null;
      fuelContext = null;
      Reset();
    }
  }
}
