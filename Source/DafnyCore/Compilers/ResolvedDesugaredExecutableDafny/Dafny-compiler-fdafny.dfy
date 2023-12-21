module {:extern "ResolvedDesugaredExecutableDafnyPlugin"} ResolvedDesugaredExecutableDafnyPlugin {
  import opened DAST
  import PrettyPrinter
  import UnsupportedFeature
  import DAM
  import DS = DAM.Syntax

  //import Std.Strings

  class COMP {
    static method PolarizePos(t: Type) returns (p: DS.Pos) {
      match t
      case Primitive(Int)  =>
        return DS.Pos.Int;
      case Primitive(Bool) =>
        return DS.Pos.Bool;
      case _ => UnsupportedFeature.Throw(); p := DS.Pos.Unit;
    }

    /*static method EmitClassType(c: Class) returns (t: DS.Neg) {
      var members := map[];
      for i := 0 to |c.body| {
        match c.body[i]
        case Method(m) =>
          var tm := EmitMethodType(m);
          members := members[m.name := tm];
      }
      t := DS.Neg.Record(members);
    }*/

    /*static method EmitMethodType(m: Method) returns (t: DS.Neg) {
      t := DS.Command();
      for i := 0 to |m.params| {
        match m.params[|m.params| - i - 1]
        case Formal(_, dom) =>
          var dom := PolarizePos(dom);
          t := DS.Neg.Function(dom, t);
      }
      // TODO out parameters
    }*/

    // Modules are just records
    static method EmitModule(m: Module) returns (s: DS.Stmt) {
      var members := map[];
      for i := 0 to |m.body| {
        match m.body[i]
        case Module(m) =>
          var mod := EmitModule(m);
          members := members[m.name := mod];
        case Class(c) =>
          var cls := EmitClass(c);
          members := members[c.name := cls];
        // Types don't exist at the level of statements
        case _ => continue;
      }
      s := DS.Stmt.Record(members);
    }

    // TODO: Classes are fixed points of records: rec(\this. {field1 = ..., fieldn = ...})
    // Methods are just functions
    static method EmitClass(c: Class) returns (s: DS.Stmt) {
      var fields := map[];
      // TODO: normal fields turn into references
      /*for i := 0 to |c.fields| {
        match c.fields[i]
        case Field(name, Some(init)) =>
          fields.fields
        case _ => UnsupportedFeature.Throw(); s := DS.Skip();
      }*/
      for i := 0 to |c.body| {
        match c.body[i]
        case Method(m) =>
          var meth := EmitMethod(m);
          fields := fields[m.name := meth];
      }
      s := DS.Stmt.Record(fields);
    }

    static method EmitMethod(m: Method) returns (s: DS.Stmt) {
      // Label a point for early returns
      var body := EmitBlock(m.body);
      s := DS.LetCS("return", DS.Command(), body);

      // Out parameters turn into input references
      match m.outVars {
      case Some(outs) => {
        for i := 0 to |outs| {
          match outs[|outs| - i - 1]
          case Ident(ret) =>
            expect i < |m.outTypes|;
            var cod := PolarizePos(m.outTypes[i]);
            s := DS.Func(ret, DS.Pos.Ref(cod), s);
        }
      }
      case None => {}
      }
      
      // In parameters also turn into input references
      for i := 0 to |m.params| {
        match m.params[|m.params| - i - 1]
        case Formal(arg, dom) =>
          var dom := PolarizePos(dom);
          s := DS.Func(arg, DS.Pos.Ref(dom), s);
      }
      // Expectation: body returns DS.Command()
    }

    // Dafny expressions are actually DAM statements, since they are sensitive to evaluation order
    static method EmitExpr(e: Expression) returns (s: DS.Stmt) {
      match e
      case Literal(BoolLiteral(b)) =>
        return DS.Pure(DS.Expr.Bool(b));
      
      case Literal(IntLiteral(i, _)) =>
        return DS.Pure(DS.Expr.Int(0));
      
      case Companion(path) =>
        expect |path| > 0;
        s := DS.Force(DS.Var(path[0].id));
        for i := 1 to |path| {
          s := DS.Stmt.Select(s, path[i].id);
        }
      
      case Call(obj, Ident(meth), _, args) =>
        s := EmitExpr(obj);
        s := DS.Stmt.Select(s, meth);
        for i := 0 to |args| {
          var arg := EmitExpr(args[i]);
          s :=
            DS.Stmt.Bind(arg, "var",
              DS.Stmt.New(DS.Var("var"), "var", DS.Stmt.Call(s, DS.Var("var"))));
        }

      case Ident(v) =>
        return DS.Read(DS.Var(v), "var", DS.Pure(DS.Var("var")));
      
      case This()   =>
        return DS.Pure(DS.Var("this"));
      
      case Ite(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitExpr(thn);
        var els  := EmitExpr(els);
        return DS.Stmt.Bind(cond, "if", DS.Ite(DS.Var("if"), thn, els));
      
      case BinOp(op, lhs, rhs) =>
        var lhs := EmitExpr(lhs);
        var rhs := EmitExpr(rhs);
        var lvar := DS.Var("var_lhs");
        var rvar := DS.Var("var_rhs");
        var end;
        match op {
          case Passthrough("+") => end := DS.Pure(DS.Plus(lvar, rvar));
          case Passthrough("<") => end := DS.Pure(DS.LT(lvar, rvar));
          case _                => UnsupportedFeature.Throw(); end := DS.Skip();
        }
        return DS.Stmt.Bind(lhs, "var_lhs", DS.Stmt.Bind(rhs, "var_rhs", end));
      
      case InitializationValue(Primitive(Int)) =>
        return DS.Pure(DS.Expr.Int(0));
      
      case InitializationValue(Primitive(Bool)) =>
        return DS.Pure(DS.Expr.Bool(false));
      
      case _ => UnsupportedFeature.Throw(); s := DS.Skip();
    }

    // Terminates by multiset ordering on block
    static method EmitBlock(block: seq<Statement>) returns (st: DS.Stmt) {
      if (|block| <= 0) { return DS.Skip(); }
      var next := block[1..];
      match block[0]

      case If(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitBlock(thn);
        var els  := EmitBlock(els);
        var next := EmitBlock(next);
        st := DS.Then(DS.Stmt.Bind(cond, "if", DS.Ite(DS.Var("if"), thn, els)), next);
      
      case While(guard, body) =>
        var guard := EmitExpr(guard);
        var body := EmitBlock(body);
        var next := EmitBlock(next);
        st := DS.While(guard, body, next);
      
      // Breaks, returns, and halts drop the rest of the block
      case Break(lab) => {
        match lab
        case Some(lab) =>
          return DS.Throw(DS.Var(lab), DS.Command(), DS.Skip());
        case None =>
          UnsupportedFeature.Throw();
          return DS.Skip();
      }

      case EarlyReturn() =>
        return DS.Throw(DS.Var("return"), DS.Command(), DS.Skip());
      
      case Return(expr) =>
        var ret := EmitExpr(expr);
        return DS.Throw(DS.Var("return"), DS.Command(), ret);

      case Labeled(lab, stmt) =>
        // No problem, multiset ordering
        assume {:axiom} stmt + next < next;
        var block := EmitBlock(stmt + next);
        return DS.LetCS(lab, DS.Command(), block);
      
      case DeclareVar(var_, ty, init) =>
        var init := EmitRHS(ty, init);
        var next := EmitBlock(next);
        return DS.Stmt.Bind(init, "var", DS.Stmt.New(DS.Expr.Var("var"), var_, next));
      
      case Assign(lhs, rhs) => {
        var rhs := EmitExpr(rhs);
        var next := EmitBlock(next);
        match lhs
        case Ident(Ident(v)) =>
          return DS.Stmt.Bind(rhs, "var", DS.Stmt.Write(DS.Expr.Var(v), DS.Expr.Var("var"), next));
        case _ =>
          UnsupportedFeature.Throw();
          return DS.Skip();
      }
      
      case Call(obj, meth, _, args, outs) => {
        var obj := EmitExpr(obj);
        st := DS.Stmt.Select(obj, meth);
        for i := 0 to |args| {
          var arg := EmitExpr(args[i]);
          st :=
            DS.Stmt.Bind(arg, "var",
              DS.Stmt.New(DS.Var("var"), "var", DS.Stmt.Call(st, DS.Var("var"))));
        }
        
        // Assumption about SinglePassCompiler: out parameters were already initialized
        match outs {
          case Some(outs) =>
            for i := 0 to |outs| {
              st := DS.Stmt.Call(st, DS.Var(outs[i].id));
            }
          case None => {}
        }

        var next := EmitBlock(next);
        st := DS.Then(st, next);
      }
      
      case Print(expr) =>
        var arg := EmitExpr(expr);
        var next := EmitBlock(next);
        return DS.Stmt.Bind(arg, "var", DS.Print(DS.Var("var"), next));
      
      // TailRecursive(body) | JumpTailCallStart() | Halt | Foreach
      case _ =>
        UnsupportedFeature.Throw();
        return DS.Skip();
    }

    static method EmitRHS(type_: Type, rhs: Optional<Expression>) returns (out: DS.Stmt) {
      match (type_, rhs)
      case (_, Some(init))      => out := EmitExpr(init);
      case (Primitive(Int), _)  => out := DS.Pure(DS.Expr.Int(0));
      case (Primitive(Bool), _) => out := DS.Pure(DS.Expr.Bool(false));
      case _                    => UnsupportedFeature.Throw(); out := DS.Skip();
    }

    static method Compile(p: seq<Module>) returns (s: string) decreases * {
      s := "";

      // Forward pass to compile modules in dependency order
      var modules := [];
      var bindings := map[];
      for i := 0 to |p| {
        var name := p[i].name;
        print "Lowering module ", name, " into the DAM instruction set...\n";
        var m      := EmitModule(p[i]);
        var mthunk := DS.Expr.Thunk(m);
        var mtype  := DAM.Statics.SynthExpr(bindings, mthunk);
        if (mtype.None?) {
          print "Unable to synthesize type for module ", name, "!\n";
          return;
        }
        print "Successfully synthesized type for module ", name, "\n";
        modules := modules + [(name, mthunk, mtype.Extract())];
        bindings := bindings[name := mtype.Extract()];
      }

      // Backward pass to emit call to main
      var body := DS.Stmt.Select(DS.Stmt.Select(DS.Force(DS.Var("_module")), "__default"), "Main");
      for i := 0 to |modules| {
        var (name, mod, modtype) := modules[|modules| - i - 1];
        body := DS.Let(mod, name, modtype, body);
      }

      // Sanity check
      var end := DAM.Statics.SynthStmt(map[], body);
      expect end.Some?;

      // Execute main!
      print "Tracing execution of _module.__default.Main() below\n";
      DAM.Dynamics.Interpret(body, traced := true);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "";
    }
  }
}
