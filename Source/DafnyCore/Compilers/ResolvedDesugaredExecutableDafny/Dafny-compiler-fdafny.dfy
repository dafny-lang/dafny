module {:extern "ResolvedDesugaredExecutableDafnyPlugin"} ResolvedDesugaredExecutableDafnyPlugin {
  import opened DAST
  import PrettyPrinter
  import UnsupportedFeature
  import DS = DAM.Syntax

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) {
      //print(p);
      /*for i := 0 to |p| {
        var m := p[i];
        if m.name == "__default" {
          var m := EmitModule(p[i]);
        }
        //print p[i], "\n\n";
        
        //var t := EmitModuleType(p[i]);
        print m;
        print "\n\n";
        //print t;
        print "\n\n";
      }*/
      
      s := PrettyPrinter.PrettyPrint(p);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "";
    }

    static method PolarizePos(t: Type) returns (p: DS.Pos) {
      match t
      case Primitive(Int)  =>
        return DS.Pos.Int;
      case Primitive(Bool) =>
        return DS.Pos.Bool;
      case _ => UnsupportedFeature.Throw(); p := DS.Pos.Unit;
    }

    /*static method EmitModuleType(m: Module) returns (t: DS.Neg) {
      var members := map[];
      for i := 0 to |m.body| {
        match m.body[i]
        case Module(m) =>
          var tm := EmitModuleType(m);
          members := members[m.name := tm];
        case Class(c) =>
          var tc := EmitClassType(c);
          members := members[c.name := tc];
        case _ => continue;
      }
      t := DS.Neg.Record(members);
    }*/

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
      s := DS.LetCS("return", body);

      // Out parameters turn into input references
      match m.outVars
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
      /*case Literal(IntLiteral(i)) =>
        return DS.Pure(DS.Expr.Int(i));*/
      case Ident(v) =>
        return DS.Pure(DS.Var(v));
      case This()   =>
        return DS.Pure(DS.Var("this"));
      
      case Ite(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitExpr(thn);
        var els  := EmitExpr(els);
        s := DS.Stmt.Bind(cond, "if", DS.Ite(DS.Var("if"), thn, els));
      
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
          return DS.Throw(DS.Var(lab), DS.Skip());
        case None =>
          UnsupportedFeature.Throw();
          return DS.Skip();
      }

      case EarlyReturn() =>
        return DS.Throw(DS.Var("return"), DS.Skip());
      
      case Return(expr) =>
        var ret := EmitExpr(expr);
        return DS.Throw(DS.Var("return"), ret);

      case Labeled(lab, stmt) =>
        // No problem, multiset ordering
        assume {:axiom} stmt + next < next;
        var block := EmitBlock(stmt + next);
        return DS.LetCS(lab, block);
      
      case DeclareVar(var_, _, Some(init)) =>
        var init := EmitExpr(init);
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
        
        match outs
        // Simplifying assumption: out parameters were already initialized
        case Some(outs) =>
          for i := 0 to |outs| {
            /*var arg := EmitExpr(InitializationValue(Primitive(Bool)));
            st :=
              DS.Stmt.Bind(arg, "var",
                DS.Stmt.New(DS.Var("var"), "var", DS.Stmt.Call(st, DS.Var("var"))));*/
            st := DS.Stmt.Call(st, DS.Var(outs[i].id));
          }
        case None => {}
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
  }
}
