module {:extern "ResolvedDesugaredExecutableDafnyPlugin"} ResolvedDesugaredExecutableDafnyPlugin {
  import opened DAST
  import PrettyPrinter
  import UnsupportedFeature
  import DAM

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) decreases * {
      //print(p);
      for i := 0 to |p| {
        var m := EmitModule(p[i]);
        var t := EmitModuleType(p[i]);
        print m;
        print "\n\n";
        print t;
        print "\n\n";
      }

      s := PrettyPrinter.PrettyPrint(p);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "";
    }

    static method PolarizePos(t: Type) returns (p: DAM.Pos) {
      match t
      case Primitive(Int)  => p := DAM.Pos.Int;
      case Primitive(Bool) => p := DAM.Pos.Bool;
      case _ => UnsupportedFeature.Throw(); p := DAM.Pos.Unit;
    }

    static method EmitModuleType(m: Module) returns (t: DAM.Neg) {
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
      t := DAM.Neg.Record(members);
    }

    static method EmitClassType(c: Class) returns (t: DAM.Neg) {
      var members := map[];
      for i := 0 to |c.body| {
        match c.body[i]
        case Method(m) =>
          var tm := EmitMethodType(m);
          members := members[m.name := tm];
      }
      t := DAM.Neg.Record(members);
    }

    static method EmitMethodType(m: Method) returns (t: DAM.Neg) {
      t := DAM.Neg.Value(DAM.Pos.Unit);
      for i := 0 to |m.params| {
        match m.params[|m.params| - i - 1]
        case Formal(_, dom) =>
          var dom := PolarizePos(dom);
          t := DAM.Neg.Function(dom, t);
      }
      // TODO out parameters
    }

    // Modules are just records
    static method EmitModule(m: Module) returns (s: DAM.Stmt) decreases * {
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
      s := DAM.Stmt.Record(members);
    }

    // TODO: Classes are fixed points of records: Fix(\this. {field1 = ..., fieldn = ...})
    // Methods are just functions
    static method EmitClass(c: Class) returns (s: DAM.Stmt) decreases * {
      var fields := map[];
      // TODO: normal fields turn into references
      /*for i := 0 to |c.fields| {
        match c.fields[i]
        case Field(name, defaultValue) =>
          fields := fields[name := DAM.Expr.Ref(new DAM.Ptr())];
        case _ => UnsupportedFeature.Throw(); s := DAM.Skip();
      }*/
      for i := 0 to |c.body| {
        match c.body[i]
        case Method(m) =>
          var meth := EmitMethod(m);
          fields := fields[m.name := meth];
      }
      s := DAM.Stmt.Record(fields);
    }

    static method EmitMethod(m: Method) returns (s: DAM.Stmt) decreases * {
      // Label a point for early returns
      var body := EmitBlock(m.body);
      s := DAM.LetCS("return", body);
      // Out parameters turn into input references
      /*for i := 0 to |m.outVars| {
        match m.outVars
        case Ident(Ident(v)) =>
        
      }*/
      // In parameters...also turn into input references
      for i := 0 to |m.params| {
        match m.params[|m.params| - i - 1]
        case Formal(arg, dom) =>
          var dom := PolarizePos(dom);
          s := DAM.Func(arg, dom, s);
      }
      // Annotate the entire function to allow it to appear in a redex
    }

    // Dafny expressions are actually DAM statements, since they are sensitive to evaluation order
    static method EmitExpr(e: Expression) returns (s: DAM.Stmt) {
      match e
      case Ident(v) => s := DAM.Pure(DAM.Var(v));
      case This()   => s := DAM.Pure(DAM.Var("this"));
      case Ite(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitExpr(thn);
        var els  := EmitExpr(els);
        s := DAM.Stmt.Bind(cond, "if", DAM.Ite(DAM.Var("if"), thn, els));
      case _ => UnsupportedFeature.Throw(); s := DAM.Skip();
    }

    // Terminates by multiset ordering on block
    static method EmitBlock(block: seq<Statement>) returns (st: DAM.Stmt) decreases * {
      if (|block| <= 0) { return DAM.Skip(); }
      var next := block[1..];
      match block[0]

      case If(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitBlock(thn);
        var els  := EmitBlock(els);
        var next := EmitBlock(next);
        st := DAM.Then(DAM.Stmt.Bind(cond, "if", DAM.Ite(DAM.Var("if"), thn, els)), next);
      
      case While(guard, body) =>
        var guard := EmitExpr(guard);
        var body := EmitBlock(body);
        var next := EmitBlock(next);
        st := DAM.While(guard, body, next);
      
      // Breaks, returns, and halts drop the rest of the block
      case Break(lab) => {
        match lab
        case Some(lab) =>
          st := DAM.Throw(DAM.Var(lab), DAM.Skip());
        case None => UnsupportedFeature.Throw(); st := DAM.Skip();
      }

      case EarlyReturn() =>
        st := DAM.Throw(DAM.Var("return"), DAM.Skip());
      
      case Return(expr) =>
        var ret := EmitExpr(expr);
        st := DAM.Throw(DAM.Var("return"), ret);

      case Labeled(lab, stmt) =>
        var block := EmitBlock(stmt + next);
        st := DAM.LetCS(lab, block);
      
      case Assign(lhs, rhs) =>
        var lhs := EmitLval(lhs);
        var rhs := EmitExpr(rhs);
        var next := EmitBlock(next);
        st := DAM.Stmt.Bind(lhs, "var",
              DAM.Stmt.Bind(rhs, "rhs",
                DAM.Write(DAM.Var("rhs"), DAM.Var("var"), next)));
      
      /*case Call(obj, meth, _, args, outs) =>
        var obj := EmitExpr(obj);
        s := DAM.Select(obj, meth);
        for i := 0 to |args| {
          var arg := EmitExpr(args[i]);
          s := DAM.Stmt.Bind(arg, "arg" + i,
            DAM.Stmt.Call(s, DAM.Var("arg" + i)));
        } */
      
      case Print(expr) =>
        var arg := EmitExpr(expr);
        var next := EmitBlock(next);
        st := DAM.Stmt.Bind(arg, "var", DAM.Print(DAM.Var("var"), next));
      
      case _ => UnsupportedFeature.Throw(); st := DAM.Skip();
    }

    static method EmitLval(lv: AssignLhs) returns (s: DAM.Stmt) {
      match lv
      case Ident(Ident(v)) => s := DAM.Pure(DAM.Var(v));
      case _        => s := DAM.Skip();
    }
  }
}
