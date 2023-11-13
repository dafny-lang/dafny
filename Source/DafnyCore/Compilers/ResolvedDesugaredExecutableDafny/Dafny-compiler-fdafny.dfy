module {:extern "ResolvedDesugaredExecutableDafnyPlugin"} ResolvedDesugaredExecutableDafnyPlugin {
  import opened DAST
  import PrettyPrinter
  import UnsupportedFeature
  import DAM

  class COMP {

    static method Compile(p: seq<Module>) returns (s: string) {
      var st := EmitDAM(p);
      print st;
      print "\n";

      s := PrettyPrinter.PrettyPrint(p);
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "";
    }

    // Modules are just classes, really
    static method EmitModule(m: Module) returns (s: DAM.Stmt) {
      s := EmitClass(Class(m.name, "", [], [], [], []));
    }

    // TODO: Classes/traits are implemented as fixed points of records: Fix(\this. {field1 = ..., fieldn = ...})
    // Methods are just functions
    static method EmitClass(c: Class) returns (s: DAM.Stmt) {
      var fields := map[];
      // TODO: normal fields turn into references
      for i := 0 to |c.body| {
        match c.body[i]
        case Method(m) =>
          var meth := EmitMethod(m);
          fields := fields[m.name := meth];
      }
      s := DAM.Record(fields);
    }

    static method EmitMethod(m: Method) returns (s: DAM.Stmt) {
      // TODO this is actually a lambda
      s := EmitBlock(m.body);
    }

    static method EmitExpr(e: Expression) returns (s: DAM.Stmt) {
      match e
      case Ident(v) => s := DAM.Pure(DAM.Var(v));
      case This()   => s := DAM.Pure(DAM.Var("this"));
      case Ite(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitExpr(thn);
        var els  := EmitExpr(els);
        s := DAM.Stmt.Bind(cond, "_guard", DAM.Ite(DAM.Var("_guard"), thn, els));
      case _ => s := DAM.Pure(DAM.Expr.Bool(true));
    }

    static method EmitStmt(s: Statement) returns (st: DAM.Stmt) {
      match s
      case If(cond, thn, els) =>
        var cond := EmitExpr(cond);
        var thn  := EmitBlock(thn);
        var els  := EmitBlock(els);
        st := DAM.Stmt.Bind(cond, "_guard", DAM.Ite(DAM.Var("_guard"), thn, els));
      case _ => st := DAM.Pure(DAM.Expr.Bool(true));
    }

    static method EmitBlock(b: seq<Statement>) returns (s: DAM.Stmt) {
      s := DAM.Pure(DAM.Expr.Bool(true));
      if (|b| > 0) {
        var first := EmitStmt(b[0]);
        var rest  := EmitBlock(b[1..]);
        s := DAM.Stmt.Bind(first, "_", rest);
      }
    }
  }
}
