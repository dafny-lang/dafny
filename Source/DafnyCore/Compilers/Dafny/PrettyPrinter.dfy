module {:extern "D2DPrettyPrinter"} PrettyPrinter {

  import DAST
  import UnsupportedFeature

  method PrettyPrint(d: seq<DAST.Module>) returns (s: string) {
    s := "";
    for i := 0 to |d| {
      var s' := PModule(d[i]);
      s := s + s';
    }
    print s;
  }

  method PModule(mod: DAST.Module) returns (s: string) {
    s := "module " + mod.name + " {\n";
    for i := 0 to |mod.body| {
      
      match mod.body[i] {
      case Module(m) => var s' := PModule(m); s := s + s';
      case Class(c) => var s' := PClass(c); s := s + s';
      case Trait(c) => s := "";
      case Newtype(n) => s := "";
      case Datatype(d) => s := "";
      }
    }
    s := s + "}\n";
  }

  method PClass(c: DAST.Class) returns (s: string) {
    s := "class " + c.name + " {\n";
    for i := 0 to |c.body| {
      match c.body[i]
      case Method(m) => var s' := PMethod(m); s := s + s' + "\n";
    }
    s := s + "}\n";
  }

  method PMethod(meth: DAST.Method) returns (s: string) {
    s := "method " + meth.name;
    var s' := PFormals(meth.params, meth.typeParams);
    s := s + s';
    s' := PBlock(meth.body);
    s := s + s';
  }

  method PFormals(names: seq<DAST.Formal>, types: seq<DAST.Type>) returns (s: string) {
    s := "(";
    for i := 0 to |names| {
      s := s + names[i].name + ": _,";
    }
    s := s + ")";
  }

  method PBlock(stmt: seq<DAST.Statement>) returns (s: string) {
    s := "";
    if (|stmt| > 0) { s := "{\n"; }
    for i := 0 to |stmt| {
      var s' := PStatement(stmt[i]);
      s := s + s' + ";\n";
    }
    if (|stmt| > 0) { s := s + "}"; }
  }

  method PStatement(st: DAST.Statement) returns (s: string) {
    match st
    case Print(e) => var s' := PExpression(e); s := "print " + s';
    case EarlyReturn() => s := "return";
    case _ => s := "NYI";
  }

  method PExpression(e: DAST.Expression) returns (s: string) {
    match e
    case Literal(l) => s := PLiteral(l);
    case _ => s := "NYI";
  }

  method PLiteral(l: DAST.Literal) returns (s: string) {
    match l
    case BoolLiteral(b) => s := if b then "true" else "false";
    case IntLiteral(i, _) => s := i;
    case StringLiteral(s') => s := "\"" + s' + "\"";
    case CharLiteral(c) => s := [c];
    case DecLiteral(l, r, _) => s := l + "." + r;
    case Null(_) => s := "null";
  }
}
