include "../Dafny/AST.dfy"

module {:extern "DCOMP"} DCOMP {
  import opened DAST

  // https://stackoverflow.com/questions/62722832/convert-numbers-to-strings
  type stringNat = s: string |
      |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
      forall i | 0 <= i < |s| :: s[i] in "0123456789"
    witness "1"

  function natToString(n: nat): stringNat {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

  class COMP {

    static method GenModule(mod: Module) returns (s: string) {
      var body := GenModuleBody(mod.body);
      s := "mod " + mod.name + " {\n" + body + "\n}";
    }

    static method GenModuleBody(body: seq<ModuleItem>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Module(m) => generated := GenModule(m);
          case Class(c) => generated := GenClass(c);
          case Newtype(n) => generated := "TODO";
        }

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method GenClass(c: Class) returns (s: string) {
      var implBody := GenClassImplBody(c.body);
      s := "pub struct " + c.name + " {\n" + "" +  "\n}" + "\n" + "impl " + c.name + " {\n" + implBody + "\n}";
    }

    static method GenClassImplBody(body: seq<ClassItem>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Method(m) => generated := GenMethod(m);
          case _ => generated := "TODO";
        }

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method GenMethod(m: Method) returns (s: string) {
      // var params := GenParams(m.params);
      var body := GenStmts(m.body);
      s := "pub fn " + m.name + "(" + "" + ") {\n" + body + "\n}\n";
    }

    static method GenStmts(body: seq<Statement>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Print(e) => {
            var printedExpr := GenExpr(e);
            generated := "print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(" + printedExpr + "));";
          }
          case DeclareVar(name, Ident(Ident(typ)), expression) => {
            var expr := GenExpr(expression);
            generated := "let mut " + name + ": " + typ + " = " + expr + ";";
          }
          case Assign(name, expression) => {
            var expr := GenExpr(expression);
            generated := name + " = " + expr + ";";
          }
          case _ => generated := "TODO";
        }

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method GenExpr(e: Expression) returns (s: string) {
      match e {
        case Literal(IntLiteral(i)) => {
          if (i < 0) {
            s := "-" + natToString(-i);
          } else {
            s := natToString(i);
          }
        }
        case Literal(DecLiteral(l)) => {
          // TODO(shadaj): handle unicode properly
          s := l;
        }
        case Literal(StringLiteral(l)) => {
          // TODO(shadaj): handle unicode properly
          s := "\"" + l + "\"";
        }
        case Ident(name) => {
          s := name;
        }
        case DatatypeValue(values) => {
          var i := 0;
          s := "(";
          while i < |values| {
            if i > 0 {
              s := s + ", ";
            }
            var recursiveGen := GenExpr(values[i]);
            s := s + recursiveGen;
            i := i + 1;
          }
          s := s + ")";
        }
        case BinOp(op, l, r) => {
          var left := GenExpr(l);
          var right := GenExpr(r);
          s := "(" + left + " " + op + " " + right + ")";
        }
      }
    }

    static method Compile(p: seq<TopLevel>, runtime: string) returns (s: string) {
      s := "#![allow(warnings)]\n";
      s := s + "mod dafny_runtime {\n" + runtime + "\n}\n";

      var i := 0;
      while i < |p| {
        var generated: string;
        match p[i] {
          case Module(m) => generated := GenModule(m);
          case Other(_, _) => generated := "TODO";
        }

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "fn main() {\n";
      var i := 0;
      while i < |fullName| {
        if i > 0 {
          s := s + "::";
        }
        s := s + fullName[i];
        i := i + 1;
      }
      s := s + "();\n}";
    }

  }

}