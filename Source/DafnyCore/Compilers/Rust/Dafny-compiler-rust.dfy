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
          case Newtype(n) => generated := GenNewtype(n);
          case Datatype(d) => generated := GenDatatype(d);
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

    static method GenNewtype(c: Newtype) returns (s: string) {
      var underlyingType := GenType(c.base);
      s := "pub type " + c.name + " =" + underlyingType +  ";\n";
    }

    static method GenDatatype(c: Datatype) returns (s: string) {
      var ctors := "";
      var i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorBody := ctor.name + " { ";
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          var formalType := GenType(formal.typ);
          ctorBody := ctorBody + formal.name + ": " + formalType + ", ";
          j := j + 1;
        }

        ctorBody := ctorBody + "}";

        ctors := ctors + ctorBody + ",\n";
        i := i + 1;
      }

      var implBody := GenClassImplBody(c.body);
      var enumBody := "pub enum " + c.name + " {\n" + ctors +  "\n}" + "\n" + "impl " + c.name + " {\n" + implBody + "\n}";

      var printImpl := "impl ::dafny_runtime::DafnyPrint for " + c.name + " {\n" + "fn fmt_print(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {\n" + "match self {\n";
      i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := ctor.name + " { ";
        var printRhs := "write!(f, \"" + c.name + "." + ctor.name + (if ctor.hasAnyArgs then "(\")?;" else "\")?;");

        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          ctorMatch := ctorMatch + formal.name + ", ";

          if (j > 0) {
            printRhs := printRhs + "\nwrite!(f, \", \")?;";
          }
          printRhs := printRhs + "\n::dafny_runtime::DafnyPrint::fmt_print(" + formal.name + ", f)?;";

          j := j + 1;
        }

        ctorMatch := ctorMatch + "}";

        if (ctor.hasAnyArgs) {
          printRhs := printRhs + "\nwrite!(f, \")\")?;";
        }

        printRhs := printRhs + "\nOk(())";

        printImpl := printImpl + c.name + "::" + ctorMatch + " => {\n" + printRhs + "\n}\n";
        i := i + 1;
      }

      printImpl := printImpl + "}\n}\n}\n";

      s := enumBody + "\n" + printImpl;
    }

    static method GenType(c: Type) returns (s: string) {
      match c {
        case Path(p) => {
          s := "super::";
          var i := 0;
          while i < |p| {
            if i > 0 {
              s := s + "::";
            }

            s := s + p[i].id;

            i := i + 1;
          }
        }
        case TypeArg(Ident(name)) => s := name;
        case Passthrough(v) => s := v;
      }
    }

    static method GenClassImplBody(body: seq<ClassItem>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Method(m) => generated := GenMethod(m);
          case Field(f) => generated := "TODO";
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
      s := "pub fn " + m.name;

      if (|m.typeArgs| > 0) {
        s := s + "<";

        var i := 0;
        while i < |m.typeArgs| {
          if i > 0 {
            s := s + ", ";
          }

          var typeString := GenType(m.typeArgs[i]);
          s := s + typeString;

          i := i + 1;
        }

        s := s + ">";
      }

      s := s + "(" + "" + ") {\n" + body + "\n}\n";
    }

    static method GenStmts(stmts: seq<Statement>) returns (generated: string) {
      generated := "";
      var i := 0;
      while i < |stmts| {
        var stmt := stmts[i];
        var stmtString := GenStmt(stmt);

        if i > 0 {
          generated := generated + "\n";
        }

        generated := generated + stmtString;
        i := i + 1;
      }
    }

    static method GenStmt(stmt: Statement) returns (generated: string) {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var expr := GenExpr(expression);
          var typeString := GenType(typ);
          generated := "let mut " + name + ": " + typeString + " = " + expr + ";";
        }
        case DeclareVar(name, typ, None) => {
          var typeString := GenType(typ);
          generated := "let mut " + name + ": " + typeString + ";";
        }
        case Assign(name, expression) => {
          var expr := GenExpr(expression);
          generated := name + " = " + expr + ";";
        }
        case If(cond, thn, els) => {
          var condString := GenExpr(cond);
          var thnString := GenStmts(thn);
          var elsString := GenStmts(els);
          generated := "if " + condString + " {\n" + thnString + "\n} else {\n" + elsString + "\n}";
        }
        case Call(enclosing, name, args) => {
          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr := GenExpr(args[i]);
            argString := argString + argExpr;

            i := i + 1;
          }

          var enclosingString := "";
          match enclosing {
            case Some(e) => {
              enclosingString := GenType(e);
              enclosingString := enclosingString + "::";
            }
            case None => {
              enclosingString := "";
            }
          }

          generated := enclosingString + name + "(" + argString + ");";
        }
        case Return(expr) => {
          var exprString := GenExpr(expr);
          generated := "return " + exprString + ";";
        }
        case Print(e) => {
          var printedExpr := GenExpr(e);
          generated := "print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(" + printedExpr + "));";
        }
        case Todo(reason) => {
          generated := "todo!(\"" + reason + "\");";
        }
      }
    }

    static method GenExpr(e: Expression) returns (s: string) {
      match e {
        case Literal(BoolLiteral(false)) => {
          s := "false";
        }
        case Literal(BoolLiteral(true)) => {
          s := "true";
        }
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
        case InitializationValue(typ) => {
          s := "std::default::Default::default()";
        }
        case DatatypeValue(typ, variant, values) => {
          s := GenType(typ);
          s := s + "::";
          s := s + variant;

          var i := 0;
          s := s + " {";
          while i < |values| {
            var (name, value) := values[i];
            if i > 0 {
              s := s + ", ";
            }
            var recursiveGen := GenExpr(value);
            s := s + name + ": " + recursiveGen;
            i := i + 1;
          }
          s := s + " }";
        }
        case BinOp(op, l, r) => {
          var left := GenExpr(l);
          var right := GenExpr(r);
          s := "(" + left + " " + op + " " + right + ")";
        }
        case Todo(reason) => {
          s := "todo!(\"" + reason + "\")";
        }
      }
    }

    static method Compile(p: seq<Module>, runtime: string) returns (s: string) {
      s := "#![allow(warnings)]\n";
      s := s + "mod dafny_runtime {\n" + runtime + "\n}\n";

      var i := 0;
      while i < |p| {
        var generated: string;
        generated := GenModule(p[i]);

        if i > 0 {
          s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static method EmitCallToMain(fullName: seq<string>) returns (s: string) {
      s := "\nfn main() {\n";
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
