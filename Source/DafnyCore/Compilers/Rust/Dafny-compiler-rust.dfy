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
      s := "mod r#" + mod.name + " {\n" + body + "\n}";
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
      s := "pub struct r#" + c.name + " {\n" + "" +  "\n}" + "\n" + "impl r#" + c.name + " {\n" + implBody + "\n}";
    }

    static method GenNewtype(c: Newtype) returns (s: string) {
      var underlyingType := GenType(c.base);
      s := "pub type r#" + c.name + " =" + underlyingType +  ";\n";
    }

    static method GenDatatype(c: Datatype) returns (s: string) {
      var ctors := "";
      var i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorBody := "r#" + ctor.name + " { ";
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          var formalType := GenType(formal.typ);
          ctorBody := ctorBody + "r#" + formal.name + ": " + formalType + ", ";
          j := j + 1;
        }

        ctorBody := ctorBody + "}";

        ctors := ctors + ctorBody + ",\n";
        i := i + 1;
      }

      var implBody := GenClassImplBody(c.body);
      i := 0;
      var emittedFields: set<string> := {};
      while i < |c.ctors| {
        // we know that across all ctors, each any fields with the same name have the same type
        // so we want to emit methods for each field that pull the appropriate value given
        // the current variant (and panic if we have a variant with no such field)
        var ctor := c.ctors[i];
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          if !(formal.name in emittedFields) {
            emittedFields := emittedFields + {formal.name};

            var formalType := GenType(formal.typ);
            var methodBody := "match self {\n";
            var k := 0;
            while k < |c.ctors| {
              var ctor2 := c.ctors[k];
              var ctorMatch := "r#" + c.name + "::" + "r#" + ctor2.name + " { ";
              var l := 0;
              var hasMatchingField := false;
              while l < |ctor2.args| {
                var formal2 := ctor2.args[l];
                if formal.name == formal2.name {
                  hasMatchingField := true;
                }
                ctorMatch := ctorMatch + "r#" + formal2.name + ", ";
                l := l + 1;
              }

              if hasMatchingField {
                ctorMatch := ctorMatch + "} => " + formal.name + ",\n";
              } else {
                ctorMatch := ctorMatch + "} => panic!(\"field does not exist on this variant\"),\n";
              }
              methodBody := methodBody + ctorMatch;
              k := k + 1;
            }

            methodBody := methodBody + "}\n";

            implBody := implBody + "pub fn " + formal.name + "(&self) -> &" + formalType + " {\n" + methodBody + "}\n";
          }
          j := j + 1;
        }

        i := i + 1;
      }

      var enumBody := "#[derive(Clone, PartialEq)]\npub enum r#" + c.name + " {\n" + ctors +  "\n}" + "\n" + "impl r#" + c.name + " {\n" + implBody + "\n}";

      var printImpl := "impl ::dafny_runtime::DafnyPrint for r#" + c.name + " {\n" + "fn fmt_print(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {\n" + "match self {\n";
      i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := "r#" + ctor.name + " { ";

        var modulePrefix := if c.enclosingModule.id == "_module" then "" else c.enclosingModule.id + ".";
        var printRhs := "write!(f, \"" + modulePrefix + c.name + "." + ctor.name + (if ctor.hasAnyArgs then "(\")?;" else "\")?;");

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

        printImpl := printImpl + "r#" + c.name + "::" + ctorMatch + " => {\n" + printRhs + "\n}\n";
        i := i + 1;
      }

      printImpl := printImpl + "}\n}\n}\n";

      var defaultImpl := "";
      if |c.ctors| > 0 {
        defaultImpl := "impl Default for r#" + c.name + " {\n" + "fn default() -> Self {\n" + "r#" + c.name + "::r#" + c.ctors[0].name + " {\n";
        i := 0;
        while i < |c.ctors[0].args| {
          var formal := c.ctors[0].args[i];
          defaultImpl := defaultImpl + formal.name + ": Default::default(),\n";
          i := i + 1;
        }

        defaultImpl := defaultImpl + "}\n}\n}\n";
      }

      s := enumBody + "\n" + printImpl + "\n" + defaultImpl;
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

            s := s + "r#" + p[i].id;

            i := i + 1;
          }
        }
        case Tuple(types) => {
          s := "(";
          var i := 0;
          while i < |types| {
            if i > 0 {
              s := s + " ";
            }

            var generated := GenType(types[i]);
            s := s + generated + ",";
            i := i + 1;
          }

          s := s + ")";
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

    static method GenParams(params: seq<Formal>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |params| {
        var param := params[i];
        var paramType := GenType(param.typ);
        s := s + "r#" + param.name + ": " + paramType;

        if i < |params| - 1 {
          s := s + ", ";
        }

        i := i + 1;
      }
    }

    static method GenMethod(m: Method) returns (s: string) {
      var params := GenParams(m.params);
      if (!m.isStatic) {
        params := "&self, " + params;
      }

      var retType := if |m.outTypes| != 1 then "(" else "";

      var typeI := 0;
      while typeI < |m.outTypes| {
        if typeI > 0 {
          retType := retType + ", ";
        }

        var typeString := GenType(m.outTypes[typeI]);
        retType := retType + typeString;

        typeI := typeI + 1;
      }

      if |m.outTypes| != 1 {
        retType := retType + ")";
      }

      s := "pub fn r#" + m.name;

      if (|m.typeParams| > 0) {
        s := s + "<";

        var i := 0;
        while i < |m.typeParams| {
          if i > 0 {
            s := s + ", ";
          }

          var typeString := GenType(m.typeParams[i]);
          s := s + typeString + ": std::default::Default";

          i := i + 1;
        }

        s := s + ">";
      }

      var earlyReturn := "return;";
      match m.outVars {
        case Some(outVars) => {
          earlyReturn := "return (";
          var outI := 0;
          while outI < |outVars| {
            if outI > 0 {
              earlyReturn := earlyReturn + ", ";
            }

            var outVar := outVars[outI];
            earlyReturn := earlyReturn + "r#" + outVar.id;

            outI := outI + 1;
          }
          earlyReturn := earlyReturn + ");";
        }
        case None => {}
      }

      var body := GenStmts(m.body, earlyReturn);
      match m.outVars {
        case Some(outVars) => {
          body := body + "\n" + earlyReturn;
        }
        case None => {}
      }

      s := s + "(" + params + ") -> " + retType + " {\n" + body + "\n}\n";
    }

    static method GenStmts(stmts: seq<Statement>, earlyReturn: string) returns (generated: string) {
      generated := "";
      var i := 0;
      while i < |stmts| {
        var stmt := stmts[i];
        var stmtString := GenStmt(stmt, earlyReturn);

        if i > 0 {
          generated := generated + "\n";
        }

        generated := generated + stmtString;
        i := i + 1;
      }
    }

    static method GenStmt(stmt: Statement, earlyReturn: string) returns (generated: string) {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var expr := GenExpr(expression);
          var typeString := GenType(typ);
          generated := "let mut r#" + name + ": " + typeString + " = " + expr + ";";
        }
        case DeclareVar(name, typ, None) => {
          var typeString := GenType(typ);
          generated := "let mut r#" + name + ": " + typeString + ";";
        }
        case Assign(name, expression) => {
          var expr := GenExpr(expression);
          generated := "r#" + name + " = " + expr + ";";
        }
        case If(cond, thn, els) => {
          var condString := GenExpr(cond);
          var thnString := GenStmts(thn, earlyReturn);
          var elsString := GenStmts(els, earlyReturn);
          generated := "if " + condString + " {\n" + thnString + "\n} else {\n" + elsString + "\n}";
        }
        case Call(on, name, typeArgs, args, maybeOutVars) => {
          var typeArgString := "";
          if (|typeArgs| >= 1) {
            var typeI := 0;
            typeArgString := "::<";
            while typeI < |typeArgs| {
              if typeI > 0 {
                typeArgString := typeArgString + ", ";
              }

              var typeString := GenType(typeArgs[typeI]);
              typeArgString := typeArgString + typeString;

              typeI := typeI + 1;
            }
            typeArgString := typeArgString + ">";
          }

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

          var enclosingString := GenExpr(on);
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::";
            }
            case _ => {
              enclosingString := enclosingString + ".";
            }
          }

          var receiver := "";
          match maybeOutVars {
            case Some(outVars) => {
              if (|outVars| > 1) {
                receiver := "(";
              }
              var outI := 0;
              while outI < |outVars| {
                if outI > 0 {
                  receiver := receiver + ", ";
                }

                var outVar := outVars[outI];
                receiver := receiver + outVar.id;

                outI := outI + 1;
              }
              if (|outVars| > 1) {
                receiver := receiver + ")";
              }
            }
            case None => {}
          }

          generated :=
            (if receiver != "" then (receiver + " = ") else "") +
            enclosingString + "r#" + name + typeArgString + "(" + argString + ");";
        }
        case Return(expr) => {
          var exprString := GenExpr(expr);
          generated := "return " + exprString + ";";
        }
        case EarlyReturn() => {
          generated := earlyReturn;
        }
        case Print(e) => {
          var printedExpr := GenExpr(e);
          generated := "print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(&" + printedExpr + "));";
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
          s := "r#" + name;
        }
        case Companion(typ) => {
          s := GenType(typ);
        }
        case InitializationValue(typ) => {
          s := "std::default::Default::default()";
        }
        case Tuple(values) => {
          s := "(";
          var i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen := GenExpr(values[i]);
            s := s + recursiveGen + ",";

            i := i + 1;
          }
          s := s + ")";
        }
        case DatatypeValue(typ, variant, values) => {
          s := GenType(typ);
          s := s + "::r#" + variant;

          var i := 0;
          s := s + " {";
          while i < |values| {
            var (name, value) := values[i];
            if i > 0 {
              s := s + ", ";
            }
            var recursiveGen := GenExpr(value);
            s := s + "r#" + name + ": " + recursiveGen;
            i := i + 1;
          }
          s := s + " }";
        }
        case BinOp(op, l, r) => {
          var left := GenExpr(l);
          var right := GenExpr(r);
          s := "(" + left + " " + op + " " + right + ")";
        }
        case Select(on, field, isDatatype) => {
          var onString := GenExpr(on);

          if isDatatype {
            s := onString + ".r#" + field + "().clone()";
          } else {
            s := onString + ".r#" + field + ".clone()";
          }
        }
        case TupleSelect(on, idx) => {
          var onString := GenExpr(on);
          s := onString + "." + natToString(idx) + ".clone()";
        }
        case Call(on, name, typeArgs, args) => {
          var typeArgString := "";
          if (|typeArgs| >= 1) {
            var typeI := 0;
            typeArgString := "::<";
            while typeI < |typeArgs| {
              if typeI > 0 {
                typeArgString := typeArgString + ", ";
              }

              var typeString := GenType(typeArgs[typeI]);
              typeArgString := typeArgString + typeString;

              typeI := typeI + 1;
            }
            typeArgString := typeArgString + ">";
          }

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

          var enclosingString := GenExpr(on);
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::";
            }
            case _ => {
              enclosingString := enclosingString + ".";
            }
          }

          s := enclosingString + "r#" + name + typeArgString + "(" + argString + ")";
        }
        case TypeTest(on, dType, variant) => {
          var exprGen := GenExpr(on);
          var typeGen := GenType(dType);
          s := "matches!(" + exprGen + ", " + typeGen + "::r#" + variant + "{ .. })";
        }
      }
    }

    static method Compile(p: seq<Module>, runtime: string) returns (s: string) {
      s := "#![allow(warnings, unconditional_panic)]\n";
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
