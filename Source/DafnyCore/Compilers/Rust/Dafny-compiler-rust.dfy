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
    static method GenModule(mod: Module, containingPath: seq<Ident>) returns (s: string) {
      var body := GenModuleBody(mod.body, containingPath + [Ident.Ident(mod.name)]);
      s := "mod r#" + mod.name + " {\n" + body + "\n}";
    }

    static method GenModuleBody(body: seq<ModuleItem>, containingPath: seq<Ident>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Module(m) => generated := GenModule(m, containingPath);
          case Class(c) => generated := GenClass(c, containingPath + [Ident.Ident(c.name)]);
          case Trait(t) => generated := GenTrait(t, containingPath);
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

    static method GenClass(c: Class, path: seq<Ident>) returns (s: string) {
      var implBody, traitBodies := GenClassImplBody(c.body, false, Type.Path(path, [], ResolvedType.Datatype(path)), {});
      implBody := "pub fn new() -> Self {\n" + "r#" + c.name + " {\n" + "" + "\n}\n}\n" + implBody;
      s := "pub struct r#" + c.name + " {\n" + "" +  "\n}" + "\n" + "impl r#" + c.name + " {\n" + implBody + "\n}";
      if (|c.superClasses| > 0) {
        var i := 0;
        while i < |c.superClasses| {
          var superClass := c.superClasses[i];
          match superClass {
            case Path(traitPath, typeArgs, Trait(_)) => {
              var pathStr := GenPath(traitPath);
              var typeArgs := GenTypeArgs(typeArgs, false, false);
              var body := "";
              if traitPath in traitBodies {
                body := traitBodies[traitPath];
              }

              var genSelfPath := GenPath(path);
              s := s + "\nimpl " + pathStr + typeArgs + " for ::std::rc::Rc<" + genSelfPath + "> {\n" + body + "\n}";
            }
            case _ => {}
          }
          i := i + 1;
        }
      }
    }

    static method GenTrait(t: Trait, containingPath: seq<Ident>) returns (s: string) {
      var typeParamsSet := {};
      var typeParams := "";
      var tpI := 0;
      if |t.typeParams| > 0 {
        typeParams := "<";
        while tpI < |t.typeParams| {
          var tp := t.typeParams[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + "r#" + genTp + ", ";
          tpI := tpI + 1;
        }
        typeParams := typeParams + ">";
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var implBody, _ := GenClassImplBody(t.body, true, Type.Path(fullPath, [], ResolvedType.Trait(fullPath)), typeParamsSet);
      s := "pub trait r#" + t.name + typeParams + " {\n" + implBody +  "\n}";
    }

    static method GenNewtype(c: Newtype) returns (s: string) {
      var underlyingType := GenType(c.base, false, false);
      s := "#[derive(Clone, PartialEq)]\npub struct r#" + c.name + "(pub " + underlyingType +  ");\n";
      s := s + "impl ::std::default::Default for r#" + c.name + " {\n";
      s := s + "fn default() -> Self {\n";

      match c.witnessExpr {
        case Some(e) => {
          var eStr, _, _ := GenExpr(e, [], true);
          s := s + "r#" + c.name + "(" + eStr + ")\n";
        }
        case None => {
          s := s + "r#" + c.name + "(::std::default::Default::default())\n";
        }
      }

      s := s + "}\n";
      s := s + "}\n";
      s := s + "impl ::dafny_runtime::DafnyPrint for r#" + c.name + " {\n";
      s := s + "fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {\n";
      s := s + "::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)\n";
      s := s + "}\n";
      s := s + "}";

      // inherit common traits
      var ops := [("::std::ops::Add", "add"), ("::std::ops::Sub", "sub"), ("::std::ops::Mul", "mul"), ("::std::ops::Div", "div")];
      var i := 0;
      while i < |ops| {
        var (traitName, methodName) := ops[i];
        s := s + "impl " + traitName + "<r#" + c.name + "> for r#" + c.name;
        s := s + " where " + underlyingType + ": " + traitName + "<" + underlyingType + ", Output = " + underlyingType + "> {\n";
        s := s + "type Output = r#" + c.name + ";\n";
        s := s + "fn " + methodName + "(self, other: r#" + c.name + ") -> r#" + c.name + " {\n";
        s := s + "r#" + c.name + "(" + traitName + "::" + methodName + "(self.0, other.0))\n";
        s := s + "}\n";
        s := s + "}\n";
        i := i + 1;
      }

      s := s + "impl ::std::cmp::PartialOrd<r#" + c.name + "> for r#" + c.name;
      s := s + " where " + underlyingType + ": ::std::cmp::PartialOrd<" + underlyingType + "> {\n";
      s := s + "fn partial_cmp(&self, other: &r#" + c.name + ") -> ::std::option::Option<::std::cmp::Ordering> {\n";
      s := s + "self.0.partial_cmp(&other.0)\n";
      s := s + "}\n";
      s := s + "}\n";
    }

    static method GenDatatype(c: Datatype) returns (s: string) {
      var typeParamsSet := {};
      var typeParams := "";
      var tpI := 0;
      if |c.typeParams| > 0 {
        typeParams := "<";
        while tpI < |c.typeParams| {
          var tp := c.typeParams[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + "r#" + genTp + ", ";
          tpI := tpI + 1;
        }
        typeParams := typeParams + ">";
      }

      var ctors := "";
      var i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorBody := "r#" + ctor.name + " { ";
        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          var formalType := GenType(formal.typ, false, false);
          if c.isCo {
            ctorBody := ctorBody + "r#" + formal.name + ": ::dafny_runtime::LazyFieldWrapper<" + formalType + ">, ";
          } else {
            ctorBody := ctorBody + "r#" + formal.name + ": " + formalType + ", ";
          }
          j := j + 1;
        }

        ctorBody := ctorBody + "}";

        ctors := ctors + ctorBody + ",\n";
        i := i + 1;
      }

      var selfPath := [Ident.Ident(c.name)];
      var implBody, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [], ResolvedType.Datatype(selfPath)), typeParamsSet);
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

            var formalType := GenType(formal.typ, false, false);
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
                if c.isCo {
                  ctorMatch := ctorMatch + "} => ::std::ops::Deref::deref(&" + formal.name + ".0),\n";
                } else {
                  ctorMatch := ctorMatch + "} => " + formal.name + ",\n";
                }
              } else {
                ctorMatch := ctorMatch + "} => panic!(\"field does not exist on this variant\"),\n";
              }
              methodBody := methodBody + ctorMatch;
              k := k + 1;
            }

            methodBody := methodBody + "}\n";

            implBody := implBody + "pub fn r#" + formal.name + "(&self) -> &" + formalType + " {\n" + methodBody + "}\n";
          }
          j := j + 1;
        }

        i := i + 1;
      }

      var constrainedTypeParams := "";
      if |c.typeParams| > 0 {
        tpI := 0;
        constrainedTypeParams := "<";
        while tpI < |c.typeParams| {
          if tpI > 0 {
            constrainedTypeParams := constrainedTypeParams + ", ";
          }

          var tp := c.typeParams[tpI];
          var genTp := GenType(tp, false, false);
          constrainedTypeParams := constrainedTypeParams + "r#" + genTp + ": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static";
          tpI := tpI + 1;
        }
        constrainedTypeParams := constrainedTypeParams + ">";
      }

      var enumBody := "#[derive(PartialEq)]\npub enum r#" + c.name + typeParams + " {\n" + ctors +  "\n}" + "\n" + "impl " + constrainedTypeParams + " r#" + c.name + typeParams + " {\n" + implBody + "\n}";

      var printImpl := "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyPrint for r#" + c.name + typeParams + " {\n" + "fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n" + "match self {\n";
      i := 0;
      while i < |c.ctors| {
        var ctor := c.ctors[i];
        var ctorMatch := "r#" + ctor.name + " { ";

        var modulePrefix := if c.enclosingModule.id == "_module" then "" else c.enclosingModule.id + ".";
        var printRhs := "write!(__fmt_print_formatter, \"" + modulePrefix + c.name + "." + ctor.name + (if ctor.hasAnyArgs then "(\")?;" else "\")?;");

        var j := 0;
        while j < |ctor.args| {
          var formal := ctor.args[j];
          ctorMatch := ctorMatch + formal.name + ", ";

          if (j > 0) {
            printRhs := printRhs + "\nwrite!(__fmt_print_formatter, \", \")?;";
          }
          printRhs := printRhs + "\n::dafny_runtime::DafnyPrint::fmt_print(" + formal.name + ", __fmt_print_formatter, false)?;";

          j := j + 1;
        }

        ctorMatch := ctorMatch + "}";

        if (ctor.hasAnyArgs) {
          printRhs := printRhs + "\nwrite!(__fmt_print_formatter, \")\")?;";
        }

        printRhs := printRhs + "\nOk(())";

        printImpl := printImpl + "r#" + c.name + "::" + ctorMatch + " => {\n" + printRhs + "\n}\n";
        i := i + 1;
      }

      printImpl := printImpl + "}\n}\n}\n";

      var defaultImpl := "";
      if |c.ctors| > 0 {
        defaultImpl := "impl " + constrainedTypeParams + " ::std::default::Default for r#" + c.name + typeParams + " {\n" + "fn default() -> Self {\n" + "r#" + c.name + "::r#" + c.ctors[0].name + " {\n";
        i := 0;
        while i < |c.ctors[0].args| {
          var formal := c.ctors[0].args[i];
          defaultImpl := defaultImpl + formal.name + ": std::default::Default::default(),\n";
          i := i + 1;
        }

        defaultImpl := defaultImpl + "}\n}\n}\n";
      }

      s := enumBody + "\n" + printImpl + "\n" + defaultImpl;
    }

    static method GenPath(p: seq<Ident>) returns (s: string) {
      if |p| == 0 {
        // TODO(shadaj): this special casing is not great
        return "Self";
      } else {
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
    }

    static method GenTypeArgs(args: seq<Type>, inBinding: bool, inFn: bool) returns (s: string) {
      s := "";
      if |args| > 0 {
        s := s + "<";
        var i := 0;
        while i < |args| {
          if i > 0 {
            s := s + ", ";
          }

          var genTp := GenType(args[i], inBinding, inFn);
          s := s + genTp;
          i := i + 1;
        }
        s := s + ">";
      }
    }

    static method GenType(c: Type, inBinding: bool, inFn: bool) returns (s: string) {
      match c {
        case Path(p, args, resolved) => {
          s := GenPath(p);

          var typeArgs := GenTypeArgs(args, inBinding, inFn);
          s := s + typeArgs;

          match resolved {
            case Datatype(_) => {
              s := "::std::rc::Rc<" + s + ">";
            }
            case Trait(_) => {
              if inBinding {
                // impl trait in bindings is not stable
                s := "_";
              } else {
                s := "impl " + s + "";
              }
            }
            case Primitive => {}
          }
        }
        case Tuple(types) => {
          s := "(";
          var i := 0;
          while i < |types| {
            if i > 0 {
              s := s + " ";
            }

            var generated := GenType(types[i], inBinding, inFn);
            s := s + generated + ",";
            i := i + 1;
          }

          s := s + ")";
        }
        case Array(element) => {
          var elemStr := GenType(element, inBinding, inFn);
          s := "::std::vec::Vec<" + elemStr + ">";
        }
        case Seq(element) => {
          var elemStr := GenType(element, inBinding, inFn);
          s := "::std::vec::Vec<" + elemStr + ">";
        }
        case Set(element) => {
          var elemStr := GenType(element, inBinding, inFn);
          s := "::std::collections::HashSet<" + elemStr + ">";
        }
        case Multiset(element) => {
          var elemStr := GenType(element, inBinding, inFn);
          s := "::std::collections::HashMap<" + elemStr + ", u64>";
        }
        case Map(key, value) => {
          var keyStr := GenType(key, inBinding, inFn);
          var valueStr := GenType(value, inBinding, inFn);
          s := "::std::collections::HashMap<" + keyStr + ", " + valueStr + ">";
        }
        case Arrow(args, result) => {
          if inBinding {
            s := "::dafny_runtime::FunctionWrapper<_>";
          } else {
            if inFn {
              s := "::dafny_runtime::FunctionWrapper<Box<dyn Fn(";
            } else {
              s := "::dafny_runtime::FunctionWrapper<impl Fn(";
            }

            var i := 0;
            while i < |args| {
              if i > 0 {
                s := s + ", ";
              }

              var generated := GenType(args[i], inBinding, true);
              s := s + "&" + generated;
              i := i + 1;
            }

            var resultType := GenType(result, inBinding, inFn);

            if inFn {
              s := s + ") -> " + resultType + " + 'static>>";
            } else {
              s := s + ") -> " + resultType + " + Clone + 'static>";
            }
          }
        }
        case TypeArg(Ident(name)) => s := name;
        case Primitive(p) => {
          match p {
            case String => s := "Vec<char>";
            case Bool => s := "bool";
            case Char => s := "char";
          }
        }
        case Passthrough(v) => s := v;
      }
    }

    static method GenClassImplBody(body: seq<ClassItem>, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>) returns (s: string, traitBodies: map<seq<Ident>, string>) {
      s := "";
      traitBodies := map[];

      var i := 0;
      while i < |body| {
        match body[i] {
          case Method(m) => {
            match m.overridingPath {
              case Some(p) => {
                var existing := "";
                if p in traitBodies {
                  existing := traitBodies[p];
                }

                if |existing| > 0 {
                  existing := existing + "\n";
                }

                var genMethod := GenMethod(m, true, enclosingType, enclosingTypeParams);
                existing := existing + genMethod;

                traitBodies := traitBodies + map[p := existing];
              }
              case None => {
                var generated := GenMethod(m, forTrait, enclosingType, enclosingTypeParams);
                s := s + generated;
              }
            }
          }
          case Field(f) => { /* TODO */ }
        }

        if |s| > 0 {
          s := s + "\n";
        }

        i := i + 1;
      }
    }

    static method GenParams(params: seq<Formal>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |params| {
        var param := params[i];
        var paramType := GenType(param.typ, false, false);
        s := s + "r#" + param.name + ": &" + paramType;

        if i < |params| - 1 {
          s := s + ", ";
        }

        i := i + 1;
      }
    }

    static method GenMethod(m: Method, forTrait: bool, enclosingType: Type, enclosingTypeParams: set<Type>) returns (s: string) {
      var params := GenParams(m.params);
      var paramNames := [];
      var paramI := 0;
      while paramI < |m.params| {
        paramNames := paramNames + [m.params[paramI].name];
        paramI := paramI + 1;
      }

      if (!m.isStatic) {
        if (forTrait) {
          params := "&self" + ", " + params;
        } else {
          var enclosingTypeString := GenType(enclosingType, false, false);
          params := "self: &" + enclosingTypeString + ", " + params;
        }
      }

      var retType := if |m.outTypes| != 1 then "(" else "";

      var typeI := 0;
      while typeI < |m.outTypes| {
        if typeI > 0 {
          retType := retType + ", ";
        }

        var typeString := GenType(m.outTypes[typeI], false, false);
        retType := retType + typeString;

        typeI := typeI + 1;
      }

      if |m.outTypes| != 1 {
        retType := retType + ")";
      }

      if forTrait {
        s := "fn r#" + m.name;
      } else {
        s := "pub fn r#" + m.name;
      }

      var typeParamsFiltered := [];
      var typeParamI := 0;
      while typeParamI < |m.typeParams| {
        var typeParam := m.typeParams[typeParamI];
        if !(typeParam in enclosingTypeParams) {
          typeParamsFiltered := typeParamsFiltered + [typeParam];
        }

        typeParamI := typeParamI + 1;
      }

      if (|typeParamsFiltered| > 0) {
        s := s + "<";

        var i := 0;
        while i < |typeParamsFiltered| {
          if i > 0 {
            s := s + ", ";
          }

          var typeString := GenType(typeParamsFiltered[i], false, false);
          s := s + typeString + ": Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static";

          i := i + 1;
        }

        s := s + ">";
      }

      s := s + "(" + params + ") -> " + retType;

      if m.hasBody {
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

        var body, _ := GenStmts(m.body, paramNames, earlyReturn);
        match m.outVars {
          case Some(outVars) => {
            body := body + "\n" + earlyReturn;
          }
          case None => {}
        }

        s := s + " {\n" + body + "\n}\n";
      } else {
        s := s + ";\n";
      }
    }

    static method GenStmts(stmts: seq<Statement>, params: seq<string>, earlyReturn: string) returns (generated: string, readIdents: set<string>) {
      generated := "";
      readIdents := {};
      var i := 0;
      while i < |stmts| {
        var stmt := stmts[i];
        var stmtString, recIdents := GenStmt(stmt, params, earlyReturn);
        readIdents := readIdents + recIdents;

        if i > 0 {
          generated := generated + "\n";
        }

        generated := generated + stmtString;
        i := i + 1;
      }
    }

    static method GenStmt(stmt: Statement, params: seq<string>, earlyReturn: string) returns (generated: string, readIdents: set<string>) {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var expr, _, recIdents := GenExpr(expression, params, true);
          var typeString := GenType(typ, true, false);
          generated := "let mut r#" + name + ": " + typeString + " = " + expr + ";";
          readIdents := recIdents;
        }
        case DeclareVar(name, typ, None) => {
          var typeString := GenType(typ, true, false);
          generated := "let mut r#" + name + ": " + typeString + ";";
          readIdents := {};
        }
        case Assign(name, expression) => {
          var expr, _, recIdents := GenExpr(expression, params, true);
          generated := "r#" + name + " = " + expr + ";";
          readIdents := recIdents;
        }
        case If(cond, thn, els) => {
          var condString, _, recIdents := GenExpr(cond, params, true);
          readIdents := recIdents;
          var thnString, thnIdents := GenStmts(thn, params, earlyReturn);
          readIdents := readIdents + thnIdents;
          var elsString, elsIdents := GenStmts(els, params, earlyReturn);
          readIdents := readIdents + elsIdents;
          generated := "if " + condString + " {\n" + thnString + "\n} else {\n" + elsString + "\n}";
        }
        case While(cond, body) => {
          var condString, _, recIdents := GenExpr(cond, params, true);
          readIdents := recIdents;
          var bodyString, bodyIdents := GenStmts(body, params, earlyReturn);
          readIdents := readIdents + bodyIdents;
          generated := "while " + condString + " {\n" + bodyString + "\n}";
        }
        case Call(on, name, typeArgs, args, maybeOutVars) => {
          readIdents := {};

          var typeArgString := "";
          if (|typeArgs| >= 1) {
            var typeI := 0;
            typeArgString := "::<";
            while typeI < |typeArgs| {
              if typeI > 0 {
                typeArgString := typeArgString + ", ";
              }

              var typeString := GenType(typeArgs[typeI], false, false);
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

            var argExpr, isOwned, argIdents := GenExpr(args[i], params, false);
            argString := argString + (if isOwned then "&" else "") + argExpr;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var enclosingString, _, enclosingIdents := GenExpr(on, params, true);
          readIdents := readIdents + enclosingIdents;
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::";
            }
            case _ => {
              enclosingString := "(" + enclosingString + ").";
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
          var exprString, _, recIdents := GenExpr(expr, params, true);
          readIdents := recIdents;
          generated := "return " + exprString + ";";
        }
        case EarlyReturn() => {
          generated := earlyReturn;
          readIdents := {};
        }
        case Halt() => {
          generated := "panic!(\"Halt\");";
          readIdents := {};
        }
        case Print(e) => {
          var printedExpr, isOwned, recIdents := GenExpr(e, params, false);
          generated := "print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(" + (if isOwned then "&" else "") + printedExpr + "));";
          readIdents := recIdents;
        }
      }
    }

    static method GenExpr(e: Expression, params: seq<string>, mustOwn: bool) returns (s: string, isOwned: bool, readIdents: set<string>) {
      match e {
        case Literal(BoolLiteral(false)) => {
          s := "false";
          isOwned := true;
          readIdents := {};
        }
        case Literal(BoolLiteral(true)) => {
          s := "true";
          isOwned := true;
          readIdents := {};
        }
        case Literal(IntLiteral(i)) => {
          if (i < 0) {
            s := "-" + natToString(-i);
          } else {
            s := natToString(i);
          }

          isOwned := true;
          readIdents := {};
        }
        case Literal(DecLiteral(l)) => {
          s := l;
          isOwned := true;
          readIdents := {};
        }
        case Literal(StringLiteral(l)) => {
          // TODO(shadaj): handle unicode properly
          s := "\"" + l + "\".chars().collect::<Vec<char>>()";
          isOwned := true;
          readIdents := {};
        }
        case Literal(CharLiteral(c)) => {
          s := "::std::primitive::char::from_u32(" + natToString(c as nat) + ").unwrap()";
          isOwned := true;
          readIdents := {};
        }
        case Literal(Null) => {
          s := "None";
          isOwned := true;
          readIdents := {};
        }
        case Ident(name) => {
          s := "r#" + name;

          if name in params {
            if mustOwn {
              s := s + ".clone()";
              isOwned := true;
            } else {
              isOwned := false;
            }
          } else {
            if mustOwn {
              s := s + ".clone()";
              isOwned := true;
            } else {
              s := "&" + s;
              isOwned := false;
            }
          }

          readIdents := {name};
        }
        case Companion(path) => {
          s := GenPath(path);
          isOwned := true;
          readIdents := {};
        }
        case InitializationValue(typ) => {
          s := "std::default::Default::default()";
          isOwned := true;
          readIdents := {};
        }
        case Tuple(values) => {
          s := "(";
          readIdents := {};
          var i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen, _, recIdents := GenExpr(values[i], params, true);
            s := s + recursiveGen + ",";
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + ")";
          isOwned := true;
        }
        case New(path, args) => {
          var path := GenPath(path);
          s := "::std::rc::Rc::new(" + path + "::new(";
          readIdents := {};
          var i := 0;
          while i < |args| {
            if i > 0 {
              s := s + ", ";
            }

            var recursiveGen, _, recIdents := GenExpr(args[i], params, true);
            s := s + recursiveGen;
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + "))";
          isOwned := true;
        }
        case NewArray(dims) => {
          var i := |dims| - 1;
          s := "::std::default::Default::default()";
          readIdents := {};
          while i >= 0 {
            var recursiveGen, _, recIdents := GenExpr(dims[i], params, true);
            s := "vec![" + s + "; (" + recursiveGen + ") as usize]";
            readIdents := readIdents + recIdents;

            i := i - 1;
          }

          isOwned := true;
        }
        case DatatypeValue(path, variant, isCo, values) => {
          var path := GenPath(path);
          s := "::std::rc::Rc::new(" + path + "::r#" + variant;
          readIdents := {};

          var i := 0;
          s := s + " {";
          while i < |values| {
            var (name, value) := values[i];
            if i > 0 {
              s := s + ", ";
            }

            if isCo {
              var recursiveGen, _, recIdents := GenExpr(value, [], true);
              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let r#" + next + " = r#" + next + ".clone();\n";
                recIdents := recIdents - {next};
              }
              s := s + "r#" + name + ": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(Box::new({\n" + allReadCloned + "move || (" + recursiveGen + ")})))";
            } else {
              var recursiveGen, _, recIdents := GenExpr(value, params, true);
              s := s + "r#" + name + ": " + recursiveGen;
              readIdents := readIdents + recIdents;
            }
            i := i + 1;
          }
          s := s + " })";
          isOwned := true;
        }
        case NewtypeValue(tpe, expr) => {
          var typeString := GenType(tpe, false, false);
          var recursiveGen, _, recIdents := GenExpr(expr, params, true);
          s := typeString + "(" + recursiveGen + ")";
          isOwned := true;
          readIdents := recIdents;
        }
        case SeqValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], params, true);
            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }

          s := "vec![";
          i := 0;
          while i < |generatedValues| {
            if i > 0 {
              s := s + ", ";
            }
            s := s + generatedValues[i];
            i := i + 1;
          }
          s := s + "]";

          isOwned := true;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          while i < |exprs| {
            var recursiveGen, _, recIdents := GenExpr(exprs[i], params, true);
            generatedValues := generatedValues + [recursiveGen];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }

          s := "vec![";
          i := 0;
          while i < |generatedValues| {
            if i > 0 {
              s := s + ", ";
            }
            s := s + generatedValues[i];
            i := i + 1;
          }
          s := s + "].into_iter().collect::<std::collections::HashSet<_>>()";

          isOwned := true;
        }
        case This() => {
          if mustOwn {
            s := "self.clone()";
            isOwned := true;
          } else {
            s := "self";
            isOwned := false;
          }

          readIdents := {"self"};
        }
        case Ite(cond, t, f) => {
          var condString, _, recIdentsCond := GenExpr(cond, params, true);
          var _, tHasToBeOwned, _ := GenExpr(t, params, mustOwn); // check if t has to be owned even if not requested
          var fString, fOwned, recIdentsF := GenExpr(f, params, tHasToBeOwned);
          var tString, _, recIdentsT := GenExpr(t, params, fOwned); // there's a chance that f forced ownership
          s := "(if " + condString + " {\n" + tString + "\n} else {\n" + fString + "\n})";
          isOwned := fOwned;
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
        }
        case UnOp(Not, e) => {
          var recursiveGen, _, recIdents := GenExpr(e, params, true);
          s := "!(" + recursiveGen + ")";
          isOwned := true;
          readIdents := recIdents;
        }
        case UnOp(BitwiseNot, e) => {
          var recursiveGen, _, recIdents := GenExpr(e, params, true);
          s := "~(" + recursiveGen + ")";
          isOwned := true;
          readIdents := recIdents;
        }
        case UnOp(Cardinality, e) => {
          var recursiveGen, _, recIdents := GenExpr(e, params, false);
          s := "(" + recursiveGen + ").len()";
          isOwned := true;
          readIdents := recIdents;
        }
        case BinOp(op, l, r) => {
          var left, _, recIdentsL := GenExpr(l, params, true);
          var right, _, recIdentsR := GenExpr(r, params, true);
          s := "(" + left + " " + op + " " + right + ")";
          isOwned := true;
          readIdents := recIdentsL + recIdentsR;
        }
        case SelectFn(on, field, isDatatype, isStatic, arity) => {
          var onString, onOwned, recIdents := GenExpr(on, params, false);

          if isStatic {
            s := onString + "::" + field;
          } else {
            s := "{\n";
            s := s + "let callTarget = (" + onString + (if onOwned then ")" else ").clone()") + ";\n";
            var args := "";
            var i := 0;
            while i < arity {
              if i > 0 {
                args := args + ", ";
              }
              args := args + "arg" + natToString(i);
              i := i + 1;
            }
            s := s + "move |" + args + "| {\n";
            s := s + "callTarget." + field + "(" + args + ")\n";
            s := s + "}\n";
            s := s + "}";
          }

          s := "::dafny_runtime::FunctionWrapper(" + s + ")";

          isOwned := true;
          readIdents := recIdents;
        }
        case Select(on, field, isDatatype) => {
          var onString, _, recIdents := GenExpr(on, params, false);

          if isDatatype {
            s := "(" + onString + ")" + ".r#" + field + "()";
            if mustOwn {
              s := "(" + s + ").clone()";
              isOwned := true;
            } else {
              isOwned := false;
            }
          } else {
            s := "(" + onString + ")" + ".r#" + field;
            if mustOwn {
              s := "(" + s + ").clone()";
              isOwned := true;
            } else {
              isOwned := false;
            }
          }

          readIdents := recIdents;
        }
        case TupleSelect(on, idx) => {
          var onString, _, recIdents := GenExpr(on, params, false);
          s := "(" + onString + ")." + natToString(idx);
          if mustOwn {
            s := "(" + s + ")" + ".clone()";
            isOwned := true;
          } else {
            s := "&" + s;
            isOwned := false;
          }
          readIdents := recIdents;
        }
        case Call(on, name, typeArgs, args) => {
          readIdents := {};

          var typeArgString := "";
          if (|typeArgs| >= 1) {
            var typeI := 0;
            typeArgString := "::<";
            while typeI < |typeArgs| {
              if typeI > 0 {
                typeArgString := typeArgString + ", ";
              }

              var typeString := GenType(typeArgs[typeI], false, false);
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

            var argExpr, isOwned, recIdents := GenExpr(args[i], params, false);
            readIdents := readIdents + recIdents;
            argString := argString + (if isOwned then "&" else "") + argExpr;

            i := i + 1;
          }

          var enclosingString, _, recIdents := GenExpr(on, params, false);
          readIdents := readIdents + recIdents;
          match on {
            case Companion(_) => {
              enclosingString := enclosingString + "::";
            }
            case _ => {
              enclosingString := "(" + enclosingString + ").";
            }
          }

          s := enclosingString + "r#" + name.id + typeArgString + "(" + argString + ")";
          isOwned := true;
        }
        case Lambda(params, body) => {
          var paramNames := [];
          var i := 0;
          while i < |params| {
            paramNames := paramNames + [params[i].name];
            i := i + 1;
          }

          var recursiveGen, recIdents := GenStmts(body, paramNames, "");
          readIdents := {};
          var allReadCloned := "";
          while recIdents != {} decreases recIdents {
            var next: string :| next in recIdents;

            if !(next in paramNames) {
              allReadCloned := allReadCloned + "let r#" + next + " = r#" + next + ".clone();\n";
              readIdents := readIdents + {next};
            }

            recIdents := recIdents - {next};
          }

          var paramsString := "";
          i := 0;
          while i < |params| {
            if i > 0 {
              paramsString := paramsString + ", ";
            }

            var typStr := GenType(params[i].typ, false, true);

            paramsString := paramsString + params[i].name + ": &" + typStr;
            i := i + 1;
          }

          s := "::dafny_runtime::FunctionWrapper({\n" + allReadCloned + "Box::new(move |" + paramsString + "| {\n" + recursiveGen + "\n})})";
          isOwned := true;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, valueOwned, recIdents := GenExpr(value, params, false);
          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, false, true);
          var bodyGen, bodyOwned, bodyIdents := GenExpr(iifeBody, params + if valueOwned then [] else [name.id], mustOwn);
          readIdents := readIdents + bodyIdents;

          s := "{\nlet r#" + name.id + ": " + (if valueOwned then "" else "&") + valueTypeGen + " = " + valueGen + ";\n" + bodyGen + "\n}";
          isOwned := bodyOwned;
        }
        case Apply(func, args) => {
          var funcString, _, recIdents := GenExpr(func, params, false);
          readIdents := recIdents;

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, isOwned, recIdents := GenExpr(args[i], params, false);
            readIdents := readIdents + recIdents;
            argString := argString + (if isOwned then "&" else "") + argExpr;

            i := i + 1;
          }

          s := "((" + funcString + ").0" + "(" + argString + "))";
          isOwned := true;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, recIdents := GenExpr(on, params, false);
          var dTypePath := GenPath(dType);
          s := "matches!(" + exprGen + ".as_ref(), " + dTypePath + "::r#" + variant + "{ .. })";
          isOwned := true;
          readIdents := recIdents;
        }
      }
    }

    static method Compile(p: seq<Module>) returns (s: string) {
      s := "#![allow(warnings, unconditional_panic)]\n";
      s := s + "extern crate dafny_runtime;\n";

      var i := 0;
      while i < |p| {
        var generated: string;
        generated := GenModule(p[i], []);

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
