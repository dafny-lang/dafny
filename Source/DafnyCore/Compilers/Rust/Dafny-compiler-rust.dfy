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

    static method GenTypeParameters(params: seq<Type>) returns (typeParamsSet: set<Type>, typeParams: string, constrainedTypeParams: string) {
      typeParamsSet := {};
      typeParams := "";
      constrainedTypeParams := "";
      var tpI := 0;

      if |params| > 0 {
        typeParams := "<";
        constrainedTypeParams := "<";
        while tpI < |params| {
          var tp := params[tpI];
          typeParamsSet := typeParamsSet + {tp};
          var genTp := GenType(tp, false, false);
          typeParams := typeParams + genTp + ", ";
          constrainedTypeParams := constrainedTypeParams + genTp + ": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<" + genTp + "> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static, ";
          tpI := tpI + 1;
        }
        typeParams := typeParams + ">";
        constrainedTypeParams := constrainedTypeParams + ">";
      }
    }

    static method GenClass(c: Class, path: seq<Ident>) returns (s: string) {
      var typeParamsSet, typeParams, constrainedTypeParams := GenTypeParameters(c.typeParams);

      var fields := "";
      var fieldInits := "";
      var fieldI := 0;
      while fieldI < |c.fields| {
        var field := c.fields[fieldI];
        var fieldType := GenType(field.formal.typ, false, false);
        fields := fields + "pub r#" + field.formal.name + ": ::std::cell::RefCell<" + fieldType + ">,\n";

        match field.defaultValue {
          case Some(e) => {
            var eStr, _, _, _ := GenExpr(e, None, [], true);
            fieldInits := fieldInits + "r#" + field.formal.name + ": ::std::cell::RefCell::new(" + eStr + "),\n";
          }
          case None => {
            fieldInits := fieldInits + "r#" + field.formal.name + ": ::std::cell::RefCell::new(::std::default::Default::default()),\n";
          }
        }

        fieldI := fieldI + 1;
      }

      var typeParamI := 0;
      while typeParamI < |c.typeParams| {
        var tpeGen := GenType(c.typeParams[typeParamI], false, false);
        fields := fields + "_phantom_type_param_" + natToString(typeParamI) + ": ::std::marker::PhantomData<" + tpeGen + ">,\n";
        fieldInits := fieldInits + "_phantom_type_param_" + natToString(typeParamI) + ": ::std::marker::PhantomData,\n";

        typeParamI := typeParamI + 1;
      }

      s := "pub struct r#" + c.name + typeParams + " {\n" + fields +  "\n}";

      var implBody, traitBodies := GenClassImplBody(c.body, false, Type.Path([], [], ResolvedType.Datatype(path)), {});
      implBody := "pub fn new() -> Self {\n" + "r#" + c.name + " {\n" + fieldInits + "\n}\n}\n" + implBody;

      s := s + "\n" + "impl " + constrainedTypeParams + " r#" + c.name + typeParams + " {\n" + implBody + "\n}";
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
              s := s + "\nimpl " + pathStr + typeArgs + " for ::std::rc::Rc<" + genSelfPath + typeParams + "> {\n" + body + "\n}";
            }
            case _ => {}
          }
          i := i + 1;
        }
      }

      var defaultImpl := "impl " + constrainedTypeParams + " ::std::default::Default for r#" + c.name + typeParams + " {\n";
      defaultImpl := defaultImpl + "fn default() -> Self {\n";
      defaultImpl := defaultImpl + "r#" + c.name + "::new()\n";
      defaultImpl := defaultImpl + "}\n";
      defaultImpl := defaultImpl + "}\n";

      var printImpl := "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyPrint for r#" + c.name + typeParams + " {\n" + "fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {\n";
      printImpl := printImpl + "write!(__fmt_print_formatter, \"" + c.enclosingModule.id + "." + c.name + (if |c.fields| > 0 then "("  else "") + "\")?;";
      var i := 0;
      while i < |c.fields| {
        var field := c.fields[i];
        if (i > 0) {
          printImpl := printImpl + "\nwrite!(__fmt_print_formatter, \", \")?;";
        }
        printImpl := printImpl + "\n::dafny_runtime::DafnyPrint::fmt_print(::std::ops::Deref::deref(&(self.r#" + field.formal.name + ".borrow())), __fmt_print_formatter, false)?;";
        i := i + 1;
      }

      if |c.fields| > 0 {
        printImpl := printImpl + "\nwrite!(__fmt_print_formatter, \")\")?;";
      }
      printImpl := printImpl + "\nOk(())\n}\n}\n";

      var ptrPartialEqImpl := "impl " + constrainedTypeParams + " ::std::cmp::PartialEq for r#" + c.name + typeParams + " {\n";
      ptrPartialEqImpl := ptrPartialEqImpl + "fn eq(&self, other: &Self) -> bool {\n";
      ptrPartialEqImpl := ptrPartialEqImpl + "::std::ptr::eq(self, other)";
      ptrPartialEqImpl := ptrPartialEqImpl + "\n}\n}\n";

      s := s + "\n" + defaultImpl + "\n" + printImpl + "\n" + ptrPartialEqImpl;
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
          typeParams := typeParams + genTp + ", ";
          tpI := tpI + 1;
        }
        typeParams := typeParams + ">";
      }

      var fullPath := containingPath + [Ident.Ident(t.name)];
      var implBody, _ := GenClassImplBody(t.body, true, Type.Path(fullPath, [], ResolvedType.Trait(fullPath)), typeParamsSet);
      s := "pub trait r#" + t.name + typeParams + " {\n" + implBody +  "\n}";
    }

    static method GenNewtype(c: Newtype) returns (s: string) {
      var typeParamsSet, typeParams, constrainedTypeParams := GenTypeParameters(c.typeParams);

      var underlyingType := GenType(c.base, false, false);
      s := "#[derive(Clone, PartialEq)]\n#[repr(transparent)]\npub struct r#" + c.name + typeParams + "(pub " + underlyingType +  ");\n";
      s := s + "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyErasable for r#" + c.name + typeParams + " {\n";
      s := s + "type Erased = " + underlyingType + ";\n";
      s := s + "#[inline]\nfn erase(&self) -> &Self::Erased {\n";
      s := s + "&self.0\n";
      s := s + "}\n";
      s := s + "#[inline]\nfn erase_owned(self) -> Self::Erased {\n";
      s := s + "self.0\n";
      s := s + "}\n";
      s := s + "}\n";
      s := s + "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyUnerasable<" + underlyingType + "> for r#" + c.name + typeParams + " {\n";
      s := s + "#[inline]\nfn unerase(x: &" + underlyingType + ") -> &Self {\n";
      s := s + "unsafe { &*(x as *const " + underlyingType + " as *const r#" + c.name + typeParams + ") }\n";
      s := s + "}\n";
      s := s + "#[inline]\nfn unerase_owned(x: " + underlyingType + ") -> Self {\n";
      s := s + "r#" + c.name + "(x)\n";
      s := s + "}\n";
      s := s + "}\n";
      s := s + "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyUnerasable<r#" + c.name + typeParams + "> for r#" + c.name + typeParams + " {\n";
      s := s + "#[inline]\nfn unerase(x: &r#" + c.name + typeParams + ") -> &Self {\n";
      s := s + "x\n";
      s := s + "}\n";
      s := s + "#[inline]\nfn unerase_owned(x: r#" + c.name + typeParams + ") -> Self {\n";
      s := s + "x\n";
      s := s + "}\n";
      s := s + "}\n";
      s := s + "impl " + constrainedTypeParams + " ::std::default::Default for r#" + c.name + typeParams + " {\n";
      s := s + "fn default() -> Self {\n";

      match c.witnessExpr {
        case Some(e) => {
          // TODO(shadaj): generate statements
          var eStr, _, _, _ := GenExpr(e, None, [], true);
          s := s + "r#" + c.name + "(" + eStr + ")\n";
        }
        case None => {
          s := s + "r#" + c.name + "(::std::default::Default::default())\n";
        }
      }

      s := s + "}\n";
      s := s + "}\n";
      s := s + "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyPrint for r#" + c.name + typeParams + " {\n";
      s := s + "fn fmt_print(&self, __fmt_print_formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {\n";
      s := s + "::dafny_runtime::DafnyPrint::fmt_print(&self.0, __fmt_print_formatter, in_seq)\n";
      s := s + "}\n";
      s := s + "}\n";
    }

    static method GenDatatype(c: Datatype) returns (s: string) {
      var typeParamsSet, typeParams, constrainedTypeParams := GenTypeParameters(c.typeParams);

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

            if |c.typeParams| > 0 {
              methodBody := methodBody + "r#" + c.name + "::_PhantomVariant(..) => panic!(),\n";
            }

            methodBody := methodBody + "}\n";

            implBody := implBody + "pub fn r#" + formal.name + "(&self) -> &" + formalType + " {\n" + methodBody + "}\n";
          }
          j := j + 1;
        }

        i := i + 1;
      }

      if |c.typeParams| > 0 {
        ctors := ctors + "_PhantomVariant(";
        var typeI := 0;
        while typeI < |c.typeParams| {
          if typeI > 0 {
            ctors := ctors + ", ";
          }

          var genTp := GenType(c.typeParams[typeI], false, false);
          ctors := ctors + "::std::marker::PhantomData::<" + genTp + ">";
          typeI := typeI + 1;
        }
        ctors := ctors + ")";
      }

      var enumBody := "#[derive(PartialEq)]\npub enum r#" + c.name + typeParams + " {\n" + ctors +  "\n}" + "\n" + "impl " + constrainedTypeParams + " r#" + c.name + typeParams + " {\n" + implBody + "\n}";

      var identEraseImpls := "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyErasable for r#" + c.name + typeParams + " {\n" + "type Erased = Self;\nfn erase(&self) -> &Self::Erased { self }\nfn erase_owned(self) -> Self::Erased { self }}\n";
      identEraseImpls := identEraseImpls + "impl " + constrainedTypeParams + " ::dafny_runtime::DafnyUnerasable<r#" + c.name + typeParams + "> for r#" + c.name + typeParams + " {\n" + "fn unerase(x: &Self) -> &Self { x }\nfn unerase_owned(x: Self) -> Self { x }}\n";

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

      if |c.typeParams| > 0 {
        printImpl := printImpl + "r#" + c.name + "::_PhantomVariant(..) => {panic!()\n}\n";
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

      s := enumBody + "\n" + identEraseImpls + "\n" + printImpl + "\n" + defaultImpl;
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
        case Nullable(inner) => {
          var innerStr := GenType(inner, inBinding, inFn);
          s := "::std::option::Option<" + innerStr + ">";
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
          s := "::std::rc::Rc<::std::cell::RefCell<::std::vec::Vec<" + elemStr + ">>>";
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
              s := "::dafny_runtime::FunctionWrapper<::std::boxed::Box<dyn ::std::ops::Fn(";
            } else {
              s := "::dafny_runtime::FunctionWrapper<impl ::std::ops::Fn(";
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
        case TypeArg(Ident(name)) => s := "r#" + name;
        case Primitive(p) => {
          match p {
            case Int => s := "::dafny_runtime::BigInt";
            case Real => s := "::dafny_runtime::BigRational";
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
          s := s + typeString + ": ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<" + typeString + "> + Clone + ::std::cmp::PartialEq + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static";

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

        var body, _ := GenStmts(m.body, if m.isStatic then None else Some("self"), paramNames, true, earlyReturn);
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

    static method GenStmts(stmts: seq<Statement>, selfIdent: Optional<string>, params: seq<string>, isLast: bool, earlyReturn: string) returns (generated: string, readIdents: set<string>) {
      generated := "";
      readIdents := {};
      var i := 0;
      while i < |stmts| {
        var stmt := stmts[i];
        var stmtString, recIdents := GenStmt(stmt, selfIdent, params, isLast && (i == |stmts| - 1), earlyReturn);
        readIdents := readIdents + recIdents;

        if i > 0 {
          generated := generated + "\n";
        }

        generated := generated + stmtString;
        i := i + 1;
      }
    }

    static method GenAssignLhs(lhs: AssignLhs, rhs: string, selfIdent: Optional<string>, params: seq<string>) returns (generated: string, needsIIFE: bool, readIdents: set<string>) {
      match lhs {
        case Ident(Ident(id)) => {
          if id in params {
            generated := "*r#" + id;
          } else {
            generated := "r#" + id;
          }

          readIdents := {id};
          needsIIFE := false;
        }

        case Select(on, field) => {
          var onExpr, onOwned, onErased, recIdents := GenExpr(on, selfIdent, params, false);
          if !onErased {
            var eraseFn := if onOwned then "erase_owned" else "erase";
            onExpr := "::dafny_runtime::DafnyErasable::" + eraseFn + "(" + onExpr + ")";
          }

          generated := "*(" + onExpr + "." + field + ".borrow_mut()) = " + rhs + ";";
          readIdents := recIdents;
          needsIIFE := true;
        }

        case Index(on, idx) => {
          var onExpr, onOwned, onErased, recIdents := GenExpr(on, selfIdent, params, false);
          if !onErased {
            var eraseFn := if onOwned then "erase_owned" else "erase";
            onExpr := "::dafny_runtime::DafnyErasable::" + eraseFn + "(" + onExpr + ")";
          }

          var idxString, _, idxErased, idxIdents := GenExpr(idx, selfIdent, params, true);
          if !idxErased {
            idxString := "::dafny_runtime::DafnyErasable::erase_owned(" + idxString + ")";
          }

          generated := "{\nlet __idx = <usize as ::dafny_runtime::NumCast>::from(" + idxString + ").unwrap();\n";
          generated := generated + onExpr + ".borrow_mut()[__idx] = " + rhs + ";\n}";
          readIdents := recIdents + idxIdents;
          needsIIFE := true;
        }
      }
    }

    static method GenStmt(stmt: Statement, selfIdent: Optional<string>, params: seq<string>, isLast: bool, earlyReturn: string) returns (generated: string, readIdents: set<string>) {
      match stmt {
        case DeclareVar(name, typ, Some(expression)) => {
          var expr, _, recErased, recIdents := GenExpr(expression, selfIdent, params, true);
          if recErased {
            expr := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + expr + ")";
          }

          var typeString := GenType(typ, true, false);
          generated := "let mut r#" + name + ": " + typeString + " = " + expr + ";";
          readIdents := recIdents;
        }
        case DeclareVar(name, typ, None) => {
          var typeString := GenType(typ, true, false);
          generated := "let mut r#" + name + ": " + typeString + ";";
          readIdents := {};
        }
        case Assign(lhs, expression) => {
          var lhsGen, needsIIFE, recIdents := GenAssignLhs(lhs, "__rhs", selfIdent, params);
          var exprGen, _, exprErased, exprIdents := GenExpr(expression, selfIdent, params, true);
          if exprErased {
            exprGen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + exprGen + ")";
          }

          if needsIIFE {
            generated := "{\nlet __rhs = " + exprGen + ";\n" + lhsGen + "\n}";
          } else {
            generated := lhsGen + " = " + exprGen + ";";
          }

          readIdents := recIdents + exprIdents;
        }
        case If(cond, thn, els) => {
          var condString, _, condErased, recIdents := GenExpr(cond, selfIdent, params, true);
          if !condErased {
            condString := "::dafny_runtime::DafnyErasable::erase_owned(" + condString + ")";
          }

          readIdents := recIdents;
          var thnString, thnIdents := GenStmts(thn, selfIdent, params, isLast, earlyReturn);
          readIdents := readIdents + thnIdents;
          var elsString, elsIdents := GenStmts(els, selfIdent, params, isLast, earlyReturn);
          readIdents := readIdents + elsIdents;
          generated := "if " + condString + " {\n" + thnString + "\n} else {\n" + elsString + "\n}";
        }
        case While(cond, body) => {
          var condString, _, condErased, recIdents := GenExpr(cond, selfIdent, params, true);
          if !condErased {
            condString := "::dafny_runtime::DafnyErasable::erase(" + condString + ")";
          }

          readIdents := recIdents;
          var bodyString, bodyIdents := GenStmts(body, selfIdent, params, false, earlyReturn);
          readIdents := readIdents + bodyIdents;
          generated := "while " + condString + " {\n" + bodyString + "\n}";
        }
        case TailRecursive(body) => {
          // clone the parameters to make them mutable
          generated := "";

          if selfIdent != None {
            generated := generated + "let mut r#_this = self.clone();\n";
          }

          var paramI := 0;
          while paramI < |params| {
            var param := params[paramI];
            generated := generated + "let mut r#" + param + " = r#" + param + ".clone();\n";
            paramI := paramI + 1;
          }

          var bodyString, bodyIdents := GenStmts(body, if selfIdent != None then Some("_this") else None, [], false, earlyReturn);
          readIdents := bodyIdents;
          generated := generated + "'TAIL_CALL_START: loop {\n" + bodyString + "\n}";
        }
        case JumpTailCallStart() => {
          generated := "continue 'TAIL_CALL_START;";
          readIdents := {};
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

            var argExpr, isOwned, argErased, argIdents := GenExpr(args[i], selfIdent, params, false);
            if isOwned {
              argExpr := "&" + argExpr;
            }

            argString := argString + argExpr;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var enclosingString, _, _, enclosingIdents := GenExpr(on, selfIdent, params, false);
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
          var exprString, _, recErased, recIdents := GenExpr(expr, selfIdent, params, true);
          exprString := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + exprString + ")";
          readIdents := recIdents;

          if isLast {
            generated := exprString;
          } else {
            generated := "return " + exprString + ";";
          }
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
          var printedExpr, isOwned, _, recIdents := GenExpr(e, selfIdent, params, false);
          generated := "print!(\"{}\", ::dafny_runtime::DafnyPrintWrapper(" + (if isOwned then "&" else "") + printedExpr + "));";
          readIdents := recIdents;
        }
      }
    }

    static method GenExpr(e: Expression, selfIdent: Optional<string>, params: seq<string>, mustOwn: bool) returns (s: string, isOwned: bool, isErased: bool, readIdents: set<string>)
      ensures mustOwn ==> isOwned
      decreases e {
      match e {
        case Literal(BoolLiteral(false)) => {
          s := "false";
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(BoolLiteral(true)) => {
          s := "true";
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(IntLiteral(i, t)) => {
          match t {
            case Primitive(Int) => {
              s := "::dafny_runtime::BigInt::parse_bytes(b\"" + i + "\", 10).unwrap()";
            }
            case _ => {
              s := i;
            }
          }

          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(DecLiteral(n, d, t)) => {
          match t {
            case Primitive(Real) => {
              s := "::dafny_runtime::BigRational::new(::dafny_runtime::BigInt::parse_bytes(b\"" + n + "\", 10).unwrap(), ::dafny_runtime::BigInt::parse_bytes(b\"" + d + "\", 10).unwrap())";
            }
            case _ => {
              s := n + ".0 / " + d + ".0";
            }
          }

          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(StringLiteral(l)) => {
          // TODO(shadaj): handle unicode properly
          s := "\"" + l + "\".chars().collect::<Vec<char>>()";
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(CharLiteral(c)) => {
          s := "::std::primitive::char::from_u32(" + natToString(c as nat) + ").unwrap()";
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Literal(Null) => {
          s := "None";
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case Ident(name) => {
          s := "r#" + name;
          if !(name in params) {
            s := "(&" + s + ")";
          }

          if mustOwn {
            s := s + ".clone()";
            isOwned := true;
          } else {
            isOwned := false;
          }

          isErased := false;

          readIdents := {name};
        }
        case Companion(path) => {
          s := GenPath(path);
          isOwned := true;
          isErased := true;
          readIdents := {};
        }
        case InitializationValue(typ) => {
          var typString := GenType(typ, false, false);
          s := "<" + typString + " as std::default::Default>::default()";
          isOwned := true;
          isErased := false;
          readIdents := {};
        }
        case Tuple(values) => {
          s := "(";
          readIdents := {};
          var i := 0;

          var allErased := true;
          while i < |values| {
            var _, _, isErased, _ := GenExpr(values[i], selfIdent, params, true);
            allErased := allErased && isErased;
            i := i + 1;
          }

          i := 0;
          while i < |values| {
            if i > 0 {
              s := s + " ";
            }

            var recursiveGen, _, isErased, recIdents := GenExpr(values[i], selfIdent, params, true);
            if isErased && !allErased {
              recursiveGen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + recursiveGen + ")";
            }

            s := s + recursiveGen + ",";
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + ")";
          isOwned := true;
          isErased := allErased;
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

            var recursiveGen, _, isErased, recIdents := GenExpr(args[i], selfIdent, params, true);
            if isErased {
              recursiveGen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + recursiveGen + ")";
            }
            s := s + recursiveGen;
            readIdents := readIdents + recIdents;

            i := i + 1;
          }
          s := s + "))";
          isOwned := true;
          isErased := true;
        }
        case NewArray(dims) => {
          var i := |dims| - 1;
          s := "::std::default::Default::default()";
          readIdents := {};
          while i >= 0 {
            var recursiveGen, _, isErased, recIdents := GenExpr(dims[i], selfIdent, params, true);
            if !isErased {
              recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
            }

            s := "::std::rc::Rc::new(::std::cell::RefCell::new(vec![" + s + "; <usize as ::dafny_runtime::NumCast>::from(" + recursiveGen + ").unwrap()]))";
            readIdents := readIdents + recIdents;

            i := i - 1;
          }

          isOwned := true;
          isErased := true;
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
              var recursiveGen, _, isErased, recIdents := GenExpr(value, selfIdent, [], true);
              if !isErased {
                recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
              }
              recursiveGen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + recursiveGen + ")";

              readIdents := readIdents + recIdents;
              var allReadCloned := "";
              while recIdents != {} decreases recIdents {
                var next: string :| next in recIdents;
                allReadCloned := allReadCloned + "let r#" + next + " = r#" + next + ".clone();\n";
                recIdents := recIdents - {next};
              }
              s := s + "r#" + name + ": ::dafny_runtime::LazyFieldWrapper(::dafny_runtime::Lazy::new(::std::boxed::Box::new({\n" + allReadCloned + "move || (" + recursiveGen + ")})))";
            } else {
              var recursiveGen, _, isErased, recIdents := GenExpr(value, selfIdent, params, true);
              if !isErased {
                recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
              }
              recursiveGen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + recursiveGen + ")";

              s := s + "r#" + name + ": " + "(" + recursiveGen + ")";
              readIdents := readIdents + recIdents;
            }
            i := i + 1;
          }
          s := s + " })";
          isOwned := true;
          isErased := true;
        }
        case Convert(expr, fromTpe, toTpe) => {
          if fromTpe == toTpe {
            var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
            s := recursiveGen;
            isOwned := recOwned;
            isErased := recErased;
            readIdents := recIdents;
          } else {
            match (fromTpe, toTpe) {
              case (Nullable(_), _) => {
                var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                if !recOwned {
                  recursiveGen := recursiveGen + ".as_ref()";
                }

                s := recursiveGen + ".unwrap()";
                isOwned := recOwned;
                isErased := recErased;
                readIdents := recIdents;
              }
              case (_, Nullable(_)) => {
                var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                if !recOwned {
                  recursiveGen := recursiveGen + ".clone()";
                }

                s := "Some(" + recursiveGen + ")";
                isOwned := true;
                isErased := recErased;
                readIdents := recIdents;
              }
              case (_, Path(_, _, Newtype(b))) => {
                if fromTpe == b {
                  var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);

                  var rhsType := GenType(toTpe, true, false);

                  var uneraseFn := if recOwned then "unerase_owned" else "unerase";
                  s := "<" + rhsType + " as ::dafny_runtime::DafnyUnerasable<_>>::" + uneraseFn + "(" + recursiveGen + ")";
                  isOwned := recOwned;
                  isErased := false;
                  readIdents := recIdents;
                } else {
                  assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
                  s, isOwned, isErased, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, mustOwn);
                }
              }
              case (Path(_, _, Newtype(b)), _) => {
                if b == toTpe {
                  var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                  var uneraseFn := if recOwned then "erase_owned" else "erase";
                  s := "::dafny_runtime::DafnyErasable::" + uneraseFn + "(" + recursiveGen + ")";
                  isOwned := recOwned;
                  isErased := true;
                  readIdents := recIdents;
                } else {
                  assume {:axiom} Convert(Convert(expr, fromTpe, b), b, toTpe) < e; // make termination go through
                  s, isOwned, isErased, readIdents := GenExpr(Convert(Convert(expr, fromTpe, b), b, toTpe), selfIdent, params, mustOwn);
                }
              }
              case (Primitive(Int), Primitive(Real)) => {
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                s := "::dafny_runtime::BigRational::from_integer(" + recursiveGen + ")";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Primitive(Real), Primitive(Int)) => {
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, false);
                s := "::dafny_runtime::dafny_rational_to_int(" + recursiveGen + ")";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Primitive(Int), Passthrough(_)) => {
                var rhsType := GenType(toTpe, true, false);
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                s := "<" + rhsType + " as ::dafny_runtime::NumCast>::from(" + recursiveGen + ").unwrap()";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Passthrough(_), Primitive(Int)) => {
                var rhsType := GenType(fromTpe, true, false);
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                s := "::dafny_runtime::BigInt::from(" + recursiveGen + ")";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Primitive(Int), Primitive(Char)) => {
                var rhsType := GenType(toTpe, true, false);
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                s := "char::from_u32(<u32 as ::dafny_runtime::NumCast>::from(" + recursiveGen + ").unwrap()).unwrap()";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Primitive(Char), Primitive(Int)) => {
                var rhsType := GenType(fromTpe, true, false);
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                s := "::dafny_runtime::BigInt::from(" + recursiveGen + " as u32)";
                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case (Passthrough(_), Passthrough(_)) => {
                var recursiveGen, _, _, recIdents := GenExpr(expr, selfIdent, params, true);
                var toTpeGen := GenType(toTpe, true, false);

                s := "((" + recursiveGen + ") as " + toTpeGen + ")";

                isOwned := true;
                isErased := true;
                readIdents := recIdents;
              }
              case _ => {
                var recursiveGen, recOwned, recErased, recIdents := GenExpr(expr, selfIdent, params, mustOwn);
                s := "(" + recursiveGen + "/* conversion not yet implemented */)";
                isOwned := recOwned;
                isErased := recErased;
                readIdents := recIdents;
              }
            }
          }
        }
        case SeqValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          var allErased := true;
          while i < |exprs| {
            var recursiveGen, _, isErased, recIdents := GenExpr(exprs[i], selfIdent, params, true);
            allErased := allErased && isErased;

            generatedValues := generatedValues + [(recursiveGen, isErased)];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }

          s := "vec![";
          i := 0;
          while i < |generatedValues| {
            if i > 0 {
              s := s + ", ";
            }

            var gen := generatedValues[i].0;
            if generatedValues[i].1 && !allErased {
              gen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + gen + ")";
            }

            s := s + gen;
            i := i + 1;
          }
          s := s + "]";

          isOwned := true;
          isErased := allErased;
        }
        case SetValue(exprs) => {
          var generatedValues := [];
          readIdents := {};
          var i := 0;
          var allErased := true;
          while i < |exprs| {
            var recursiveGen, _, isErased, recIdents := GenExpr(exprs[i], selfIdent, params, true);
            allErased := allErased && isErased;

            generatedValues := generatedValues + [(recursiveGen, isErased)];
            readIdents := readIdents + recIdents;
            i := i + 1;
          }

          s := "vec![";
          i := 0;
          while i < |generatedValues| {
            if i > 0 {
              s := s + ", ";
            }

            var gen := generatedValues[i].0;
            if generatedValues[i].1 && !allErased {
              gen := "::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(" + gen + ")";
            }

            s := s + gen;
            i := i + 1;
          }
          s := s + "].into_iter().collect::<std::collections::HashSet<_>>()";

          isOwned := true;
          isErased := true;
        }
        case This() => {
          match selfIdent {
            case Some(id) => {
              if mustOwn {
                s := id + ".clone()";
                isOwned := true;
              } else {
                if id == "self" {
                  s := "self";
                } else {
                  s := "&" + id;
                }
                isOwned := false;
              }

              readIdents := {id};
              isErased := false;
            }
            case None => {
              s := "panic!(\"this outside of a method\")";
              isOwned := true;
              readIdents := {};
              isErased := true;
            }
          }
        }
        case Ite(cond, t, f) => {
          var condString, _, condErased, recIdentsCond := GenExpr(cond, selfIdent, params, true);
          if !condErased {
            condString := "::dafny_runtime::DafnyErasable::erase_owned(" + condString + ")";
          }

          var _, tHasToBeOwned, _, _ := GenExpr(t, selfIdent, params, mustOwn); // check if t has to be owned even if not requested
          var fString, fOwned, fErased, recIdentsF := GenExpr(f, selfIdent, params, tHasToBeOwned);
          var tString, _, tErased, recIdentsT := GenExpr(t, selfIdent, params, fOwned); // there's a chance that f forced ownership

          if !fErased || !tErased {
            if fErased {
              fString := "::dafny_runtime::DafnyErasable::erase_owned(" + fString + ")";
            }

            if tErased {
              tString := "::dafny_runtime::DafnyErasable::erase_owned(" + tString + ")";
            }
          }

          s := "(if " + condString + " {\n" + tString + "\n} else {\n" + fString + "\n})";
          isOwned := fOwned;
          readIdents := recIdentsCond + recIdentsT + recIdentsF;
          isErased := fErased || tErased;
        }
        case UnOp(Not, e) => {
          var recursiveGen, _, recErased, recIdents := GenExpr(e, selfIdent, params, true);
          if !recErased {
            recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
          }

          s := "!(" + recursiveGen + ")";
          isOwned := true;
          readIdents := recIdents;
          isErased := true;
        }
        case UnOp(BitwiseNot, e) => {
          var recursiveGen, _, recErased, recIdents := GenExpr(e, selfIdent, params, true);
          if !recErased {
            recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
          }

          s := "~(" + recursiveGen + ")";
          isOwned := true;
          readIdents := recIdents;
          isErased := true;
        }
        case UnOp(Cardinality, e) => {
          var recursiveGen, recOwned, recErased, recIdents := GenExpr(e, selfIdent, params, false);
          if !recErased {
            var eraseFn := if recOwned then "erase_owned" else "erase";
            recursiveGen := "::dafny_runtime::DafnyErasable::" + eraseFn + "(" + recursiveGen + ")";
          }

          s := "::dafny_runtime::BigInt::from((" + recursiveGen + ").len())";
          isOwned := true;
          readIdents := recIdents;
          isErased := true;
        }
        case BinOp(op, l, r) => {
          var left, _, leftErased, recIdentsL := GenExpr(l, selfIdent, params, true);
          var right, _, rightErased, recIdentsR := GenExpr(r, selfIdent, params, true);

          if !leftErased {
            left := "::dafny_runtime::DafnyErasable::erase_owned(" + left + ")";
          }

          if !rightErased {
            right := "::dafny_runtime::DafnyErasable::erase_owned(" + right + ")";
          }

          if op == "/" {
            s := "::dafny_runtime::euclidian_division(" + left + ", " + right + ")";
          } else if op == "%" {
            s := "::dafny_runtime::euclidian_modulo(" + left + ", " + right + ")";
          } else {
            s := "(" + left + " " + op + " " + right + ")";
          }

          isOwned := true;
          readIdents := recIdentsL + recIdentsR;
          isErased := true;
        }
        case ArrayLen(expr) => {
          var recursiveGen, _, recErased, recIdents := GenExpr(expr, selfIdent, params, true);
          if !recErased {
            recursiveGen := "::dafny_runtime::DafnyErasable::erase_owned(" + recursiveGen + ")";
          }

          s := "::dafny_runtime::BigInt::from((" + recursiveGen + ").borrow().len())";
          isOwned := true;
          readIdents := recIdents;
          isErased := true;
        }
        case SelectFn(on, field, isDatatype, isStatic, arity) => {
          var onString, onOwned, _, recIdents := GenExpr(on, selfIdent, params, false);

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
          isErased := true;
          readIdents := recIdents;
        }
        case Select(on, field, isConstant, isDatatype) => {
          var onString, onOwned, onErased, recIdents := GenExpr(on, selfIdent, params, false);
          if !onErased {
            var eraseFn := if onOwned then "erase_owned" else "erase";
            onString := "::dafny_runtime::DafnyErasable::" + eraseFn + "(" + onString + ")";
          }

          if isDatatype || isConstant {
            s := "(" + onString + ")" + ".r#" + field + "()";
            if isConstant {
              s := "&" + s;
            }

            if mustOwn {
              s := "(" + s + ").clone()";
              isOwned := true;
            } else {
              isOwned := false;
            }
          } else {
            s := "::std::ops::Deref::deref(&((" + onString + ")" + ".r#" + field + ".borrow()))";
            s := "(" + s + ").clone()"; // TODO(shadaj): think through when we can avoid cloning
            isOwned := true;
          }

          isErased := false;
          readIdents := recIdents;
        }
        case Index(on, idx) => {
          var onString, onOwned, onErased, recIdents := GenExpr(on, selfIdent, params, false);
          if !onErased {
            var eraseFn := if onOwned then "erase_owned" else "erase";
            onString := "::dafny_runtime::DafnyErasable::" + eraseFn + "(" + onString + ")";
          }

          var idxString, _, idxErased, recIdentsIdx := GenExpr(idx, selfIdent, params, true);
          if !idxErased {
            idxString := "::dafny_runtime::DafnyErasable::erase_owned(" + idxString + ")";
          }

          s := "(" + onString + ")" + "[<usize as ::dafny_runtime::NumCast>::from(" + idxString + ").unwrap()]";
          if mustOwn {
            s := "(" + s + ").clone()";
            isOwned := true;
          } else {
            s := "(&" + s + ")";
            isOwned := false;
          }

          isErased := true;
          readIdents := recIdents + recIdentsIdx;
        }
        case TupleSelect(on, idx) => {
          var onString, _, tupErased, recIdents := GenExpr(on, selfIdent, params, false);
          s := "(" + onString + ")." + natToString(idx);
          if mustOwn {
            s := "(" + s + ")" + ".clone()";
            isOwned := true;
          } else {
            s := "&" + s;
            isOwned := false;
          }
          isErased := tupErased;
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

            var argExpr, isOwned, argErased, argIdents := GenExpr(args[i], selfIdent, params, false);
            if isOwned {
              argExpr := "&" + argExpr;
            }

            argString := argString + argExpr;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          var enclosingString, _, _, recIdents := GenExpr(on, selfIdent, params, false);
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
          isErased := false;
        }
        case Lambda(params, retType, body) => {
          var paramNames := [];
          var i := 0;
          while i < |params| {
            paramNames := paramNames + [params[i].name];
            i := i + 1;
          }

          var recursiveGen, recIdents := GenStmts(body, None, paramNames, true, "");
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

          var retTypeGen := GenType(retType, false, true);

          s := "::dafny_runtime::FunctionWrapper({\n" + allReadCloned + "::std::boxed::Box::new(move |" + paramsString + "| -> " + retTypeGen + " {\n" + recursiveGen + "\n})})";
          isOwned := true;
          isErased := true;
        }
        case IIFE(name, tpe, value, iifeBody) => {
          var valueGen, valueOwned, valueErased, recIdents := GenExpr(value, selfIdent, params, false);
          if valueErased {
            var eraseFn := if valueOwned then "unerase_owned" else "unerase";
            valueGen := "::dafny_runtime::DafnyUnerasable::<_>::" + eraseFn + "(" + valueGen + ")";
          }

          readIdents := recIdents;
          var valueTypeGen := GenType(tpe, false, true);
          var bodyGen, bodyOwned, bodyErased, bodyIdents := GenExpr(iifeBody, selfIdent, params + if valueOwned then [] else [name.id], mustOwn);
          readIdents := readIdents + bodyIdents;

          var eraseFn := if valueOwned then "unerase_owned" else "unerase";

          s := "{\nlet r#" + name.id + ": " + (if valueOwned then "" else "&") + valueTypeGen + " = " + valueGen + ";\n" + bodyGen + "\n}";
          isOwned := bodyOwned;
          isErased := bodyErased;
        }
        case Apply(func, args) => {
          var funcString, _, funcErased, recIdents := GenExpr(func, selfIdent, params, false);
          readIdents := recIdents;

          var argString := "";
          var i := 0;
          while i < |args| {
            if i > 0 {
              argString := argString + ", ";
            }

            var argExpr, isOwned, argErased, argIdents := GenExpr(args[i], selfIdent, params, false);
            if isOwned {
              argExpr := "&" + argExpr;
            }

            argString := argString + argExpr;
            readIdents := readIdents + argIdents;

            i := i + 1;
          }

          s := "((" + funcString + ").0" + "(" + argString + "))";
          isOwned := true;
          isErased := false;
        }
        case TypeTest(on, dType, variant) => {
          var exprGen, _, exprErased, recIdents := GenExpr(on, selfIdent, params, false);
          var dTypePath := GenPath(dType);
          s := "matches!(" + exprGen + ".as_ref(), " + dTypePath + "::r#" + variant + "{ .. })";
          isOwned := true;
          isErased := true;
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
