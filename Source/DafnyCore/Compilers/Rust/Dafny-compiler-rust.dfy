include "../Dafny/AST.dfy"

module {:extern "DCOMP"} DCOMP {

  import opened DAST

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
      s := "pub fn " + m.name + "(" + "" + ") {" + body + "}\n";
    }

    static method GenStmts(body: seq<Statement>) returns (s: string) {
      s := "";
      var i := 0;
      while i < |body| {
        var generated: string;
        match body[i] {
          case Print(e) => generated := "println!(\"{:?}\", " + GenExpr(e) + ");";
          case _ => generated := "TODO";
        }

        if i > 0 {
           s := s + "\n";
        }

        s := s + generated;
        i := i + 1;
      }
    }

    static function GenExpr(e: Expression): string {
      match e {
        case Literal(StringLiteral(s)) => s
        case _ => "TODO"
      }
    }
		
    static method Compile(p: seq<TopLevel>) returns (s: string) {
      s := "#![allow(warnings)]\n";
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