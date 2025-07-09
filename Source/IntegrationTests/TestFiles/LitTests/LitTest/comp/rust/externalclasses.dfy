// NONUNIFORM: Rust-specific tests. Extern abstract types only compile with the Rust compiler for now.
// RUN: %baredafny run --target=rs --general-traits=legacy --enforce-determinism --input "%S/externalclasses.rs" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "External.Class.Container"} ExternalClassContainer {
  @NativeUInt64
  newtype u64 = x : int | 0 <= x <= 0xFFFF_FFFF_FFFF_FFFF

  class {:extern} ExternalClass {
    constructor {:extern} (i: int)
  }
  method {:extern} Test() returns (i: int)
  trait GetValueHolder {
    function GetValue(): int
  }

  class {:extern} ExternalPartialClass extends GetValueHolder {
    constructor {:extern} ()
    function {:extern} GetValue(): int
    method Print() {
      print GetValue();
    }
  }
  class {:extern} ExternalPartialClass2 extends GetValueHolder {
    constructor {:extern} ()
    function GetValue(): int {
      2
    }
    method Print() {
      print GetValue();
    }
  }
  
  type {:extern "StringWrapper"} RustString {
    ghost const s: string
    static function from_char(s: char): RustString
    function concat(other: RustString): RustString
    function length_bytes(): u64
  }
}

module Dafny.FileIO {
  method ReadBytesFromFile(path: string) returns (res: string) {
    res := INTERNAL_ReadBytesFromFile(path);
    INTERNAL_WriteBytesToFile(path, res);
  }

  method {:extern "DafnyLibraries.FileIO", "INTERNAL_WriteBytesToFile"}
  INTERNAL_WriteBytesToFile(path: string, content: string)
  
  function {:extern "DafnyLibraries.FileIO", "INTERNAL_ReadBytesFromFile"}
  INTERNAL_ReadBytesFromFile(path: string): (bytes: string)
}

module {:extern} ExternButEverythingImplemented {
  function test(): int { 1 }
}

module {:extern "ExternWithOnlyAStaticMethodUninmplemented"} ExternWithOnlyAStaticMethodUninmplemented {
  method {:extern} DoThis(i: int) returns (res: int)
}

module {:extern "ExternModuleWithOneClassToImport"} ExternModuleWithOneClassToImport {
  trait {:termination false} TraitDefinedInModule {
    function Get(): string
      reads this

    method Put(s: string)
      modifies this
      ensures this.Get() == s
  }

  class {:extern} NonShareableBox extends TraitDefinedInModule {
    constructor {:extern} {:axiom} ()
      ensures this.Get() == ""

    function {:extern} Get(): string
      reads this

    method {:extern} {:axiom} Put(s: string)
      modifies this
      ensures this.Get() == s

    function GetOpt(): (o: string)
      reads this
    {
      if Get() == "" then "None" else "Some("+Get()+")"
    }
  }
}


method Main() {
  var i := ExternalClassContainer.Test();
  expect i == 2;
  var j := new ExternalClassContainer.ExternalClass(i);
  var message := Dafny.FileIO.ReadBytesFromFile("hello.dfy");
  var c := new ExternalClassContainer.ExternalPartialClass();
  c.Print();
  var c2 := new ExternalClassContainer.ExternalPartialClass2();
  c2.Print();
  expect ExternButEverythingImplemented.test() == 1;
  var x := ExternWithOnlyAStaticMethodUninmplemented.DoThis(1);
  expect x == 2;
  var n: ExternModuleWithOneClassToImport.NonShareableBox := new ExternModuleWithOneClassToImport.NonShareableBox();
  expect n as object as ExternModuleWithOneClassToImport.NonShareableBox == n;
  expect n.Get() == "";
  expect n.GetOpt() == "None";
  n.Put("x");
  expect n.Get() == "x";
  expect n.GetOpt() == "Some(x)";
  var a := ExternalClassContainer.RustString.from_char('a');
  expect a.length_bytes() == 1;
  a := a.concat(a);
  expect a.length_bytes() == 2;
  print message;
}
