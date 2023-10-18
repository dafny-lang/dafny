// RUN: echo 'lit should ignore this file'


method Main() {
  InDefaultModule();
  var x := new SomeModule.ClassInSomeModule();
  print x.x;
}

method InDefaultModule() {
  var x := 3;
}

class ClassInDefaultModule { // Extern does not work in JS {:extern "ClassInDefaultModuleCustomName" } 
  const x: int := 3 
}

module SomeModule { // Extern does not work in JS  {:extern "SomeModuleCustomName" } 
  method InSomeModule() {
    var x := 3;
  } 
  class ClassInSomeModule { // Extern does not work in JS {:extern "ClassInSomeModuleCustomName" } 
    const x := 3
    
    constructor() { }
  }
}