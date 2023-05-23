// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// test various compiler-target keywords

datatype struct = S  // C# keyword
datatype byte = arguments  // JavaScript keyword

method Main()
{
  var s := S;
  var t: struct;
  var b := arguments;
  print s, " ", b, "\n";

  var ref: enum.goto, transient: enum.goto;
  ref := enum.switch;
  transient := enum.do();
  print ref, " ", transient, "\n";

  var params := catch(20);
  var final := enum.catch(params);
  var procedure := params + final;  // Boogie keyword
  print params, " + ", final, " == ", procedure, "\n";
}

method catch(do: int) returns (finally: int) {
  finally := do;
}

module enum {
  datatype goto = switch
  function do(): goto {
    switch
  }
  method catch(do: int) returns (finally: int) {
    finally := do;
  }
}
