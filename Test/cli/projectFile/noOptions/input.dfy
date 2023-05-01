// RUN: %baredafny resolve %args "%S/dfyconfig.toml" > "%t"
// RUN: %diff "%s.expect" "%t"

module NoOptions {
  method Main() {
    print "Hello, world!\n";
  }
}