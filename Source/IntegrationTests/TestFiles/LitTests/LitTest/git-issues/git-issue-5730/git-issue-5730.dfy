// RUN: %exits-with -any %verify "%S/dfyconfig.toml" > "%t"
// RUN: %diff "%s.expect" "%t"

module X {
  @VerifyOnly method VerifyMe() {
    assert false; // Should display an error
  }
  method DontVerifyMe() {
    assert false; // Should not show any error
  }
}
