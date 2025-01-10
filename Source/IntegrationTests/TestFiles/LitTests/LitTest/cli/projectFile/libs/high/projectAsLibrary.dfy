// RUN: %resolve --library "%S/../mid/dfyconfig.toml" --library %S/../low/wrappersLib.dfy --allow-warnings --function-syntax 3 %s > "%t"
// RUN: ! %resolve --library "%S/../mid/dfyconfig.toml" --library %S/../low/wrappersLib.dfy --allow-warnings --function-syntax 3 --unicode-char false %s >> "%t"
// RUN: %verify --library "%S/../mid/dfyconfig.toml" --library %S/../low/wrappersLib.dfy --dont-verify-dependencies --allow-warnings --function-syntax 3 %s >> "%t"
// RUN: ! %verify --library "%S/../mid/dfyconfig.toml" --library %S/../low/wrappersLib.dfy --verbose --allow-warnings --function-syntax 3 %s >> "%t"
// RUN: %verify --library "%S/../safeMid/dfyconfig.toml" --library %S/../low/wrappersLib.dfy --verbose --allow-warnings --function-syntax 3 %s >> "%t"
// RUN: %diff "%s.expect" "%t"

module ConsumerConsumer {
  import opened Consumer
  import opened Wrappers

  function UsesMaybeInt(): Option<int> {
    MaybeInt()
  }
}