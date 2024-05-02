// RUN: %resolve --library "%S/dfyconfig.toml" --library %S/wrappersLib.dfy --allow-warnings --function-syntax 3 %s > "%t"
// RUN: ! %verify --library "%S/dfyconfig.toml" --library %S/wrappersLib.dfy --allow-warnings --function-syntax 3 --unicode-char false %s >> "%t"
// RUN: %verify --unsafe-dependencies --library "%S/dfyconfig.toml" --library %S/wrappersLib.dfy --allow-warnings --function-syntax 3 --unicode-char false %s >> "%t"
// RUN: %resolve --library "%S/dfyconfig.toml" --library %S/wrappersLib.dfy --allow-warnings --function-syntax 3 --unicode-char false %s >> "%t"
// RUN: %diff "%s.expect" "%t"

module ConsumerConsumer {
  import opened Consumer
  import opened Wrappers

  function UsesMaybeInt(): Option<int> {
    MaybeInt()
  }
}