// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --type-system-refresh=false --allow-external-contracts

include "../../libraries/src/MutableMap/MutableMap.dfy"
import opened DafnyLibraries

method Main() {
  var m: MutableMap<nat, nat> := new MutableMap(true);
}
