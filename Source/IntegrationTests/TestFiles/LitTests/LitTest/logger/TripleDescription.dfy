// RUN: %exits-with 4 %baredafny verify --show-snippets:false --log-format:text "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Outcome: Invalid
// CHECK: TripleDescription.dfy(.*,.*): this postcondition holds
method BadAbs(x: int) returns (r: int)
  ensures r > 0
{
    if(x < 0) {
        return -x;
    } else {
        return x;
    }
}
