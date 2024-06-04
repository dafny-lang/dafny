// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

function Loop(xs: seq<()>): ()
{
  if |xs| == 0
  then ()
  else
    var _: bool -> bool := e => e;
    Loop(xs[1..])
}

method Main(){
    print Loop([(), ()]), "\n";
}