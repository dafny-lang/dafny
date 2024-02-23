// RUN: %testDafnyForEachCompiler "%s"

function True(): bool {
  if false 
    then false
    else if (_ => false)(false)
      then false 
      else true
}

method Main(){
    print True(), "\n";
}
