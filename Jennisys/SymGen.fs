module SymGen

let cnt = ref 0

let NewSym = 
  let sym = sprintf "x_%d" !cnt
  cnt := !cnt + 1
  sym
   