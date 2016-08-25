module SymGen

let incr =
  let counter = ref 0
  fun () ->
    counter := !counter + 1
    !counter

let NewSymFake expr = sprintf "x_%d" (incr())