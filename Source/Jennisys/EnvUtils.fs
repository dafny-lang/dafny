module EnvUtils

open Ast

let GetThisLoc env = 
  Map.findKey (fun k v -> 
                 match v with
                 | ThisConst(_) -> true
                 | _ -> false) env