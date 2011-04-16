module TypeChecker

open Ast
open System.Collections.Generic

let GetClass name decls =
  match decls |> List.tryFind (function Class(_,_,_) -> true | _ -> false) with
    | Some(cl) -> cl
    | None -> Class(name,[],[])

let GetModel name decls =
  match decls |> List.tryFind (function Model(_,_,_,_,_) -> true | _ -> false) with
    | Some(m) -> m
    | None -> Model(name,[],[],[],IdLiteral("true"))

let GetCode name decls =
  match decls |> List.tryFind (function Code(_,_) -> true | _ -> false) with
    | Some(c) -> c
    | None -> Code(name,[])

let TypeCheck prog =
  match prog with
  | SProgram(decls) ->
      let componentNames = decls |> List.choose (function Class(name,_,_) -> Some(name) | _ -> None)
      let clist = componentNames |> List.map (fun name -> Component(GetClass name decls, GetModel name decls, GetCode name decls))
      Some(Program(clist))
