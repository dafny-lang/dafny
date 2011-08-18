module TypeChecker

open Ast
open AstUtils
open Printer
open System.Collections.Generic

let GetClass name decls =
  match decls |> List.tryFind (function Class(n,_,_) when n = name -> true | _ -> false) with
  | Some(cl) -> cl
  | None -> Class(name,[],[])

let GetModel name decls =
  match decls |> List.tryFind (function Model(n,_,_,_,_) when n = name -> true | _ -> false) with
  | Some(m) -> m
  | None -> Model(name,[],[],[],BoolLiteral(true))

let GetCode name decls =
  match decls |> List.tryFind (function Code(n,_) when n = name -> true | _ -> false) with
  | Some(c) -> c
  | None -> Code(name,[])

let IsUserType prog tpo =
  match tpo with
  | Some(tp) ->
      let tpname = match tp with
                   | NamedType(tname,_) -> tname
                   | InstantiatedType(tname, _) -> tname
                   | _ -> ""
      match prog with
      | Program(components) -> components |> List.filter (function Component(Class(name,_,_),_,_) when name = tpname -> true
                                                                   | _                                               -> false) |> List.isEmpty |> not
  | None -> false

let TypeCheck prog =
  match prog with
  | SProgram(decls) ->
      let componentNames = decls |> List.choose (function Class(name,_,_) -> Some(name) | _ -> None)
      let clist = componentNames |> List.map (fun name -> Component(GetClass name decls, GetModel name decls, GetCode name decls))
      Some(Program(clist))

// TODO: implement this
let rec InferType prog thisComp expr = 
  let __FindVar comp fldName = 
    let var = FindVar comp fldName |> Utils.ExtractOption
    match var with
    | Var(_, tyOpt) -> 
        let c = FindComponentForType prog (Utils.ExtractOption tyOpt) |> Utils.ExtractOption
        Some(c)
  try 
    match expr with
    | ObjLiteral("this") -> Some(thisComp)
    | ObjLiteral("null") -> None
    | IdLiteral(id) -> __FindVar thisComp id
    | Dot(discr, fldName) -> 
        match InferType prog thisComp discr with
        | Some(comp) -> __FindVar comp fldName
        | None -> None
    | _ -> None
  with 
  | ex -> None