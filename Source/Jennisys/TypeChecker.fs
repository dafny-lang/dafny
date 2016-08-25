module TypeChecker

open Ast
open Getters
open AstUtils
open Printer
open System.Collections.Generic

let GetClass name decls =
  match decls |> List.tryFind (function Interface(n,_,_) when n = name -> true | _ -> false) with
  | Some(cl) -> cl
  | None -> Interface(name,[],[])

let GetModel name decls =
  match decls |> List.tryFind (function DataModel(n,_,_,_,_) when n = name -> true | _ -> false) with
  | Some(m) -> m
  | None -> DataModel(name,[],[],[],BoolLiteral(true))

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
      | Program(components) -> components |> List.filter (function Component(Interface(name,_,_),_,_) when name = tpname -> true
                                                                   | _                                               -> false) |> List.isEmpty |> not
  | None -> false

let TypeCheck prog =
  match prog with
  | SProgram(decls) ->
      let componentNames = decls |> List.choose (function Interface(name,_,_) -> Some(name) | _ -> None)
      let clist = componentNames |> List.map (fun name -> Component(GetClass name decls, GetModel name decls, GetCode name decls))
      Some(Program(clist))

let MethodArgChecker prog meth varName = 
  let ins = GetMethodInArgs meth
  let outs = GetMethodOutArgs meth
  ins @ outs |> List.choose (fun var -> if GetVarName var = varName then GetVarType var |> FindComponentForTypeOpt prog else None) |> Utils.ListToOption

// TODO: implement this
let rec InferType prog thisComp checkLocalFunc expr = 
  let __FindVar comp fldName = 
    let var = FindVar comp fldName |> Utils.ExtractOption
    let c = FindComponentForType prog (Utils.ExtractOption (GetVarType var)) |> Utils.ExtractOption
    Some(c)
    
  try 
    match expr with
    | ObjLiteral("this") -> Some(thisComp)
    | ObjLiteral("null") -> None
    | IdLiteral(id) -> __FindVar thisComp id
    | VarLiteral(id) -> checkLocalFunc id
    | Dot(discr, fldName) -> 
        match InferType prog thisComp checkLocalFunc discr with
        | Some(comp) -> __FindVar comp fldName
        | None -> None                        
    | _ -> None
  with 
  | ex -> None