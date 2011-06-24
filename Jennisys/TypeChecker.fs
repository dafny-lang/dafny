module TypeChecker

open Ast
open System.Collections.Generic

let GetClass name decls =
  match decls |> List.tryFind (function Class(n,_,_) when n = name -> true | _ -> false) with
    | Some(cl) -> cl
    | None -> Class(name,[],[])

let GetModel name decls =
  match decls |> List.tryFind (function Model(n,_,_,_,_) when n = name -> true | _ -> false) with
    | Some(m) -> m
    | None -> Model(name,[],[],[],IdLiteral("true"))

let GetCode name decls =
  match decls |> List.tryFind (function Code(n,_) when n = name -> true | _ -> false) with
    | Some(c) -> c
    | None -> Code(name,[])

let IsUserType prog tpo =
  match tpo with
    | Some(tp) ->
        let tpname = match tp with
                       | NamedType(tname) -> tname
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

// resolving values
 
let rec Resolve cst (env,ctx) =
  match cst with
  | Unresolved(_) as u -> 
      // see if it is in the env map first
      let envVal = Map.tryFind cst env
      match envVal with
      | Some(c) -> Resolve c (env,ctx)
      | None -> 
          // not found in the env map --> check the equality sets
          let eq = ctx |> Set.filter (fun eqSet -> Set.contains u eqSet)
                       |> Utils.SetToOption
          match eq with 
          | Some(eqSet) -> 
              let cOpt = eqSet |> Set.filter (function Unresolved(_) -> false | _ -> true)
                               |> Utils.SetToOption
              match cOpt with 
              | Some(c) -> c
              | _ -> failwith ("failed to resolve " + cst.ToString())
          | _ -> failwith ("failed to resolve " + cst.ToString())
  | SeqConst(cseq) -> 
      let resolvedLst = cseq |> List.fold (fun acc cOpt ->
                                             match cOpt with
                                             | Some(c) -> Some(Resolve c (env,ctx)) :: acc 
                                             | None -> cOpt :: acc
                                          ) []
      SeqConst(resolvedLst)
  | SetConst(cset) ->
      let resolvedSet = cset |> Set.fold (fun acc cOpt ->
                                            match cOpt with
                                            | Some(c) -> acc |> Set.add (Some(Resolve c (env,ctx)))
                                            | None -> acc |> Set.add(cOpt)
                                          ) Set.empty
      SetConst(resolvedSet)
  | _ -> cst
