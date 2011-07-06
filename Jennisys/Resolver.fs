module Resolver

open Ast
open Printer
open EnvUtils

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
      let resolvedLst = cseq |> List.rev |> List.fold (fun acc cOpt ->
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

let rec EvalUnresolved expr (heap,env,ctx) = 
  match expr with
  | IntLiteral(n) -> IntConst(n)
  | IdLiteral(id) when id = "this" -> GetThisLoc env
  | IdLiteral(id) -> EvalUnresolved (Dot(IdLiteral("this"), id)) (heap,env,ctx)
  | Dot(e, str) -> 
      let discr = EvalUnresolved e (heap,env,ctx)
      let h2 = Map.filter (fun (loc,Var(fldName,_)) v -> loc = discr && fldName = str) heap |> Map.toList
      match h2 with
      | ((_,_),x) :: [] -> x
      | _ :: _ -> failwithf "can't evaluate expression deterministically: %s.%s resolves to multiple locations." (PrintConst discr) str
      | [] -> failwithf "can't find value for %s.%s" (PrintConst discr) str
  | _ -> failwith "NOT IMPLEMENTED YET" //TODO finish this!
//  | Star         
//  | SelectExpr(_)   
//  | UpdateExpr(_)   
//  | SequenceExpr(_) 
//  | SeqLength(_)    
//  | ForallExpr(_)   
//  | UnaryExpr(_)   
//  | BinaryExpr(_)

let Eval expr (heap,env,ctx) = 
  try 
    let unresolvedConst = EvalUnresolved expr (heap,env,ctx)
    Some(Resolve unresolvedConst (env,ctx))
  with
    ex -> None