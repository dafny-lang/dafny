module Resolver

open Ast
open Printer
open EnvUtils

// resolving values
exception ConstResolveFailed of string
 
let rec ResolveCont cst (env,ctx) failResolver =
  match cst with
  | Unresolved(_) as u -> 
      // see if it is in the env map first
      let envVal = Map.tryFind cst env
      match envVal with
      | Some(c) -> ResolveCont c (env,ctx) failResolver
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
              | _ -> failResolver cst (env,ctx)
          | _ -> failResolver cst (env,ctx)
  | SeqConst(cseq) -> 
      let resolvedLst = cseq |> List.rev |> List.fold (fun acc c -> ResolveCont c (env,ctx) failResolver :: acc) []
      SeqConst(resolvedLst)
  | SetConst(cset) ->
      let resolvedSet = cset |> Set.fold (fun acc c -> acc |> Set.add (ResolveCont c (env,ctx) failResolver)) Set.empty
      SetConst(resolvedSet)
  | _ -> cst

let TryResolve cst (env,ctx) = 
  ResolveCont cst (env,ctx) (fun c (e,x) -> c)

let Resolve cst (env,ctx) =
  ResolveCont cst (env,ctx) (fun c (e,x) -> raise (ConstResolveFailed("failed to resolve " + c.ToString())))



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
  | SelectExpr(lst, idx) ->
      let lstC = Resolve (EvalUnresolved lst (heap,env,ctx)) (env,ctx)
      let idxC = EvalUnresolved idx (heap,env,ctx)
      match lstC, idxC with
      | SeqConst(clist), IntConst(n) -> clist.[n]
      | _ -> failwith "can't eval SelectExpr"
  | _ -> failwith "NOT IMPLEMENTED YET" //TODO finish this!
//  | Star         
//  | SelectExpr(_)   
//  | UpdateExpr(_)   
//  | SequenceExpr(_) 
//  | SeqLength(_)    
//  | ForallExpr(_)   
//  | UnaryExpr(_)   
//  | BinaryExpr(_)

// TODO: can this be implemented on top of the existing AstUtils.EvalSym??  We must!
let Eval expr (heap,env,ctx) = 
  try 
    let unresolvedConst = EvalUnresolved expr (heap,env,ctx)
    Some(TryResolve unresolvedConst (env,ctx))
  with
    ex -> None