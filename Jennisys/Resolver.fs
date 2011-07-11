//  ####################################################################
///   Utilities for resolving the "Unresolved" constants with respect to 
///   a given context (heap/env/ctx)
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Resolver

open Ast
open AstUtils 
open Printer
open EnvUtils

// resolving values
exception ConstResolveFailed of string
 
//  ================================================================
/// Resolves a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, it just delegates the task to the
/// failResolver function
//  ================================================================
let rec ResolveCont (env,ctx) failResolver cst =
  match cst with
  | Unresolved(_) as u -> 
      // see if it is in the env map first
      let envVal = Map.tryFind cst env
      match envVal with
      | Some(c) -> ResolveCont (env,ctx) failResolver c
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
      let resolvedLst = cseq |> List.rev |> List.fold (fun acc c -> ResolveCont (env,ctx) failResolver c :: acc) []
      SeqConst(resolvedLst)
  | SetConst(cset) ->
      let resolvedSet = cset |> Set.fold (fun acc c -> acc |> Set.add (ResolveCont (env,ctx) failResolver c)) Set.empty
      SetConst(resolvedSet)
  | _ -> cst

//  =====================================================================
/// Tries to resolve a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, just returns the original Unresolved const.
//  =====================================================================
let TryResolve (env,ctx) cst = 
  ResolveCont (env,ctx) (fun c (e,x) -> c) cst

//  ==============================================================
/// Resolves a given Const (cst) with respect to a given env/ctx. 
///
/// If unable to resolve, raises a ConstResolveFailed exception
//  ==============================================================
let Resolve (env,ctx) cst =
  ResolveCont (env,ctx) (fun c (e,x) -> raise (ConstResolveFailed("failed to resolve " + c.ToString()))) cst
   
//  =================================================================
/// Evaluates a given expression with respect to a given heap/env/ctx       
//  =================================================================
let Eval (heap,env,ctx) expr = 
  let rec __EvalResolver expr = 
    match expr with
    | IdLiteral(id) when id = "this" -> GetThisLoc env
    | IdLiteral(id) ->
        match TryResolve (env,ctx) (Unresolved(id)) with 
        | Unresolved(_) -> __EvalResolver (Dot(IdLiteral("this"), id))
        | _ as c -> c
    | Dot(e, str) -> 
        let discr = __EvalResolver e
        let h2 = Map.filter (fun (loc,Var(fldName,_)) v -> loc = discr && fldName = str) heap |> Map.toList
        match h2 with
        | ((_,_),x) :: [] -> x
        | _ :: _ -> failwithf "can't evaluate expression deterministically: %s.%s resolves to multiple locations." (PrintConst discr) str
        | [] -> failwithf "can't find value for %s.%s" (PrintConst discr) str
    | _ -> failwith "NOT IMPLEMENTED YET"
  try 
    let unresolvedConst = EvalSym (fun e -> __EvalResolver e |> Resolve (env,ctx)) expr
    Some(TryResolve (env,ctx) unresolvedConst)
  with
    ex -> None