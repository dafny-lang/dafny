module MethodUnifier

open Ast
open Getters
open AstUtils
open FixpointSolver
open PrintUtils
open Resolver
open Utils

let TryUnify targetMthd candMethod = 
  let targetPre,targetPost = GetMethodPrePost targetMthd
  let targetPre = BinaryAnd targetPre (GetMethodGhostPrecondition targetMthd)
  let candPre,candPost = GetMethodPrePost candMethod
  let candPre = BinaryAnd candPre (GetMethodGhostPrecondition candMethod)
  let builder = new CascadingBuilder<_>(None)
  builder {
    let! unifs1 = UnifyImplies targetPre candPre RTL Map.empty
    let! unifs2 = UnifyImplies candPost targetPost LTR unifs1
    return Some(unifs2)
  }

let rec TryFindAMatch targetMthd candidateMethods = 
  let targetMthdName = GetMethodName targetMthd
  match candidateMethods with
  | candMthd :: rest ->
      if GetMethodName candMthd = targetMthdName then
        // skip if it is the same method
        TryFindAMatch targetMthd rest
      else
        match TryUnify targetMthd candMthd with
        | Some(unifs) -> Some(candMthd,unifs)
        | None -> TryFindAMatch targetMthd rest
  | [] -> None

let TryFindExistingOpt comp targetMthd = 
  TryFindAMatch targetMthd (GetMembers comp |> FilterMethodMembers)

let TryFindExisting comp targetMthd = 
  match TryFindAMatch targetMthd (GetMembers comp |> FilterMethodMembers) with
  | Some(m,unifs) -> m,unifs
  | None -> targetMthd, Map.empty

let ApplyMethodUnifs receiver (c,m) unifs =
  let __Apply args = args |> List.map (fun var -> 
                                         let name = GetExtVarName var
                                         match Map.tryFind name unifs with
                                         | Some(e) -> e
                                         | None -> VarLiteral(name))
  let ins = GetMethodInArgs m |> __Apply
  let outs = GetMethodOutArgs m |> __Apply
  
  let retVars, asgs = outs |> List.fold (fun (acc1,acc2) e -> 
                                          let vname = SymGen.NewSymFake e
                                          let v = Var(vname, None, false)
                                          let acc1' = acc1 @ [v]
                                          let acc2' = acc2 @ [ArbitraryStatement(Assign(VarLiteral(vname), e))]
                                          acc1', acc2'
                                       ) ([],[])
  let mcallExpr = MethodCall(receiver, GetComponentName c, GetMethodName m, ins)
  match retVars, outs with
  | [], [] -> [ArbitraryStatement(ExprStmt(mcallExpr))]
  | [_], [VarLiteral(vn2)] -> [ArbitraryStatement(Assign(VarDeclExpr([Var(vn2, None, false)], false), mcallExpr))]
  | _ ->
      let mcall = ArbitraryStatement(Assign(VarDeclExpr(retVars, true), mcallExpr))
      mcall :: asgs

//  ====================================================
///
//  ====================================================
let TryFindExistingAndConvertToSolution indent comp m cond callGraph =
  let __Calls caller callee =
    let keyOpt = callGraph |> Map.tryFindKey (fun (cc,mm) mset -> CheckSameMethods (comp,caller) (cc,mm))
    match keyOpt with
    | Some(k) -> callGraph |> Map.find k |> Set.contains ((GetComponentName comp),(GetMethodName callee))
    | None -> false
  (* --- function body starts here --- *)      
  if not Options.CONFIG.genMod then
    None
  else 
    let idt = Indent indent
    let candidateMethods = GetMembers comp |> List.filter (fun cm ->
                                                             match cm with
                                                             | Method(mname,_,_,_,_) when not (__Calls cm m) -> true
                                                             | _ -> false)
    match TryFindAMatch m candidateMethods with
    | Some(m',unifs) -> 
        Logger.InfoLine (idt + "    - substitution method found:")
        Logger.InfoLine (Printer.PrintMethodSignFull (indent+6) comp m')
        Logger.DebugLine (idt + "      Unifications: ")
        let idtt = idt + "        "
        unifs |> Map.fold (fun acc k v -> acc + (sprintf "%s%s -> %s%s" idtt k (Printer.PrintExpr 0 v) newline)) "" |> Logger.Debug 
        let obj = { name = "this"; objType = GetClassType comp }
        let modObjs = if IsModifiableObj obj (comp,m) then Set.singleton obj else Set.empty
        let body = ApplyMethodUnifs ThisLiteral (comp,m') unifs
        let hInst = { objs           = Utils.MapSingleton obj.name obj;
                      modifiableObjs         = modObjs;
                      assignments            = body; 
                      concreteValues         = body;
                      methodArgs             = Map.empty; 
                      methodRetVals          = Map.empty;
                      concreteMethodRetVals  = Map.empty;
                      globals                = Map.empty }
        Some(Map.empty |> Map.add (comp,m) [cond, hInst]
                       |> Map.add (comp,m') [])
    | None -> None

