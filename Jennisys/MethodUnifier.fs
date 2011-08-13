module MethodUnifier

open Ast
open AstUtils
open PrintUtils
open Resolver
open Utils

exception CannotUnify

type UnifDirection = LTR | RTL

let rec UnifyImplies lhs rhs dir unifs = 
  ///
  let __AddOrNone unifs name e = Some(unifs |> Utils.MapAddNew name e)
  ///
  let __UnifLists lstL lstR = 
    if List.length lstL = List.length lstR then
      try 
        let unifs2 = List.fold2 (fun acc elL elR -> match UnifyImplies elL elR dir acc with
                                                    | Some(u) -> u
                                                    | None -> raise CannotUnify) unifs lstL lstR
        Some(unifs2)
      with 
      | CannotUnify -> None
    else
      None
  ///
  let __ApplyUnifs unifs exprList = 
            exprList |> List.fold (fun acc e -> 
                                     let e' = e |> Rewrite (fun e ->
                                                              match e with 
                                                              | VarLiteral(id) when Map.containsKey id unifs -> Some(unifs |> Map.find id)
                                                              | _ -> None)
                                     acc |> Set.add e'
                                  ) Set.empty

  if lhs = FalseLiteral || rhs = TrueLiteral then
    Some(unifs)
  else 
    try 
      let l,r = match dir with
                | LTR -> lhs,rhs
                | RTL -> rhs,lhs
      match l, r with
      | VarLiteral(vname), rhs -> __AddOrNone unifs vname rhs
      | IntLiteral(nL), IntLiteral(nR) when nL = nR -> 
          Some(unifs)
      | BoolLiteral(bL), BoolLiteral(bR) when bL = bR -> 
          Some(unifs)
      | SetExpr(elistL),  SetExpr(elistR) ->
          let s1 = elistL |> __ApplyUnifs unifs 
          let s2 = elistR |> Set.ofList
          if (s1 = s2) then 
            Some(unifs)
          else
            __UnifLists elistL elistR
      | SequenceExpr(elistL), SequenceExpr(elistR) when List.length elistL = List.length elistR ->
          __UnifLists elistL elistR
      | _ when l = r ->
          Some(unifs)
      | _ ->
          let __InvOps op1 op2 = match op1, op2 with "<" , ">" | ">" , "<" | "<=", ">=" | ">=", "<=" -> true | _ -> false
          let __ImpliesOp op1 op2 = 
            match op1, op2 with 
            | "<" , "!=" | ">" , "!=" -> true 
            | "=" , ">=" | "=" , "<=" -> true 
            | _ -> false
          let __CommOp op = match op with "=" | "!=" -> true | _ -> false

          let __TryUnifyPair x1 a1 x2 a2 unifs = 
            let builder = new CascadingBuilder<_>(None)
            builder {
              let! unifsLhs = UnifyImplies x1 a1 dir unifs
              let! unifsRhs = UnifyImplies x2 a2 dir unifsLhs
              return Some(unifsRhs)
            }

          // target implies candidate!
          let rec ___f2 consequence premise unifs = 
            match consequence, premise with
            // same operators + commutative -> try both
            | BinaryExpr(_, opT, lhsT, rhsT), BinaryExpr(_, opC, lhsC, rhsC) when opT = opC && __CommOp opT ->
                match __TryUnifyPair lhsC lhsT rhsC rhsT unifs with
                | Some(x) -> Some(x)
                | None -> __TryUnifyPair lhsC rhsT rhsC lhsT unifs
            // operators are the same
            | BinaryExpr(_, opT, lhsT, rhsT), BinaryExpr(_, opC, lhsC, rhsC) when opC = opT ->
                __TryUnifyPair lhsC lhsT rhsC rhsT unifs
            // operators are exactly the invers of one another
            | BinaryExpr(_, opT, lhsT, rhsT), BinaryExpr(_, opC, lhsC, rhsC) when __InvOps opC opT ->
                __TryUnifyPair lhsC rhsT rhsC lhsT unifs
            // 
            | BinaryExpr(_, opT, lhsT, rhsT), BinaryExpr(_, opC, lhsC, rhsC) when __ImpliesOp opC opT ->
                __TryUnifyPair lhsC lhsT rhsC rhsT unifs
            | UnaryExpr(opC, subC), UnaryExpr(opP, subP) when opC = opP ->
                UnifyImplies subP subC dir unifs 
            | _ -> None                     

          let rec ___f1 targetLst candidateLst unifs = 
            match targetLst, candidateLst with
            | targetExpr :: targetRest, candExpr :: candRest -> 
                // trying to find a unification for "targetExpr"
                let uOpt = match ___f2 targetExpr candExpr unifs with
                            // found -> just return
                            | Some(unifs2) -> Some(unifs2)
                            // not found -> keep looking in the rest of the candidate expressions
                            | None -> ___f1 [targetExpr] candRest unifs
                match uOpt with
                // found -> try find for the rest of the target expressions
                | Some(unifs2) -> ___f1 targetRest candidateLst unifs2
                // not found -> fail
                | None -> None
            | targetExpr :: _, [] ->
                // no more candidates for unification for this targetExpr -> fail
                None
            | [], _ ->
                // we've found unifications for all target expressions -> return the current unifications map
                Some(unifs)
                  
          let __HasSetExpr e = DescendExpr2 (fun ex acc -> if acc then true else match ex with SetExpr(_) -> true | _ -> false) e false
          let __PreprocSplitSort e = e |> DesugarAndRemove |> DistributeNegation |> SplitIntoConjunts |> List.sortBy (fun e -> if __HasSetExpr e then 1 else 0)
          let lhsConjs = lhs |> __PreprocSplitSort
          let rhsConjs = rhs |> __PreprocSplitSort
          ___f1 rhsConjs lhsConjs unifs
    with
    | KeyAlreadyExists
    | CannotUnify -> None

let TryUnify targetMthd candMethod = 
  let targetPre,targetPost = GetMethodPrePost targetMthd
  let candPre,candPost = GetMethodPrePost candMethod
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
  let __Apply args = args |> List.map (fun (Var(name,_)) -> 
                                             match Map.tryFind name unifs with
                                             | Some(e) -> e
                                             | None -> VarLiteral(name))
  let ins = GetMethodInArgs m |> __Apply
  let outs = GetMethodOutArgs m |> __Apply
  
  let retVars, asgs = outs |> List.fold (fun (acc1,acc2) e -> 
                                          let vname = SymGen.NewSym
                                          let v = Var(vname, None)
                                          let acc1' = acc1 @ [v]
                                          let acc2' = acc2 @ [ArbitraryStatement(Assign(VarLiteral(vname), e))]
                                          acc1', acc2'
                                       ) ([],[])
  let mcallExpr = MethodCall(receiver, GetComponentName c, GetMethodName m, ins)
  match retVars, outs with
  | [], [] -> [ArbitraryStatement(ExprStmt(mcallExpr))]
  | [_], [VarLiteral(vn2)] -> [ArbitraryStatement(Assign(VarDeclExpr([Var(vn2, None)], false), mcallExpr))]
  | _ ->
      let mcall = ArbitraryStatement(Assign(VarDeclExpr(retVars, true), mcallExpr))
      mcall :: asgs

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
        let modObjs = if IsModifiableObj obj m then Set.singleton obj else Set.empty
        let body = ApplyMethodUnifs ThisLiteral (comp,m') unifs
        let hInst = { objs           = Utils.MapSingleton obj.name obj;
                      modifiableObjs = modObjs;
                      assignments    = body; 
                      methodArgs     = Map.empty; 
                      methodRetVals  = Map.empty;
                      globals        = Map.empty }
        Some(Map.empty |> Map.add (comp,m) [cond, hInst]
                       |> Map.add (comp,m') [])
    | None -> None