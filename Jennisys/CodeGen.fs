module CodeGen

open Ast
open AstUtils
open Utils
open Resolver
open TypeChecker
open PrintUtils
open DafnyPrinter
open DafnyModelUtils

// TODO: this should take a list of fields and unroll all possibilities (instead of unrolling on branch only, following exactly one field)
//let rec GetUnrolledFieldValidExpr fldExpr fldName validFunName numUnrolls : Expr = 
//  if numUnrolls = 0 then
//    TrueLiteral
//  else
//    BinaryImplies (BinaryNeq fldExpr (ObjLiteral("null")))
//                  (BinaryAnd (Dot(fldExpr, validFunName))
//                             (GetUnrolledFieldValidExpr (Dot(fldExpr, fldName)) fldName validFunName (numUnrolls-1)))

/// requires: numUnrols >= 0
/// requires: |fldExprs| = |fldNames|
let rec GetUnrolledFieldValidExpr fldExprs fldNames validFunName numUnrolls = 
  let rec __Combine exprLst strLst = 
    match exprLst with
    | e :: rest ->
        let resLst1 = strLst |> List.map (fun s -> Dot(e, s))
        List.concat [resLst1; __Combine rest strLst]
    | [] -> []
  let rec __NotNull e = 
    match e with
    | IdLiteral(_)
    | ObjLiteral(_) -> BinaryNeq e (ObjLiteral("null"))
    | Dot(sub, str) -> BinaryAnd (__NotNull sub) (BinaryNeq e (ObjLiteral("null")))
    | _ -> failwith "not supposed to happen"
  (* --- function body starts here --- *)  
  assert (numUnrolls >= 0)
  if numUnrolls = 0 then
    [TrueLiteral]
  else
    let exprList = fldExprs |> List.map (fun e -> BinaryImplies (__NotNull e) (Dot(e, validFunName)))
    if numUnrolls = 1 then 
      exprList
    else 
      let fldExprs = __Combine fldExprs fldNames
      List.append exprList (GetUnrolledFieldValidExpr fldExprs fldNames validFunName (numUnrolls - 1))
                                                                    

//let GetFieldValidExpr fldName validFunName numUnrolls : Expr = 
//  GetUnrolledFieldValidExpr (IdLiteral(fldName)) fldName validFunName numUnrolls

let GetFieldValidExpr flds validFunName numUnrolls = 
  let fldExprs = flds |> List.map (function Var(name, _) -> IdLiteral(name))
  let fldNames = flds |> List.map (function Var(name, _) -> name)
  GetUnrolledFieldValidExpr fldExprs fldNames validFunName numUnrolls

let GetFieldsForValidExpr allFields prog : VarDecl list =
  allFields |> List.filter (function Var(name, tp) when IsUserType prog tp -> true
                                     | _                                   -> false)

let GetFieldsValidExprList clsName allFields prog : Expr list =
  let fields = GetFieldsForValidExpr allFields prog
  let fieldsByType = GroupFieldsByType fields
  fieldsByType |> Map.fold (fun acc t varSet ->
                              let validFunName, numUnrolls = 
                                match t with
                                | Some(ty) when clsName = (GetTypeShortName ty) -> "Valid_self()", Options.CONFIG.numLoopUnrolls
                                | _ -> "Valid()", 1 
                              acc |> List.append (GetFieldValidExpr (Set.toList varSet) validFunName numUnrolls)
                           ) []

//  fields |> List.map (function Var(name, t) -> 
//                                 let validFunName, numUnrolls = 
//                                   match t with
//                                   | Some(ty) when clsName = (GetTypeShortName ty) -> "Valid_self()", Options.CONFIG.numLoopUnrolls
//                                   | _ -> "Valid()", 1
//                                 GetFieldValidExpr name validFunName numUnrolls
//                     )

let PrintValidFunctionCode comp prog genRepr: string = 
  let idt = "    "
  let __PrintInvs invs = 
    invs |> List.fold (fun acc e -> List.concat [acc ; SplitIntoConjunts e]) []
         |> PrintSep (" &&" + newline) (fun e -> sprintf "%s(%s)" idt (PrintExpr 0 e))
         |> fun s -> if s = "" then (idt + "true") else s
  let clsName = GetClassName comp
  let vars = GetAllFields comp
  let allInvs = GetInvariantsAsList comp |> DesugarLst
  let fieldsValid = GetFieldsValidExprList clsName vars prog
  
  let frameFldNames = GetFrameFields comp |> List.choose (function Var(name,_) -> Some(name))
  let validReprBody = 
    "    this in Repr &&" + newline +
    "    null !in Repr" + 
    (PrintSep "" (fun x -> " &&" + newline + "    ($x != null ==> $x in Repr && $x.Repr <= Repr && this !in $x.Repr)".Replace("$x", x)) frameFldNames)

  let vr = 
    if genRepr then
      "  function Valid_repr(): bool" + newline +
      "    reads *;" + newline +
      "  {" + newline +
      validReprBody + newline +
      "  }" + newline + newline
    else
      ""                                                        
  // TODO: don't hardcode decr vars!!!
//  let decrVars = if List.choose (function Var(n,_) -> Some(n)) vars |> List.exists (fun n -> n = "next") then
//                   ["list"]
//                 else
//                   []
//  (if List.isEmpty decrVars then "" else sprintf "    decreases %s;%s" (PrintSep ", " (fun a -> a) decrVars) newline) +
  vr + 
  "  function Valid_self(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  (Utils.Ite genRepr ("    Valid_repr() &&" + newline) "") +
  (__PrintInvs allInvs) + newline +
  "  }" + newline +
  newline +
  "  function Valid(): bool" + newline +
  "    reads *;" + newline +
  "  {" + newline + 
  "    this.Valid_self() &&" + newline +
  (__PrintInvs fieldsValid) + newline +
  "  }" + newline

let PrintDafnyCodeSkeleton prog methodPrinterFunc genRepr =
  match prog with
  | Program(components) -> components |> List.fold (fun acc comp -> 
      match comp with  
      | Component(Class(name,typeParams,members), Model(_,_,cVars,frame,inv), code) as comp ->
        let aVars = FilterFieldMembers members |> List.append (Utils.Ite genRepr [Var("Repr", Some(SetType(NamedType("object", []))))] [])
        let compMethods = FilterConstructorMembers members
        // Now print it as a Dafny program
        acc + 
        (sprintf "class %s%s {" name (PrintTypeParams typeParams)) + newline +       
        // the fields: original abstract fields plus concrete fields
        (sprintf "%s" (PrintFields aVars 2 true)) + newline +     
        (sprintf "%s" (PrintFields cVars 2 false)) + newline +                           
        // generate the Valid function
        (sprintf "%s" (PrintValidFunctionCode comp prog genRepr)) + newline +
        // call the method printer function on all methods of this component
        (methodPrinterFunc comp) +
        // the end of the class
        "}" + newline + newline
      | _ -> assert false; "") ""

let PrintAllocNewObjects heapInst indent = 
  let idt = Indent indent
  heapInst.assignments |> List.fold (fun acc a ->
                                       match a with
                                       | FieldAssignment((obj,fld),_) when not (obj.name = "this") ->
                                           acc |> Set.add obj
                                       | FieldAssignment(_, ObjLiteral(name)) when not (name = "this" || name = "null") ->
                                           acc |> Set.add (heapInst.objs |> Map.find name)
                                       | _ -> acc
                                   ) Set.empty
                       |> Set.fold (fun acc obj -> acc + (sprintf "%svar %s := new %s;%s" idt obj.name (PrintType obj.objType) newline)) ""

let PrintVarAssignments heapInst indent = 
  let idt = Indent indent
  let fldAssgnsStr = heapInst.assignments |> PrintSep newline (fun asgn ->                                                        
                                                                 let exprStr = 
                                                                   match asgn with
                                                                   | FieldAssignment((o,f),e) ->
                                                                       let fldName = GetVarName f
                                                                       if fldName = "" then
                                                                         PrintStmt (ExprStmt(e)) 0 false
                                                                       else
                                                                         PrintStmt (Assign(Dot(ObjLiteral(o.name), fldName), e)) 0 false
                                                                   | ArbitraryStatement(stmt) ->
                                                                         PrintStmt stmt 0 false
                                                                 idt + exprStr)
  let retValsAssgnsStr = heapInst.methodRetVals |> Map.toList
                                                |> PrintSep newline (fun (retVarName, retVarVal) ->  
                                                                       let stmt = Assign(VarLiteral(retVarName), retVarVal)
                                                                       let assgnStr = PrintStmt stmt 0 false
                                                                       idt + assgnStr)
  let str = [fldAssgnsStr; retValsAssgnsStr] |> List.filter (fun s -> not (s = "")) |> PrintSep newline (fun s -> s)
  str + newline

///
let PrintReprAssignments prog heapInst indent = 
  let __FollowsFunc o1 o2 = 
    heapInst.assignments |> List.fold (fun acc assgn -> 
                                         match assgn with
                                         | FieldAssignment ((srcObj,fld),value) -> acc || (srcObj = o1 && value = ObjLiteral(o2.name))
                                         | _ -> false
                                      ) false
  let idt = Indent indent
  let objs = heapInst.assignments |> List.fold (fun acc assgn -> 
                                                  match assgn with
                                                  | FieldAssignment((obj,(Var(fldName,_))),_) -> if fldName = "" then acc else acc |> Set.add obj
                                                  | _ -> acc
                                               ) Set.empty
                                  |> Set.toList
                                  |> Utils.TopSort __FollowsFunc
                                  |> List.rev
  let reprGetsList = objs |> List.fold (fun acc obj -> 
                                          let expr = SetExpr([ObjLiteral(obj.name)])
                                          let builder = CascadingBuilder<_>(expr)
                                          let fullRhs = builder {
                                            let typeName = GetTypeShortName obj.objType
                                            let! comp = FindComponent prog typeName
                                            let vars = GetFrameFields comp
                                            let nonNullVars = vars |> List.filter (fun v -> 
                                                                                      let lst = heapInst.assignments |> List.choose (function FieldAssignment(x,y) -> Some(x,y) | _ -> None)
                                                                                      match Utils.ListMapTryFind (obj,v) lst with
                                                                                      | Some(ObjLiteral(n)) when not (n = "null") -> true
                                                                                      | _ -> false)
                                            return nonNullVars |> List.fold (fun a v -> 
                                                                                BinaryPlus a (Dot(Dot(ObjLiteral(obj.name), (GetVarName v)), "Repr"))
                                                                            ) expr
                                          }
                                          let fullReprExpr = BinaryGets (Dot(ObjLiteral(obj.name), "Repr")) fullRhs 
                                          fullReprExpr :: acc
                                        ) []
  
  if not (reprGetsList = []) then
    idt + "// repr stuff" + newline + 
    (PrintStmtList reprGetsList indent true)
  else
    ""
                                                          
let rec PrintHeapCreationCode prog sol indent genRepr =
  /// just removes all FieldAssignments to unmodifiable objects    
  let __RemoveUnmodifiableStuff heapInst = 
    let newAsgs = heapInst.assignments |> List.fold (fun acc a ->
                                                       match a with
                                                       | FieldAssignment((obj,_),_) when not (Set.contains obj heapInst.modifiableObjs) ->
                                                           acc
                                                       | _ -> acc @ [a]
                                                    ) []
    { heapInst with assignments = newAsgs }

  let idt = Indent indent
  match sol with
  | (c, hi) :: rest ->
      let heapInstMod = __RemoveUnmodifiableStuff hi
      let __ReprAssignments ind = 
        if genRepr then
          (PrintReprAssignments prog heapInstMod ind)
        else 
          ""
      if c = TrueLiteral then
        (PrintAllocNewObjects heapInstMod indent) +
        (PrintVarAssignments heapInstMod indent) +
        (__ReprAssignments indent) +
        (PrintHeapCreationCode prog rest indent genRepr) 
      else
        if List.length rest > 0 then
          idt + "if (" + (PrintExpr 0 c) + ") {" + newline +
          (PrintAllocNewObjects heapInstMod (indent+2)) +
          (PrintVarAssignments heapInstMod (indent+2)) +
          (__ReprAssignments (indent+2)) +
          idt + "} else {" + newline + 
          (PrintHeapCreationCode prog rest (indent+2) genRepr) +
          idt + "}" + newline
        else 
          (PrintAllocNewObjects heapInstMod indent) +
          (PrintVarAssignments heapInstMod indent) +
          (__ReprAssignments indent)
  | [] -> ""

let PrintPrePost pfix expr = 
  SplitIntoConjunts expr |> PrintSep "" (fun e -> pfix + (PrintExpr 0 e) + ";")

let GetPreconditionForMethod m = 
  let validExpr = IdLiteral("Valid()");
  match m with
  | Method(_,_,pre,_,isConstr) ->
      if isConstr then
        pre
      else
        BinaryAnd validExpr pre
  | _ -> failwithf "expected a method, got %O" m     

let GetPostconditionForMethod m genRepr = 
  let validExpr = IdLiteral("Valid()");
  match m with
  | Method(_,_,_,post,isConstr) ->
      let postExpr = BinaryAnd validExpr post
      if genRepr then
        let freshExpr = if isConstr then "fresh(Repr - {this})" else "fresh(Repr - old(Repr))";
        BinaryAnd (IdLiteral(freshExpr)) postExpr
      else
        postExpr
  | _ -> failwithf "expected a method, got %O" m     
      
let GenConstructorCode mthd body genRepr =
  let validExpr = IdLiteral("Valid()");
  match mthd with
  | Method(methodName, sign, pre, post, _) -> 
      let preExpr = GetPreconditionForMethod mthd |> Desugar
      let postExpr = GetPostconditionForMethod mthd genRepr |> Desugar
      "  method " + methodName + (PrintSig sign) + newline +
      "    modifies this;" + 
      (PrintPrePost (newline + "    requires ") preExpr) + 
      (PrintPrePost (newline + "    ensures ") postExpr) + 
      newline +
      "  {" + newline + 
      body + 
      "  }" + newline
  | _ -> ""

// solutions: (comp, constructor) |--> condition * heapInst
let PrintImplCode prog solutions genRepr =
  PrintDafnyCodeSkeleton prog (fun comp ->
                                 let cname = GetComponentName comp
                                 solutions |> Map.fold (fun acc (c,m) sol -> 
                                                          if (GetComponentName c) = cname then
                                                            let mthdBody = 
                                                              match sol with
                                                              | [] -> 
                                                                  "    //unable to synthesize" +
                                                                  PrintPrePost (newline + "    assume ") (GetPostconditionForMethod m genRepr |> Desugar) + newline
                                                              | _ -> 
                                                                  PrintHeapCreationCode prog sol 4 genRepr
                                                            acc + newline + (GenConstructorCode m mthdBody genRepr) + newline
                                  
                                                          else
                                                            acc) "") genRepr