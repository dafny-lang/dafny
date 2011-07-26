module CodeGen

open Ast
open AstUtils
open Utils
open Printer   
open Resolver
open TypeChecker
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
        (compMethods |> List.fold (fun acc m -> acc + (methodPrinterFunc comp m)) "") +
        // the end of the class
        "}" + newline + newline
      | _ -> assert false; "") ""

let PrintAllocNewObjects heapInst indent = 
  let idt = Indent indent
  heapInst.assignments |> List.fold (fun acc ((obj,fld),_) ->
                                      if not (obj.name = "this") then
                                        acc |> Set.add obj
                                      else 
                                        acc
                                   ) Set.empty
                       |> Set.fold (fun acc obj -> acc + (sprintf "%svar %s := new %s;%s" idt obj.name (PrintType obj.objType) newline)) ""

let PrintVarAssignments heapInst indent = 
  let idt = Indent indent
  heapInst.assignments |> List.fold (fun acc ((o,f),e) ->
                                      let fldName = PrintVarName f
                                      let value = PrintExpr 0 e
                                      acc + (sprintf "%s%s.%s := %s;" idt o.name fldName value) + newline
                                    ) ""

let PrintReprAssignments prog heapInst indent = 
  let __FollowsFunc o1 o2 = 
    heapInst.assignments |> List.fold (fun acc ((srcObj,fld),value) -> 
                                        acc || (srcObj = o1 && value = ObjLiteral(o2.name))
                                     ) false
  let idt = Indent indent
  let objs = heapInst.assignments |> List.fold (fun acc ((obj,fld),_) -> acc |> Set.add obj) Set.empty
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
                                                                                      match Utils.ListMapTryFind (obj,v) heapInst.assignments with
                                                                                      | Some(ObjLiteral(n)) when not (n = "null") -> true
                                                                                      | _ -> false)
                                            return nonNullVars |> List.fold (fun a v -> 
                                                                               BinaryPlus a (Dot(Dot(ObjLiteral(obj.name), (PrintVarName v)), "Repr"))
                                                                            ) expr
                                          }
                                          let fullReprExpr = BinaryGets (Dot(ObjLiteral(obj.name), "Repr")) fullRhs 
                                          fullReprExpr :: acc
                                       ) []
  
  idt + "// repr stuff" + newline + 
  (PrintStmtList reprGetsList indent)
                                                          
let rec PrintHeapCreationCode prog sol indent genRepr =    
  let idt = Indent indent
  match sol with
  | (c, heapInst) :: rest ->
      let __ReprAssignments ind = 
        if genRepr then
          (PrintReprAssignments prog heapInst ind)
        else 
          ""
      if c = TrueLiteral then
        (PrintAllocNewObjects heapInst indent) +
        (PrintVarAssignments heapInst indent) +
        (__ReprAssignments indent) +
        (PrintHeapCreationCode prog rest indent genRepr) 
      else
        if List.length rest > 0 then
          idt + "if (" + (PrintExpr 0 c) + ") {" + newline +
          (PrintAllocNewObjects heapInst (indent+2)) +
          (PrintVarAssignments heapInst (indent+2)) +
          (__ReprAssignments (indent+2)) +
          idt + "} else {" + newline + 
          (PrintHeapCreationCode prog rest (indent+2) genRepr) +
          idt + "}" + newline
        else 
          (PrintAllocNewObjects heapInst indent) +
          (PrintVarAssignments heapInst indent) +
          (__ReprAssignments indent)
  | [] -> ""

let GenConstructorCode mthd body genRepr =
  let validExpr = IdLiteral("Valid()");
  match mthd with
  | Method(methodName, sign, pre, post, _) -> 
      let __PrintPrePost pfix expr = SplitIntoConjunts expr |> PrintSep "" (fun e -> pfix + (PrintExpr 0 e) + ";")
      let preExpr = pre 
      let postExpr = BinaryAnd validExpr post
      "  method " + methodName + (PrintSig sign) + newline +
      "    modifies this;" + 
      (__PrintPrePost (newline + "    requires ") preExpr) + 
      Utils.Ite genRepr (newline + "    ensures fresh(Repr - {this});") "" +
      (__PrintPrePost (newline + "    ensures ") postExpr) + 
      newline +
      "  {" + newline + 
      body + 
      "  }" + newline
  | _ -> ""

// solutions: (comp, constructor) |--> condition * heapInst
let PrintImplCode prog solutions methodsToPrintFunc genRepr =
  let methods = methodsToPrintFunc prog
  PrintDafnyCodeSkeleton prog (fun comp mthd ->
                                 if Utils.ListContains (comp,mthd) methods  then
                                   let mthdBody = match Map.tryFind (comp,mthd) solutions with
                                                  | Some(sol) -> PrintHeapCreationCode prog sol 4 genRepr
                                                  | _ -> "    //unable to synthesize" + newline
                                   (GenConstructorCode mthd mthdBody genRepr) + newline
                                 else
                                   "") genRepr