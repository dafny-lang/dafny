//  ####################################################################
///   Various utility functions
///
///   author: Aleksandar Milicevic (t-alekm@microsoft.com)
//  ####################################################################

module Utils

// -------------------------------------------
// ----------- collection util funcs ---------
// -------------------------------------------

//  =====================================
/// ensures: ret = b ? Some(b) : None
//  =====================================
let BoolToOption b =
  if b then
    Some(b)
  else
    None

//  =====================================
/// ensures: ret = (opt == Some(_))
//  =====================================
let IsSomeOption opt = 
  match opt with
  | Some(_) -> true
  | None -> false

//  =====================================
/// ensures: ret = (opt == None)
//  =====================================
let IsNoneOption opt = IsSomeOption opt |> not

//  =====================================
/// requres: x = Some(a) or failswith msg
/// ensures: ret = a
//  =====================================
let ExtractOptionMsg msg x = 
  match x with
  | Some(a) -> a
  | None -> failwith msg

//  ====================
/// requres: x = Some(a)
/// ensures: ret = a
//  ====================
let ExtractOption x = 
  ExtractOptionMsg "can't extract anything from a None" x

//  ==========================================================
/// requres: List.length lst <= 1, otherwise fails with errMsg
/// ensures: if |lst| = 0 then
///            ret = None
///          else
///            ret = Some(lst[0])
//  ==========================================================
let ListToOptionMsg  lst errMsg = 
  if List.length lst > 1 then
    failwith errMsg
  if List.isEmpty lst then
    None
  else
    Some(lst.[0])

let ListToOption lst = ListToOptionMsg lst "given list contains more than one element"

//  =============================================================
/// ensures: forall i :: 0 <= i < |lst| ==> ret[i] = Some(lst[i])
//  =============================================================
let rec ConvertToOptionList lst = 
  match lst with
  | fs :: rest -> Some(fs) :: ConvertToOptionList rest
  | [] -> []

//  =========================================================
/// requres: Seq.length seq <= 1, otherwise fails with errMsg
/// ensures: if |seq| = 0 then
///            ret = None
///          else
///            ret = Some(seq[0])
//  =========================================================
let SeqToOptionMsg seq errMsg = 
  if Seq.length seq > 1 then
    failwith errMsg
  if Seq.isEmpty seq then
    None
  else
    Some(Seq.nth 0 seq)

let SeqToOption seq = SeqToOptionMsg seq "given seq contains more than one element"

//  =========================================================
/// requires: Set.count set <= 1, otherwise fails with errMsg
/// ensures: if |set| = 0 then
///            ret = None
///          else
///            ret = Some(set[0])
//  =========================================================
let SetToOptionMsg set errMsg = 
  if Set.count set > 1 then
    failwith errMsg
  if (Set.isEmpty set) then
    None
  else 
    Some(set |> Set.toList |> List.head)

let SetToOption set = SetToOptionMsg set "give set contains more than one value"

//  ============================================================
/// requires: n >= 0
/// ensures:  |ret| = n && forall i :: 0 <= i < n ==> ret[i] = e
//  ============================================================
let rec GenList n e =
  if n < 0 then 
    failwith "n must be positive"
  if n = 0 then
    []
  else
    e :: (GenList (n-1) e)

//  ==========================
/// ensures: ret = elem in lst
//  ==========================
let ListContains elem lst = 
  lst |> List.exists (fun e -> e = elem)

//  ===============================================================
/// ensures: |ret| = max(|lst| - cnt, 0)
/// ensures: forall i :: cnt <= i < |lst| ==> ret[i] = lst[i-cnt]
//  ===============================================================
let rec ListSkip cnt lst = 
  if cnt = 0 then
    lst    
  else
    match lst with
    | fs :: rest -> ListSkip (cnt-1) rest
    | [] -> []

//  ===============================================================
/// ensures: forall i :: 0 <= i < max(|srcList|, |dstList|) ==> 
///            if i = idx then
///              ret[i] = v
///            elif i < |srcList| then
///              ret[i] = srcList[i]
///            else
///              ret[i] = dstList[i] 
//  ===============================================================
let rec ListBuild srcList idx v dstList =
  match srcList, dstList with
  | fs1 :: rest1, fs2 :: rest2 -> if idx = 0 then
                                    v :: List.concat [rest1 ; ListSkip (List.length rest1) rest2]
                                  else 
                                    fs1 :: ListBuild rest1 (idx-1) v rest2
  | [],           fs2 :: rest2 -> if idx = 0 then
                                    v :: rest2
                                  else 
                                    fs2 :: ListBuild [] (idx-1) v rest2
  | _,            []           -> failwith "index out of range"

//  =======================================
/// ensures: forall i :: 0 <= i < |lst| ==>
///            if i = idx then
///              ret[i] = v
///            else
///              ret[i] = lst[i]
//  =======================================
let rec ListSet idx v lst =
  match lst with
  | fs :: rest -> if idx = 0 then 
                    v :: rest
                  else
                    fs :: ListSet (idx-1) v rest
  | [] -> failwith "index out of range"

//  =======================================
/// ensures: forall k,v :: 
///            if k,v in map2 then
//               k,v in ret
///            elif k,v in map1 then
///              k,v in ret
///            else
///              k,v !in ret
//  =======================================
let rec MapAddAll map1 map2 = 
  map2 |> Map.fold (fun acc k v -> acc |> Map.add k v) map1
                                                 
// -------------------------------------------
// ------ string active patterns -------------
// -------------------------------------------

let (|Prefix|_|) (p:string) (s:string) =
  if s.StartsWith(p) then
    Some(s.Substring(p.Length))
  else
    None
                 
// -------------------------------------------
// --------------- workflow ------------------
// -------------------------------------------

let IfDo1 cond func1 a =
  if cond then
    func1 a
  else 
    a

let IfDo2 cond func2 (a1,a2) =
  if cond then
    func2 a1 a2
  else
    a1,a2 

type CascadingBuilder<'a>(failVal: 'a) = 
  member this.Bind(v, f) =
    match v with
    | Some(x) -> f x
    | None -> failVal
  member this.Return(v) = v

// -------------------------------------------
// --------------- random --------------------
// -------------------------------------------

let Iden x = x