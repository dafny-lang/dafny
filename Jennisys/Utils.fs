module Utils

// -------------------------------------------
// ----------- collection util funcs ---------
// -------------------------------------------

let ListToOption lst = 
  assert (List.length lst <= 1)
  if List.isEmpty lst then
    None
  else
    Some(lst.[0])

let SeqToOption seq = 
  assert (Seq.length seq <= 1)
  if Seq.isEmpty seq then
    None
  else
    Some(Seq.nth 0 seq)

let rec GenList n =
  if n = 0 then
    []
  else
    None :: (GenList (n-1))

let rec ListSkip cnt lst = 
  if cnt = 0 then
    lst
  else
    match lst with
    | fs :: rest -> ListSkip (cnt-1) rest
    | [] -> []

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


let rec ListSet idx v lst =
  match lst with
  | fs :: rest -> if idx = 0 then 
                    v :: rest
                  else
                    fs :: ListSet (idx-1) v rest
  | [] -> failwith "index out of range"

// -------------------------------------------
// ------ string active patterns -------------
// -------------------------------------------

let (|Prefix|_|) (p:string) (s:string) =
  if s.StartsWith(p) then
    Some(s.Substring(p.Length))
  else
    None

let (|Exact|_|) (p:string) (s:string) =
  if s = p then
    Some(s)
  else
    None

