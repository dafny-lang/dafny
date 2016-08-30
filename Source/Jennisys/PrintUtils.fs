module PrintUtils

let newline = System.Environment.NewLine // "\r\n"

let rec Indent i =
  if i = 0 then "" else " " + (Indent (i-1))

let rec PrintSep sep f list =
  match list with
  | [] -> ""
  | [a] -> f a
  | a :: more -> (f a) + sep + (PrintSep sep f more)