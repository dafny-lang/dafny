// RUN: %testDafnyForEachCompiler "%s"

function method {:tailrecursion} GetMaps(
    opts : string,
    shortMap : map<char, string> := map[])
    : map<char, string> 
  {
    if |opts| == 0 then
      shortMap
    else
      var shortMap := shortMap[opts[0] := "spoo"];
      GetMaps(opts[1..], shortMap)
  }