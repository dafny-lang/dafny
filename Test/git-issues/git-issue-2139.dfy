// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method a() 
{
    var tok := (0,0);
    match tok {
      case "B" => 
      case _ => 
    }
}