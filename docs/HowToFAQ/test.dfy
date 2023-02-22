module {:options "--function-syntax:4"} M {
  
function fm(b: int): int { 20 }

predicate  pm(a: int)
{
    true
}

function  fm'(n: int): int
ensures pm(n)
{
    var v := fm(n);
    //assert pm(v);   // OK
    //assume pm(v);   // OK
    expect pm(v);   // error
    v
}

}
