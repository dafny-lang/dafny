// RUN: %exits-with 4 %verify --show-proof-obligation-expressions "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Div(x: int, y: int): int
    requires y != 0
{
    x / y
}

function BadDiv(a: int, b: int): int
{
    Div(a, b)
}

function DivErrorMsg(x: int, y: int): int
    requires {:error "divisor must be nonzero", "divisor is nonzero"} y != 0
{
    x / y
}

function BadDivErrorMsg(a: int, b: int): int
{
    DivErrorMsg(a, b)
}

function BadNamedLambdaDiv(a: int, b: int): int
{
    var lam := (x, y) requires y != 0 => x / y;
    lam(a, b)
}

function BadAnonLambdaDiv(a: int, b: int): int
{
    ((x, y) requires y != 0 => x / y)(a, b)
}