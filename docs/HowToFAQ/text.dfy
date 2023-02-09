function Eval(): string -> bool {
   EvalOperator(Dummy)
}

function EvalOperator(op: string -> bool): string -> bool 
{
  (v: string) => op(v)
}

function method Dummy(str: string): bool
  requires str == []
