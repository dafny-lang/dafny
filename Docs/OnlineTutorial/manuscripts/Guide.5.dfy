method MultipleReturns(x: int, y: int) returns (more: int, less: int)
   ensures less < x && x < more;
{
   more := x + y;
   less := x - y;
}