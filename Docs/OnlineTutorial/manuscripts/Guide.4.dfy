method MultipleReturns(x: int, y: int) returns (more: int, less: int)
   ensures less < x;
   ensures x < more;
{
   more := x + y;
   less := x - y;
}