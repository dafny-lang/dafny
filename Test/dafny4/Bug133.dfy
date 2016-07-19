// RUN: %dafny /noNLarith /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Math__div_def_i { 
	function my_div_pos(x:int, d:int) : int
		requires d >  0;
		decreases if x < 0 then (d - x) else x;
	{
		if x < 0 then
			-1 + my_div_pos(x+d, d)
		else if x < d then
			0
		else
			1 + my_div_pos(x-d, d)
	} 
} 


