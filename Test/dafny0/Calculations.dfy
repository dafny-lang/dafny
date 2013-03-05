method CalcTest0(s: seq<int>) {
	calc {
		s[0]; // error: ill-formed line
	}
	
	calc {
		2;
		{ assert s[0] == 1; } // error: ill-formed hint
		1 + 1;
	}
	
	if (|s| > 0) {
		calc {
			s[0]; // OK: well-formed in this context
			<= { assert s[0] == s[0]; }
			s[0];
		}
	}
	assume forall x :: x in s ==> x >= 0;
	calc {
		0 < |s|;
	==>	{ assert s[0] >= 0; }   // OK: well-formed after previous line
		s[0] >= 0;                // OK: well-formed after previous line
  <==> { assert s[0] >= 0; }  // OK: well-formed when the previous line is well-formed
    s[0] > 0 || s[0] == 0;    // OK: well-formed when the previous line is well-formed
	}
}

method CalcTest1(x: int, y: int) {
	calc {
		x + y;
		{ assume x == 0; }
		y;
	}
	assert x == 0; // OK: follows from x + y == y;
}

method CalcTest2(x: int, y: int) {
	calc {
		x + y;
		{ assume x == 0; }
		y + x;
	}
	assert x == 0; // error: even though assumed above, is not exported by the calculation
}

// calc expression:
function CalcTest3(s: seq<int>): int {
	calc < {
		0;
		{ assume |s| == 5; }
		|s|;
	}
	s[0]
}