// ---------------------- chaining operators -----------------------------------

method TestChaining0(j: int, k: int, m: int)
  requires j != k != m;  // error: cannot have more than one != per chain
  requires j == k == m;  // dandy
  requires j < k == m == m+1 != m+2 >= 100;  // error: cannot mix < and >=
  requires j >= k == m == m-1 != m-2 < 100;  // error: cannot mix >= and <
{
}

method TestChaining1<T>(s: set<T>, t: set<T>, u: set<T>, x: T, SuperSet: set<set<T>>)
  requires s <= t <= u >= s+u;  // error: cannot mix <= and >=
  ensures s <= u;
  ensures s !! t !! u; // valid, means pairwise disjoint
  ensures x in s in SuperSet;  // error: 'in' is not chaining
  ensures x !in s in SuperSet;  // error: 'in' is not chaining
  ensures x in s !in SuperSet;  // error: 'in' is not chaining
  ensures x in s == t;  // error: 'in' is not chaining
{
}

// ---------------------- calc statements -----------------------------------

method TestCalc()
{
  calc {} // OK, empty calculations are allowed
  calc {
	2 + 3; // OK, single-line calculations are allowed
  }
  calc {
	2 + 3;
	calc {  // OK: a calc statement is allowed as a sub-hint
		2;
		1 + 1;
	}
	calc {
		3;
		1 + 2;
	}
	{ assert true; } // OK: multiple subhints are allowed between two lines
	1 + 1 + 1 + 2;
	{ assert 1 + 1 + 1 == 3; }
	{ assert true; }
	3 + 2;
  }
  calc != { // error: != is not allowed as the main operator of a calculation
	2 + 3;
	4;
  }
  calc { // OK, these operators are compatible
	2 + 3;
	> 4;
	>= 2 + 2;
  }
  calc < { // OK, these operators are compatible
	2 + 3;
	== 5;
	<= 3 + 3;
  }
  calc < { // error: cannot mix < and >= or >
	2 + 3;
	>= 5;
	> 2 + 2;
	6;
  }
  calc >= { // error: cannot mix >= and <= or !=
	2 + 3;
	<= 5;
	!= 2 + 2;
	3;
  }
  calc { // error: cannot have more than one != per calc
	2 + 3;
	!= 4;
	!= 1 + 2;
	3;
  }
}
