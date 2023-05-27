// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
datatype DT_2<T_2> = DT_2_1 | DT_2_2(DT_2_2_1: T_2, DT_2_2_2: T_2) | DT_2_3(DT_2_3_1: int)
datatype DT_3<T_3> = DT_3_1
datatype DT_4<T_4, T_5> = DT_4_1 | DT_4_5(DT_4_5_1: T_4, DT_4_5_2: T_4, DT_4_5_3: T_5, DT_4_5_4: T_4)
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: seq<int>, p_m_method_9_2: seq<int>) returns (ret_1: bool, ret_2: array<real>, ret_3: real, ret_4: real)
{
	var v_array_1: array<real> := new real[4] [27.92, -1.04, 20.35, 5.83];
	return true, v_array_1, 16.28, -10.22;
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: seq<int>, p_m_method_8_2: char, p_m_method_8_3: bool, p_m_method_8_4: real) returns (ret_1: map<int, bool>)
{
	var v_map_4: map<multiset<int>, multiset<real>> := map[multiset{15, 27, 9} := multiset({20.27, -11.89, 5.29, -1.70}), multiset{19} := multiset({-19.61, -11.75, 0.48, -1.24}), multiset{} := multiset{-26.09, -14.12}, multiset{22} := multiset{13.01, 18.28}];
	if false {
		var v_seq_7: seq<int> := [14, 16, 28, 10];
		var v_seq_8: seq<int> := [18, 22, 28];
		var v_bool_11: bool, v_array_2: array<real>, v_real_3: real, v_real_4: real := m_method_9(v_seq_7, v_seq_8);
		v_bool_11, v_array_2, v_real_3, v_real_4 := v_bool_11, v_array_2, v_real_3, v_real_4;
		return map[17 := false, 6 := false, 28 := false, 24 := false];
	} else {
		if false {
			return map[10 := true, 10 := false, 28 := true];
		}
		var v_bool_12: bool, v_char_6: char, v_multiset_2: multiset<int>, v_set_1: set<multiset<bool>>, v_multiset_3: multiset<multiset<int>> := true, 'C', multiset{}, {}, multiset{multiset({3}), multiset{}};
	}
	var v_int_16: int := 29;
	var v_int_17: int := 7;
	while (v_int_16 < v_int_17) 
		decreases v_int_17 - v_int_16;
		invariant (v_int_16 <= v_int_17);
	{
		v_int_16 := (v_int_16 + 1);
	}
	return map[14 := true];
}

method m_method_7(p_m_method_7_1: real, p_m_method_7_2: bool) returns (ret_1: seq<int>)
{
	var v_int_12: int, v_multiset_1: multiset<multiset<int>> := 20, multiset({multiset{}, multiset{-6}});
	match 'Z' {
		case _ => {
			var v_int_13: int := 26;
			var v_char_5: char := m_method_3(v_int_13);
			v_char_5 := v_char_5;
			assert true;
			expect true;
		}
		
	}
	
	return [16];
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: bool, p_m_method_6_2: map<int, bool>, p_m_method_6_3: (bool, int, int)) returns (ret_1: bool)
{
	assert true;
	expect true;
	return false;
}

method m_method_5(p_m_method_5_1: bool) returns (ret_1: (int, real))
	requires ((p_m_method_5_1 == false));
	ensures (((p_m_method_5_1 == false)) ==> (((ret_1).0 == 8) && (-30.00 < (ret_1).1 < -29.80)));
{
	var v_int_real_1: (int, real) := (8, -29.90);
	var v_int_real_12: (int, real) := (8, -29.90);
	print "v_int_real_1.1", " ", (v_int_real_1.1 == -29.90), " ", "v_int_real_1", " ", (v_int_real_1 == v_int_real_12), " ", "v_int_real_1.0", " ", v_int_real_1.0, " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
	return v_int_real_1;
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool) returns (ret_1: real, ret_2: char, ret_3: map<int, int>, ret_4: DT_1<char>, ret_5: bool)
	requires ((p_m_method_4_2 == true) && (p_m_method_4_1 == false));
	ensures (((p_m_method_4_2 == true) && (p_m_method_4_1 == false)) ==> ((18.55 < ret_1 < 18.75) && (ret_2 == 'H') && (ret_3 == map[20 := 21, 22 := 5, 7 := 19, 27 := 3]) && (ret_4.DT_1_1? && ((ret_4 == DT_1_1))) && (ret_5 == true)));
{
	var v_DT_1_1_15: DT_1<char> := DT_1_1;
	print "p_m_method_4_1", " ", p_m_method_4_1, " ", "v_DT_1_1_15", " ", v_DT_1_1_15, " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return 18.65, 'H', map[20 := 21, 7 := 19, 27 := 3, 22 := 5], v_DT_1_1_15, true;
}

method m_method_3(p_m_method_3_1: int) returns (ret_1: char)
	requires ((p_m_method_3_1 == 2));
	ensures (((p_m_method_3_1 == 2)) ==> ((ret_1 == 'm')));
{
	var v_bool_2: bool := false;
	var v_bool_3: bool := true;
	var v_real_1: real, v_char_2: char, v_map_1: map<int, int>, v_DT_1_1_16: DT_1<char>, v_bool_4: bool := m_method_4(v_bool_2, v_bool_3);
	v_real_1, v_char_2, v_map_1, v_DT_1_1_16, v_bool_4 := v_real_1, v_char_2, v_map_1, v_DT_1_1_16, v_bool_4;
	print "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_char_2", " ", (v_char_2 == 'H'), " ", "v_real_1", " ", (v_real_1 == 18.65), " ", "v_map_1", " ", (v_map_1 == map[20 := 21, 22 := 5, 7 := 19, 27 := 3]), " ", "v_DT_1_1_16", " ", v_DT_1_1_16, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "v_bool_4", " ", v_bool_4, "\n";
	return 'm';
}

method safe_division(p_safe_division_1: int, p_safe_division_2: int) returns (ret_1: int)
	ensures (p_safe_division_2 == 0 ==> ret_1 == p_safe_division_1) && (p_safe_division_2 != 0 ==> ret_1 == p_safe_division_1 / p_safe_division_2);
{
	return (if ((p_safe_division_2 != 0)) then ((p_safe_division_1 / p_safe_division_2)) else (p_safe_division_1));
}

method safe_subsequence(p_safe_subsequence_1: seq, p_safe_subsequence_2: int, p_safe_subsequence_3: int) returns (ret_1: int, ret_2: int)
	ensures ((|p_safe_subsequence_1| > 0) ==> ((0 <= ret_1 < |p_safe_subsequence_1|) && (0 <= ret_2 < |p_safe_subsequence_1|) && ret_1 <= ret_2)) && ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_2 == 0))) || ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_2 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)))));
{
	var v_seq_1: seq := p_safe_subsequence_1;
	var v_int_2: int := p_safe_subsequence_2;
	var v_int_3: int := safe_index_seq(v_seq_1, v_int_2);
	var v_int_1: int := v_int_3;
	var v_seq_2: seq := p_safe_subsequence_1;
	var v_int_5: int := p_safe_subsequence_3;
	var v_int_6: int := safe_index_seq(v_seq_2, v_int_5);
	var v_int_4: int := v_int_6;
	if (v_int_1 <= v_int_4) {
		return v_int_1, v_int_4;
	} else {
		return v_int_4, v_int_1;
	}
}

method m_method_2(p_m_method_2_1: char, p_m_method_2_2: (int, bool), p_m_method_2_3: bool) returns (ret_1: DT_1<char>)
	requires (((p_m_method_2_2).0 == 10) && ((p_m_method_2_2).1 == false) && (p_m_method_2_1 == 'd') && (p_m_method_2_3 == true));
	ensures ((((p_m_method_2_2).0 == 10) && ((p_m_method_2_2).1 == false) && (p_m_method_2_1 == 'd') && (p_m_method_2_3 == true)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_int_8: int, v_int_9: int := 16, 3;
	for v_int_7 := v_int_8 downto v_int_9 
		invariant (v_int_7 - v_int_9 >= 0)
	{
		
	}
	var v_DT_1_1_13: DT_1<char> := DT_1_1;
	print "p_m_method_2_1", " ", (p_m_method_2_1 == 'd'), " ", "p_m_method_2_2.0", " ", p_m_method_2_2.0, " ", "p_m_method_2_2.1", " ", p_m_method_2_2.1, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, " ", "v_DT_1_1_13", " ", v_DT_1_1_13, "\n";
	return v_DT_1_1_13;
}

method m_method_1(p_m_method_1_1: char, p_m_method_1_2: bool, p_m_method_1_3: bool, p_m_method_1_4: (int, real)) returns (ret_1: DT_1<char>)
	requires ((p_m_method_1_1 == 'm') && (p_m_method_1_3 == false) && (p_m_method_1_2 == true) && ((p_m_method_1_4).0 == 8) && (-30.00 < (p_m_method_1_4).1 < -29.80));
	ensures (((p_m_method_1_1 == 'm') && (p_m_method_1_3 == false) && (p_m_method_1_2 == true) && ((p_m_method_1_4).0 == 8) && (-30.00 < (p_m_method_1_4).1 < -29.80)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_char_1: char := 'd';
	var v_int_bool_1: (int, bool) := (10, false);
	var v_int_bool_2: (int, bool) := v_int_bool_1;
	var v_bool_1: bool := true;
	var v_DT_1_1_14: DT_1<char> := m_method_2(v_char_1, v_int_bool_2, v_bool_1);
	var v_int_real_13: (int, real) := (8, -29.90);
	print "v_int_bool_1.0", " ", v_int_bool_1.0, " ", "v_char_1", " ", (v_char_1 == 'd'), " ", "v_bool_1", " ", v_bool_1, " ", "p_m_method_1_4.0", " ", p_m_method_1_4.0, " ", "p_m_method_1_4.1", " ", (p_m_method_1_4.1 == -29.90), " ", "v_int_bool_1.1", " ", v_int_bool_1.1, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'm'), " ", "p_m_method_1_4", " ", (p_m_method_1_4 == v_int_real_13), " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_int_bool_2", " ", v_int_bool_2, " ", "v_int_bool_1", " ", v_int_bool_1, " ", "v_DT_1_1_14", " ", v_DT_1_1_14, "\n";
	return v_DT_1_1_14;
}

method m_method_10(p_m_method_10_1: bool, p_m_method_10_2: bool, p_m_method_10_3: bool, p_m_method_10_4: bool) returns (ret_1: seq<int>)
{
	var v_int_19: int := (19 - 15);
	var v_array_3: array<bool> := new bool[5] [true, true, true, false, false];
	var v_int_20: int := v_array_3.Length;
	while (v_int_19 < v_int_20) 
		decreases v_int_20 - v_int_19;
		invariant (v_int_19 <= v_int_20);
	{
		v_int_19 := (v_int_19 + 1);
	}
	assert true;
	expect true;
	var v_real_6: real := -27.45;
	var v_bool_18: bool := false;
	var v_seq_11: seq<int> := m_method_7(v_real_6, v_bool_18);
	return v_seq_11;
}

method Main() returns ()
{
	var v_DT_1_1_1: DT_1<char> := DT_1_1;
	var v_DT_1_1_2: DT_1<char> := DT_1_1;
	var v_DT_1_1_3: DT_1<char> := DT_1_1;
	var v_DT_1_1_4: DT_1<char> := DT_1_1;
	var v_DT_1_1_5: DT_1<char> := DT_1_1;
	var v_DT_1_1_6: DT_1<char> := DT_1_1;
	var v_DT_1_1_7: DT_1<char> := DT_1_1;
	var v_DT_1_1_8: DT_1<char> := DT_1_1;
	var v_DT_1_1_9: DT_1<char> := DT_1_1;
	var v_DT_1_1_10: DT_1<char> := DT_1_1;
	var v_DT_1_1_11: DT_1<char> := DT_1_1;
	var v_DT_1_1_12: DT_1<char> := DT_1_1;
	var v_map_2: map<DT_1<char>, int> := ((if (false) then (map[v_DT_1_1_1 := -22, v_DT_1_1_2 := 19]) else (map[v_DT_1_1_3 := 5])) - (map[v_DT_1_1_8 := 6.13]).Keys);
	var v_int_10: int := 2;
	var v_char_3: char := m_method_3(v_int_10);
	var v_char_4: char := v_char_3;
	var v_bool_6: bool := ({false, true} == {true, false});
	var v_seq_3: seq<bool> := [false, false];
	var v_int_11: int := 9;
	var v_seq_189: seq<bool> := v_seq_3;
	var v_int_249: int := v_int_11;
	var v_int_250: int := safe_index_seq(v_seq_189, v_int_249);
	v_int_11 := v_int_250;
	var v_bool_7: bool := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_11]) else (true));
	var v_bool_5: bool := false;
	var v_int_real_2: (int, real) := m_method_5(v_bool_5);
	var v_int_real_3: (int, real) := v_int_real_2;
	var v_DT_1_1_17: DT_1<char> := m_method_1(v_char_4, v_bool_6, v_bool_7, v_int_real_3);
	var v_DT_1_1_18: DT_1<char> := v_DT_1_1_17;
	match (if ((v_DT_1_1_18 in v_map_2)) then (v_map_2[v_DT_1_1_18]) else (v_int_11)) {
		case 16 => {
			var v_bool_8: bool := false;
			var v_map_3: map<int, bool> := map[17 := true, 28 := false, 28 := false, 11 := false];
			var v_bool_int_int_1: (bool, int, int) := (false, 14, 12);
			var v_bool_int_int_2: (bool, int, int) := v_bool_int_int_1;
			var v_bool_9: bool := m_method_6(v_bool_8, v_map_3, v_bool_int_int_2);
			var v_bool_bool_1: (bool, bool) := (true, true);
			var v_real_bool_real_1: (real, bool, real) := (1.94, true, 2.72);
			var v_int_int_1: (int, int) := (26, 0);
			var v_bool_bool_real_bool_real_int_int_1: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_1, v_real_bool_real_1, v_int_int_1);
			var v_bool_bool_2: (bool, bool) := (false, false);
			var v_real_bool_real_2: (real, bool, real) := (-20.87, false, 4.55);
			var v_int_int_2: (int, int) := (13, 0);
			var v_bool_bool_real_bool_real_int_int_2: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_2, v_real_bool_real_2, v_int_int_2);
			var v_bool_bool_3: (bool, bool) := (false, true);
			var v_real_bool_real_3: (real, bool, real) := (13.34, true, 9.92);
			var v_int_int_3: (int, int) := (12, 17);
			var v_bool_bool_real_bool_real_int_int_3: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_3, v_real_bool_real_3, v_int_int_3);
			var v_bool_bool_4: (bool, bool) := (false, true);
			var v_real_bool_real_4: (real, bool, real) := (18.27, true, 27.48);
			var v_int_int_4: (int, int) := (9, 15);
			var v_bool_bool_real_bool_real_int_int_4: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_4, v_real_bool_real_4, v_int_int_4);
			var v_bool_bool_5: (bool, bool) := (false, false);
			var v_real_bool_real_5: (real, bool, real) := (-22.07, true, 15.78);
			var v_int_int_5: (int, int) := (1, -12);
			var v_bool_bool_real_bool_real_int_int_5: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_5, v_real_bool_real_5, v_int_int_5);
			var v_bool_bool_6: (bool, bool) := (false, false);
			var v_real_bool_real_6: (real, bool, real) := (10.38, false, -24.99);
			var v_int_int_6: (int, int) := (3, 22);
			var v_bool_bool_real_bool_real_int_int_6: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_6, v_real_bool_real_6, v_int_int_6);
			var v_bool_bool_7: (bool, bool) := (false, true);
			var v_real_bool_real_7: (real, bool, real) := (22.02, false, -14.24);
			var v_int_int_7: (int, int) := (15, 15);
			var v_bool_bool_real_bool_real_int_int_7: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_7, v_real_bool_real_7, v_int_int_7);
			var v_bool_bool_8: (bool, bool) := (true, true);
			var v_real_bool_real_8: (real, bool, real) := (-17.43, false, -21.94);
			var v_int_int_8: (int, int) := (18, 29);
			var v_bool_bool_real_bool_real_int_int_8: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_8, v_real_bool_real_8, v_int_int_8);
			var v_bool_bool_9: (bool, bool) := (false, false);
			var v_real_bool_real_9: (real, bool, real) := (-4.50, true, -27.42);
			var v_int_int_9: (int, int) := (28, 25);
			var v_bool_bool_real_bool_real_int_int_9: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_9, v_real_bool_real_9, v_int_int_9);
			var v_bool_bool_10: (bool, bool) := (false, true);
			var v_real_bool_real_10: (real, bool, real) := (7.59, true, 4.36);
			var v_int_int_10: (int, int) := (19, 5);
			var v_bool_bool_real_bool_real_int_int_10: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_10, v_real_bool_real_10, v_int_int_10);
			var v_bool_bool_11: (bool, bool) := (true, false);
			var v_real_bool_real_11: (real, bool, real) := (-9.79, false, 25.29);
			var v_int_int_11: (int, int) := (15, 19);
			var v_bool_bool_real_bool_real_int_int_11: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_11, v_real_bool_real_11, v_int_int_11);
			var v_bool_bool_12: (bool, bool) := (false, false);
			var v_real_bool_real_12: (real, bool, real) := (12.59, false, 20.27);
			var v_int_int_12: (int, int) := (5, 26);
			var v_bool_bool_real_bool_real_int_int_12: ((bool, bool), (real, bool, real), (int, int)) := (v_bool_bool_12, v_real_bool_real_12, v_int_int_12);
			var v_seq_6: seq<bool> := v_seq_3;
			var v_real_2: real := 12.64;
			var v_bool_10: bool := false;
			var v_seq_4: seq<int> := m_method_7(v_real_2, v_bool_10);
			var v_seq_5: seq<int> := v_seq_4;
			var v_int_14: int := (if (false) then (20) else (23));
			var v_int_15: int := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_14]) else ((match true {
				case _ => 14
			})));
			v_bool_5, v_bool_8, v_bool_7 := (if ((v_bool_9 in (map[true := false, true := true, false := false] - {true, false, true}))) then (((match 14 {
				case _ => multiset({v_bool_bool_real_bool_real_int_int_4, v_bool_bool_real_bool_real_int_int_5})
			}) >= (multiset{v_bool_bool_real_bool_real_int_int_6, v_bool_bool_real_bool_real_int_int_7, v_bool_bool_real_bool_real_int_int_8, v_bool_bool_real_bool_real_int_int_9} - multiset{v_bool_bool_real_bool_real_int_int_10, v_bool_bool_real_bool_real_int_int_11, v_bool_bool_real_bool_real_int_int_12}))) else ((v_bool_bool_11.1 == (if (false) then (true) else (false))))), v_bool_bool_7.1, (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_15]) else (v_bool_bool_7.1));
			assert true;
			expect true;
			var v_bool_14: bool := v_bool_bool_7.1;
			var v_seq_9: seq<int> := [6, -27];
			var v_char_7: char := 'D';
			var v_bool_13: bool := false;
			var v_real_5: real := 14.77;
			var v_map_5: map<int, bool> := m_method_8(v_seq_9, v_char_7, v_bool_13, v_real_5);
			var v_map_6: map<int, bool> := v_map_5;
			var v_bool_int_int_3: (bool, int, int) := (false, 13, -11);
			var v_bool_int_int_4: (bool, int, int) := (true, 19, 0);
			var v_bool_int_int_5: (bool, int, int) := (true, 5, 12);
			var v_seq_10: seq<(bool, int, int)> := [v_bool_int_int_3, v_bool_int_int_4, v_bool_int_int_5];
			var v_int_18: int := 16;
			var v_bool_int_int_6: (bool, int, int) := (false, 11, 22);
			var v_bool_int_int_7: (bool, int, int) := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_18]) else (v_bool_int_int_6));
			var v_bool_15: bool := m_method_6(v_bool_14, v_map_6, v_bool_int_int_7);
			var v_map_8: map<multiset<char>, bool> := (if (false) then (map[multiset{'T', 'n'} := false]) else (map[multiset{'w', 'd'} := true, multiset{} := false, multiset{'S'} := true]));
			var v_multiset_4: multiset<char> := (multiset{'S', 'F', 'L'} * multiset({'T', 'h', 'R'}));
			var v_bool_16: bool := true;
			var v_map_7: map<int, bool> := map[15 := true];
			var v_bool_int_int_8: (bool, int, int) := (true, -14, 17);
			var v_bool_int_int_9: (bool, int, int) := v_bool_int_int_8;
			var v_bool_17: bool := m_method_6(v_bool_16, v_map_7, v_bool_int_int_9);
			var v_bool_20: bool := (true !in map[true := false]);
			var v_map_9: map<bool, bool> := map[true := false, true := false, false := true, false := false];
			var v_bool_19: bool := false;
			var v_bool_21: bool := (if ((v_bool_19 in v_map_9)) then (v_map_9[v_bool_19]) else (true));
			var v_bool_22: bool := v_real_bool_real_12.1;
			var v_bool_23: bool := (match true {
				case _ => false
			});
			var v_seq_12: seq<int> := m_method_10(v_bool_20, v_bool_21, v_bool_22, v_bool_23);
			var v_int_21: int := (if (true) then (29) else (7));
			var v_char_8: char := m_method_3(v_int_21);
			var v_char_9: char := v_char_8;
			var v_map_10: map<bool, bool> := v_map_9;
			var v_seq_13: seq<bool> := [];
			var v_int_22: int := 19;
			var v_bool_24: bool := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_22]) else (false));
			var v_bool_25: bool := (if ((v_bool_24 in v_map_10)) then (v_map_10[v_bool_24]) else ((false in map[false := true, false := false, true := false, false := false, false := true])));
			var v_seq_14: seq<bool> := [false];
			var v_seq_15: seq<bool> := v_seq_14;
			var v_int_23: int := 2;
			var v_int_24: int := safe_index_seq(v_seq_15, v_int_23);
			var v_int_25: int := v_int_24;
			var v_seq_16: seq<bool> := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_25 := true]) else (v_seq_14));
			var v_int_26: int := v_int_24;
			var v_bool_26: bool := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_26]) else ((false in map[false := true])));
			var v_int_real_4: (int, real) := (5, -2.33);
			var v_int_real_5: (int, real) := (29, -4.38);
			var v_int_real_6: (int, real) := (18, 10.88);
			var v_int_real_7: (int, real) := (16, -29.60);
			var v_int_real_8: (int, real) := (8, 3.67);
			var v_int_real_9: (int, real) := (2, 7.89);
			var v_int_real_10: (int, real) := (5, -15.95);
			var v_seq_17: seq<(int, real)> := ([v_int_real_4, v_int_real_5, v_int_real_6] + [v_int_real_7, v_int_real_8, v_int_real_9, v_int_real_10]);
			var v_int_27: int := (if (true) then (10) else (1));
			var v_int_real_11: (int, real) := (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_27]) else (v_int_real_4));
			var v_DT_1_1_19: DT_1<char> := m_method_1(v_char_9, v_bool_25, v_bool_26, v_int_real_11);
			v_int_18, v_bool_19, v_seq_5, v_DT_1_1_17 := v_int_11, (v_bool_15 <==> (if ((v_multiset_4 in v_map_8)) then (v_map_8[v_multiset_4]) else (v_bool_17))), (v_seq_12 + v_seq_5), v_DT_1_1_19;
			return ;
		}
			case _ => {
			var v_int_real_14: (int, real) := (8, -29.90);
			var v_int_real_15: (int, real) := (8, -29.90);
			print "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_7", " ", v_bool_7, " ", "v_int_real_3", " ", (v_int_real_3 == v_int_real_14), " ", "v_int_real_2", " ", (v_int_real_2 == v_int_real_15), " ", "v_bool_6", " ", v_bool_6, " ", "v_DT_1_1_18", " ", v_DT_1_1_18, " ", "v_DT_1_1_17", " ", v_DT_1_1_17, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_char_3", " ", (v_char_3 == 'm'), " ", "v_char_4", " ", (v_char_4 == 'm'), " ", "v_map_2", " ", (v_map_2 == map[]), " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_3", " ", v_seq_3, "\n";
			return ;
		}
		
	}
	
	var v_real_real_1: (real, real) := (26.45, 10.87);
	var v_real_real_2: (real, real) := (11.81, -17.79);
	var v_real_real_3: (real, real) := (7.54, -0.01);
	var v_real_real_4: (real, real) := (-23.07, -7.80);
	var v_real_real_5: (real, real) := (11.72, 17.63);
	var v_real_real_6: (real, real) := (-5.93, 19.97);
	var v_real_real_7: (real, real) := (26.84, 25.16);
	var v_real_real_8: (real, real) := (15.24, 9.74);
	var v_real_real_9: (real, real) := (-24.42, 7.64);
	var v_real_real_10: (real, real) := (24.25, 6.81);
	var v_real_real_11: (real, real) := (-8.67, 7.32);
	var v_real_real_12: (real, real) := (13.52, -14.41);
	var v_real_real_13: (real, real) := (7.65, 21.41);
	var v_real_real_14: (real, real) := (17.33, -24.38);
	var v_real_real_15: (real, real) := (15.16, 16.82);
	var v_seq_128: seq<multiset<(real, real)>> := [multiset{v_real_real_12, v_real_real_13, v_real_real_14, v_real_real_15}];
	var v_int_176: int := 0;
	var v_real_real_16: (real, real) := (9.94, 28.13);
	var v_real_real_17: (real, real) := (-19.79, 26.87);
	var v_real_real_18: (real, real) := (5.31, -6.75);
	var v_real_real_19: (real, real) := (-12.94, -6.74);
	var v_map_68: map<multiset<(real, real)>, int> := map[multiset{v_real_real_1, v_real_real_2, v_real_real_3} := 10, multiset{} := 15, multiset{v_real_real_4, v_real_real_5, v_real_real_6, v_real_real_7} := 18, multiset({v_real_real_8, v_real_real_9}) := 8, multiset({v_real_real_10, v_real_real_11}) := 10][multiset({}) := 8][(if ((|v_seq_128| > 0)) then (v_seq_128[v_int_176]) else (multiset{v_real_real_16, v_real_real_17, v_real_real_18, v_real_real_19})) := (16 * 12)];
	var v_seq_129: seq<multiset<(real, real)>> := v_seq_128;
	var v_array_13: array<bool> := new bool[5];
	v_array_13[0] := true;
	v_array_13[1] := true;
	v_array_13[2] := true;
	v_array_13[3] := true;
	v_array_13[4] := false;
	var v_int_177: int := v_array_13.Length;
	var v_real_real_20: (real, real) := (18.15, 16.15);
	var v_multiset_7: multiset<(real, real)> := (if ((|v_seq_129| > 0)) then (v_seq_129[v_int_177]) else ((multiset({v_real_real_20}) * multiset{})));
	var v_map_67: map<bool, int> := map[false := 14, false := -6][true := 2];
	var v_bool_56: bool := (match 'U' {
		case _ => true
	});
	var v_int_174: int := (if ((v_multiset_7 in v_map_68)) then (v_map_68[v_multiset_7]) else ((if ((v_bool_56 in v_map_67)) then (v_map_67[v_bool_56]) else ((if (false) then (-1) else (26))))));
	var v_DT_1_1_20: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_1: (DT_1<char>, real, char) := (v_DT_1_1_20, 3.44, 'D');
	var v_DT_1_1_21: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_2: (DT_1<char>, real, char) := (v_DT_1_1_21, -6.88, 'S');
	var v_DT_1_1_22: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_3: (DT_1<char>, real, char) := (v_DT_1_1_22, -30.00, 'U');
	var v_DT_1_1_23: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_4: (DT_1<char>, real, char) := (v_DT_1_1_23, -26.30, 'm');
	var v_DT_1_1_24: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_5: (DT_1<char>, real, char) := (v_DT_1_1_24, 23.20, 'b');
	var v_DT_1_1_25: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_6: (DT_1<char>, real, char) := (v_DT_1_1_25, 22.74, 'V');
	var v_DT_1_1_26: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_7: (DT_1<char>, real, char) := (v_DT_1_1_26, 29.04, 'g');
	var v_DT_1_1_27: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_8: (DT_1<char>, real, char) := (v_DT_1_1_27, -24.81, 'W');
	var v_DT_1_1_28: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_9: (DT_1<char>, real, char) := (v_DT_1_1_28, 7.80, 'P');
	var v_DT_1_1_29: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_10: (DT_1<char>, real, char) := (v_DT_1_1_29, -23.49, 'J');
	var v_DT_1_1_30: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_11: (DT_1<char>, real, char) := (v_DT_1_1_30, -0.06, 'm');
	var v_DT_1_1_31: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_12: (DT_1<char>, real, char) := (v_DT_1_1_31, 5.69, 'N');
	var v_DT_1_1_32: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_13: (DT_1<char>, real, char) := (v_DT_1_1_32, -9.08, 'f');
	var v_DT_1_1_33: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_14: (DT_1<char>, real, char) := (v_DT_1_1_33, 10.11, 'L');
	var v_DT_1_1_34: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_15: (DT_1<char>, real, char) := (v_DT_1_1_34, -18.79, 'R');
	var v_DT_1_1_35: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_16: (DT_1<char>, real, char) := (v_DT_1_1_35, 16.09, 'W');
	var v_DT_1_1_36: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_17: (DT_1<char>, real, char) := (v_DT_1_1_36, -19.21, 'g');
	var v_seq_130: seq<map<(DT_1<char>, real, char), int>> := [map[v_DT_1_1_real_char_6 := 15, v_DT_1_1_real_char_7 := 5, v_DT_1_1_real_char_8 := 0, v_DT_1_1_real_char_9 := 4], map[v_DT_1_1_real_char_10 := 4], map[v_DT_1_1_real_char_11 := 6, v_DT_1_1_real_char_12 := 20, v_DT_1_1_real_char_13 := -23, v_DT_1_1_real_char_14 := 26, v_DT_1_1_real_char_15 := 11], map[v_DT_1_1_real_char_16 := 5, v_DT_1_1_real_char_17 := 11]];
	var v_int_178: int := 18;
	var v_DT_1_1_37: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_18: (DT_1<char>, real, char) := (v_DT_1_1_37, 17.27, 'h');
	var v_DT_1_1_38: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_19: (DT_1<char>, real, char) := (v_DT_1_1_38, 11.55, 'y');
	var v_map_70: map<(DT_1<char>, real, char), int> := ((map[v_DT_1_1_real_char_1 := 0, v_DT_1_1_real_char_2 := 8, v_DT_1_1_real_char_3 := 14, v_DT_1_1_real_char_4 := 24, v_DT_1_1_real_char_5 := 15] - {}) + (if ((|v_seq_130| > 0)) then (v_seq_130[v_int_178]) else (map[v_DT_1_1_real_char_18 := 0, v_DT_1_1_real_char_19 := 14])));
	var v_DT_1_1_39: DT_1<char> := DT_1_1;
	var v_DT_1_1_real_char_20: (DT_1<char>, real, char) := (v_DT_1_1_39, 0.71, 'f');
	var v_seq_131: seq<(DT_1<char>, real, char)> := [v_DT_1_1_real_char_20];
	var v_seq_132: seq<(DT_1<char>, real, char)> := (if ((|v_seq_131| > 0)) then (v_seq_131[18..-5]) else (v_seq_131));
	var v_int_179: int := v_int_11;
	var v_DT_1_1_real_char_21: (DT_1<char>, real, char) := (if ((|v_seq_132| > 0)) then (v_seq_132[v_int_179]) else (v_DT_1_1_real_char_4));
	var v_map_69: map<char, int> := map['G' := 2]['M' := 28];
	var v_char_10: char := v_DT_1_1_real_char_20.2;
	var v_seq_133: seq<int> := [22, 21];
	var v_int_180: int := 28;
	var v_int_175: int := (if ((v_DT_1_1_real_char_21 in v_map_70)) then (v_map_70[v_DT_1_1_real_char_21]) else ((if ((v_char_10 in v_map_69)) then (v_map_69[v_char_10]) else ((if ((|v_seq_133| > 0)) then (v_seq_133[v_int_180]) else (1))))));
	while (v_int_174 < v_int_175) 
		decreases v_int_175 - v_int_174;
		invariant (v_int_174 <= v_int_175);
	{
		v_int_174 := (v_int_174 + 1);
		continue;
	}
	var v_bool_bool_real_1: (bool, bool, real) := (false, true, 9.61);
	var v_seq_bool_bool_real_1: (seq<real>, (bool, bool, real)) := ([-18.22, 26.84], v_bool_bool_real_1);
	var v_int_int_bool_1: (int, int, bool) := (4, 0, false);
	var v_bool_bool_real_2: (bool, bool, real) := (true, true, 18.45);
	var v_seq_bool_bool_real_2: (seq<real>, (bool, bool, real)) := ([20.83], v_bool_bool_real_2);
	var v_int_int_bool_2: (int, int, bool) := (15, 28, true);
	var v_int_int_bool_3: (int, int, bool) := (22, 27, false);
	var v_int_int_bool_4: (int, int, bool) := (6, -3, true);
	var v_int_int_bool_5: (int, int, bool) := (24, 22, false);
	var v_bool_bool_real_3: (bool, bool, real) := (false, false, 9.29);
	var v_seq_bool_bool_real_3: (seq<real>, (bool, bool, real)) := ([15.05, 8.77, 29.91], v_bool_bool_real_3);
	var v_int_int_bool_6: (int, int, bool) := (19, 23, false);
	var v_int_int_bool_7: (int, int, bool) := (15, -6, true);
	var v_bool_bool_real_4: (bool, bool, real) := (false, true, 6.06);
	var v_seq_bool_bool_real_4: (seq<real>, (bool, bool, real)) := ([-17.83, 0.50, 27.26, -25.58], v_bool_bool_real_4);
	var v_int_int_bool_8: (int, int, bool) := (14, 8, false);
	var v_int_int_bool_9: (int, int, bool) := (6, 0, true);
	var v_int_int_bool_10: (int, int, bool) := (4, 3, true);
	var v_int_int_bool_11: (int, int, bool) := (-10, 14, true);
	var v_bool_bool_real_5: (bool, bool, real) := (true, true, 7.35);
	var v_seq_bool_bool_real_5: (seq<real>, (bool, bool, real)) := ([29.73, -22.17], v_bool_bool_real_5);
	var v_int_int_bool_12: (int, int, bool) := (-14, 16, false);
	var v_int_int_bool_13: (int, int, bool) := (12, 0, false);
	var v_int_int_bool_14: (int, int, bool) := (4, 6, true);
	var v_int_int_bool_15: (int, int, bool) := (15, 8, true);
	var v_int_int_bool_16: (int, int, bool) := (15, 29, false);
	var v_int_int_bool_17: (int, int, bool) := (13, 25, false);
	var v_int_int_bool_18: (int, int, bool) := (12, 1, true);
	var v_int_int_bool_19: (int, int, bool) := (24, 21, true);
	var v_int_int_bool_20: (int, int, bool) := (-13, -23, false);
	var v_int_int_bool_21: (int, int, bool) := (23, 1, false);
	var v_int_int_bool_22: (int, int, bool) := (2, 18, true);
	var v_int_int_bool_23: (int, int, bool) := (0, 16, true);
	var v_int_int_bool_24: (int, int, bool) := (27, -5, false);
	var v_int_int_bool_25: (int, int, bool) := (15, 16, true);
	var v_int_int_bool_26: (int, int, bool) := (-18, 23, false);
	var v_int_int_bool_27: (int, int, bool) := (26, 21, true);
	var v_int_int_bool_28: (int, int, bool) := (5, 18, true);
	var v_int_int_bool_29: (int, int, bool) := (27, 16, true);
	var v_int_int_bool_30: (int, int, bool) := (21, 3, true);
	var v_int_int_bool_31: (int, int, bool) := (14, -9, false);
	var v_int_int_bool_32: (int, int, bool) := (0, 3, false);
	var v_int_int_bool_33: (int, int, bool) := (19, 14, false);
	var v_int_int_bool_34: (int, int, bool) := (15, 3, true);
	var v_int_int_bool_35: (int, int, bool) := (22, 23, false);
	var v_map_71: map<bool, set<multiset<(int, int, bool)>>> := map[true := {multiset({v_int_int_bool_12, v_int_int_bool_13, v_int_int_bool_14, v_int_int_bool_15}), multiset{v_int_int_bool_16}, multiset{v_int_int_bool_17, v_int_int_bool_18, v_int_int_bool_19, v_int_int_bool_20}}, true := {multiset{v_int_int_bool_21, v_int_int_bool_22, v_int_int_bool_23, v_int_int_bool_24}, multiset({v_int_int_bool_25}), multiset{v_int_int_bool_26, v_int_int_bool_27}, multiset({v_int_int_bool_28})}, true := {multiset{v_int_int_bool_29, v_int_int_bool_30, v_int_int_bool_31}, multiset{v_int_int_bool_32, v_int_int_bool_33, v_int_int_bool_34, v_int_int_bool_35}}];
	var v_bool_57: bool := true;
	var v_int_int_bool_36: (int, int, bool) := (1, 29, false);
	var v_int_int_bool_37: (int, int, bool) := (17, 8, true);
	var v_int_int_bool_38: (int, int, bool) := (3, 7, false);
	var v_int_int_bool_39: (int, int, bool) := (23, 23, true);
	var v_int_int_bool_40: (int, int, bool) := (8, 9, false);
	var v_int_int_bool_41: (int, int, bool) := (5, 17, true);
	var v_int_int_bool_42: (int, int, bool) := (13, 14, true);
	var v_int_int_bool_43: (int, int, bool) := (0, 8, true);
	var v_int_int_bool_44: (int, int, bool) := (0, 1, false);
	var v_int_int_bool_45: (int, int, bool) := (2, 12, false);
	var v_int_int_bool_46: (int, int, bool) := (27, 7, true);
	if ((if (v_array_13[4]) then ((map[multiset{} := v_seq_bool_bool_real_1, multiset{v_int_int_bool_1} := v_seq_bool_bool_real_2, multiset({v_int_int_bool_2, v_int_int_bool_3, v_int_int_bool_4, v_int_int_bool_5}) := v_seq_bool_bool_real_3, multiset({v_int_int_bool_6, v_int_int_bool_7}) := v_seq_bool_bool_real_4, multiset{v_int_int_bool_8, v_int_int_bool_9, v_int_int_bool_10, v_int_int_bool_11} := v_seq_bool_bool_real_5]).Keys) else ((if ((v_bool_57 in v_map_71)) then (v_map_71[v_bool_57]) else ({multiset{v_int_int_bool_36}, multiset({v_int_int_bool_37, v_int_int_bool_38, v_int_int_bool_39})})))) !! (map[true := multiset{v_int_int_bool_40, v_int_int_bool_41, v_int_int_bool_42}, true := multiset({v_int_int_bool_43, v_int_int_bool_44}), true := multiset({v_int_int_bool_45})][true := multiset{v_int_int_bool_46}]).Values) {
		assert true;
		expect true;
		var v_seq_134: seq<bool> := [];
		var v_seq_135: seq<bool> := (if ((|v_seq_134| > 0)) then (v_seq_134[7..0]) else (v_seq_134));
		var v_map_72: map<bool, int> := map[true := 7, true := 3, false := 4, true := 25, true := 4];
		var v_bool_58: bool := false;
		var v_int_181: int := (if ((v_bool_58 in v_map_72)) then (v_map_72[v_bool_58]) else (23));
		var v_seq_136: seq<set<bool>> := [{}, {false, false, false}, {}];
		var v_seq_137: seq<set<bool>> := v_seq_136;
		var v_int_182: int := 10;
		var v_int_183: int := safe_index_seq(v_seq_137, v_int_182);
		var v_int_184: int := v_int_183;
		var v_seq_139: seq<set<bool>> := (if ((|v_seq_136| > 0)) then (v_seq_136[v_int_184 := {true}]) else (v_seq_136));
		var v_seq_138: seq<int> := [18, 8];
		var v_int_185: int := 0;
		var v_int_186: int := (if ((|v_seq_138| > 0)) then (v_seq_138[v_int_185]) else (0));
		var v_map_73: map<bool, set<bool>> := map[true := {}, false := {false}, false := {}, false := {true}];
		var v_bool_59: bool := true;
		if ((if ((|v_seq_135| > 0)) then (v_seq_135[v_int_181]) else ((true <==> false))) in (if ((|v_seq_139| > 0)) then (v_seq_139[v_int_186]) else ((if ((v_bool_59 in v_map_73)) then (v_map_73[v_bool_59]) else ({true, false, false}))))) {
			return ;
		}
		assert true;
		expect true;
	}
	var v_seq_140: seq<bool> := [false, false];
	var v_seq_141: seq<bool> := v_seq_140;
	var v_int_187: int := 21;
	var v_int_188: int := safe_index_seq(v_seq_141, v_int_187);
	var v_int_189: int := v_int_188;
	var v_seq_142: seq<bool> := (if ((match true {
		case _ => false
	})) then ((if ((|v_seq_140| > 0)) then (v_seq_140[v_int_189 := true]) else (v_seq_140))) else (([true, false, true, true] + [true])));
	var v_map_74: map<bool, int> := map[false := 26];
	var v_bool_60: bool := true;
	var v_int_190: int := ((if ((v_bool_60 in v_map_74)) then (v_map_74[v_bool_60]) else (25)) + (if (false) then (18) else (20)));
	match (if ((|v_seq_142| > 0)) then (v_seq_142[v_int_190]) else ((if ((match false {
		case _ => false
	})) then (('d' !in multiset{'z', 'n', 'Q', 'O'})) else ((if (true) then (true) else (true)))))) {
		case _ => {
			return ;
		}
		
	}
	
	var v_map_75: map<bool, seq<int>> := map[true := [14], false := [21, 2], false := [25, 17]];
	var v_bool_61: bool := false;
	var v_seq_143: seq<int> := (if ((v_bool_61 in v_map_75)) then (v_map_75[v_bool_61]) else ([19]));
	var v_seq_144: seq<int> := v_seq_143;
	var v_real_real_int_3: (real, real, int) := (-12.66, 21.84, 13);
	var v_bool_real_3: (bool, real) := (false, -26.25);
	var v_real_bool_5: (real, bool) := (8.70, true);
	var v_real_real_int_bool_real_real_bool_1: ((real, real, int), (bool, real), (real, bool)) := (v_real_real_int_3, v_bool_real_3, v_real_bool_5);
	var v_real_real_int_4: (real, real, int) := (-9.97, -23.66, 7);
	var v_bool_real_4: (bool, real) := (false, 1.94);
	var v_real_bool_6: (real, bool) := (-2.89, false);
	var v_real_real_int_bool_real_real_bool_2: ((real, real, int), (bool, real), (real, bool)) := (v_real_real_int_4, v_bool_real_4, v_real_bool_6);
	var v_map_76: map<((real, real, int), (bool, real), (real, bool)), int> := map[v_real_real_int_bool_real_real_bool_1 := 15, v_real_real_int_bool_real_real_bool_2 := 27];
	var v_real_real_int_5: (real, real, int) := (19.75, -2.20, 4);
	var v_bool_real_5: (bool, real) := (true, 20.12);
	var v_real_bool_7: (real, bool) := (8.26, false);
	var v_real_real_int_bool_real_real_bool_3: ((real, real, int), (bool, real), (real, bool)) := (v_real_real_int_5, v_bool_real_5, v_real_bool_7);
	var v_real_real_int_bool_real_real_bool_4: ((real, real, int), (bool, real), (real, bool)) := v_real_real_int_bool_real_real_bool_3;
	var v_int_193: int := (if ((v_real_real_int_bool_real_real_bool_4 in v_map_76)) then (v_map_76[v_real_real_int_bool_real_real_bool_4]) else (25));
	var v_int_194: int := safe_index_seq(v_seq_144, v_int_193);
	var v_int_195: int := v_int_194;
	var v_real_real_real_1: (real, real, real) := (-11.15, -14.65, -26.51);
	var v_real_real_21: (real, real) := (-28.86, 11.03);
	var v_real_real_real_real_real_1: ((real, real, real), (real, real)) := (v_real_real_real_1, v_real_real_21);
	var v_real_real_real_2: (real, real, real) := (9.20, 5.32, 20.43);
	var v_real_real_22: (real, real) := (4.19, -23.62);
	var v_real_real_real_real_real_2: ((real, real, real), (real, real)) := (v_real_real_real_2, v_real_real_22);
	var v_real_real_real_3: (real, real, real) := (29.25, -28.54, -19.82);
	var v_real_real_23: (real, real) := (1.33, 28.18);
	var v_real_real_real_real_real_3: ((real, real, real), (real, real)) := (v_real_real_real_3, v_real_real_23);
	var v_real_real_real_4: (real, real, real) := (18.46, 9.36, -3.20);
	var v_real_real_24: (real, real) := (15.27, -20.60);
	var v_real_real_real_real_real_4: ((real, real, real), (real, real)) := (v_real_real_real_4, v_real_real_24);
	var v_real_real_real_5: (real, real, real) := (19.73, 24.68, -24.62);
	var v_real_real_25: (real, real) := (25.00, -21.90);
	var v_real_real_real_real_real_5: ((real, real, real), (real, real)) := (v_real_real_real_5, v_real_real_25);
	var v_array_14: array<((real, real, real), (real, real))> := new ((real, real, real), (real, real))[5] [v_real_real_real_real_real_1, v_real_real_real_real_real_2, v_real_real_real_real_real_3, v_real_real_real_real_real_4, v_real_real_real_real_real_5];
	var v_seq_145: seq<int> := (if ((|v_seq_143| > 0)) then (v_seq_143[v_int_195 := v_array_14.Length]) else (v_seq_143));
	var v_int_196: int := v_int_int_bool_21.1;
	var v_seq_146: seq<int> := [];
	var v_seq_147: seq<int> := (if ((|v_seq_146| > 0)) then (v_seq_146[13..0]) else (v_seq_146));
	var v_int_197: int := (match 3 {
		case _ => 1
	});
	var v_int_191: int := (if ((|v_seq_145| > 0)) then (v_seq_145[v_int_196]) else ((if ((|v_seq_147| > 0)) then (v_seq_147[v_int_197]) else ((match false {
		case _ => 18
	})))));
	var v_int_192: int := v_int_int_bool_31.0;
	while (v_int_191 < v_int_192) 
		decreases v_int_192 - v_int_191;
		invariant (v_int_191 <= v_int_192);
	{
		v_int_191 := (v_int_191 + 1);
		assert true;
		expect true;
		return ;
	}
	var v_seq_148: seq<int> := v_seq_143;
	var v_int_200: int := (match false {
		case _ => 27
	});
	var v_seq_149: seq<int> := v_seq_145;
	var v_int_201: int := (-1 / 10);
	var v_map_77: map<bool, int> := map[true := 14];
	var v_bool_62: bool := false;
	var v_int_198: int := (match true {
		case _ => ((if ((v_bool_62 in v_map_77)) then (v_map_77[v_bool_62]) else (29)) * (if (false) then (1) else (2)))
	});
	var v_array_15: array<bool> := new bool[3] [false, true, false];
	var v_array_16: array<bool> := new bool[4] [false, false, false, false];
	var v_map_78: map<bool, bool> := map[true := true, false := false, true := true];
	var v_bool_63: bool := true;
	var v_int_199: int := (match true {
		case _ => (if ((if ((v_bool_63 in v_map_78)) then (v_map_78[v_bool_63]) else (true))) then ((match true {
			case _ => 19
		})) else ((1 / 4)))
	});
	while (v_int_198 < v_int_199) 
		decreases v_int_199 - v_int_198;
		invariant (v_int_198 <= v_int_199);
	{
		v_int_198 := (v_int_198 + 1);
		var v_map_81: map<bool, bool> := map[true := false, true := false, true := true, true := false, true := true][true := true][!(true) := (if (true) then (false) else (false))];
		var v_map_79: map<bool, bool> := map[false := false, false := false][false := false];
		var v_bool_64: bool := (if (false) then (true) else (false));
		var v_bool_66: bool := (if ((v_bool_64 in v_map_79)) then (v_map_79[v_bool_64]) else ((false || true)));
		var v_map_80: map<bool, bool> := map[true := true, false := false, true := false];
		var v_bool_65: bool := true;
		if (if ((v_bool_66 in v_map_81)) then (v_map_81[v_bool_66]) else ((if ((if ((v_bool_65 in v_map_80)) then (v_map_80[v_bool_65]) else (false))) then ((match true {
			case _ => false
		})) else ((multiset{false, true} <= multiset{true, true, true, false}))))) {
			
		}
		var v_seq_150: seq<bool> := [false, true, true, false];
		var v_seq_151: seq<bool> := v_seq_150;
		var v_int_202: int := 2;
		var v_int_203: int := safe_index_seq(v_seq_151, v_int_202);
		var v_int_204: int := v_int_203;
		var v_seq_152: seq<bool> := (if ((|v_seq_150| > 0)) then (v_seq_150[v_int_204 := true]) else (v_seq_150));
		var v_seq_153: seq<bool> := v_seq_152;
		var v_array_17: array<bool> := new bool[3];
		v_array_17[0] := false;
		v_array_17[1] := false;
		v_array_17[2] := true;
		var v_int_205: int := v_array_17.Length;
		var v_int_206: int := safe_index_seq(v_seq_153, v_int_205);
		var v_int_207: int := v_int_206;
		var v_seq_158: seq<bool> := (if ((|v_seq_152| > 0)) then (v_seq_152[v_int_207 := (if (true) then (true) else (true))]) else (v_seq_152));
		var v_seq_154: seq<int> := [-7];
		var v_seq_155: seq<int> := v_seq_154;
		var v_int_208: int := 24;
		var v_int_209: int := safe_index_seq(v_seq_155, v_int_208);
		var v_int_210: int := v_int_209;
		var v_seq_157: seq<int> := (if ((|v_seq_154| > 0)) then (v_seq_154[v_int_210 := 21]) else (v_seq_154));
		var v_seq_156: seq<int> := [7, 18];
		var v_int_211: int := -15;
		var v_int_212: int := (if ((|v_seq_156| > 0)) then (v_seq_156[v_int_211]) else (0));
		var v_map_82: map<bool, int> := map[true := 20, true := 1, true := 7, true := 11];
		var v_bool_67: bool := false;
		var v_int_213: int := (if ((|v_seq_157| > 0)) then (v_seq_157[v_int_212]) else ((if ((v_bool_67 in v_map_82)) then (v_map_82[v_bool_67]) else (28))));
		var v_seq_159: seq<bool> := [];
		var v_seq_160: seq<bool> := (if ((|v_seq_159| > 0)) then (v_seq_159[9..18]) else (v_seq_159));
		var v_map_83: map<bool, int> := map[true := 20];
		var v_bool_68: bool := true;
		var v_int_214: int := (if ((v_bool_68 in v_map_83)) then (v_map_83[v_bool_68]) else (25));
		if (if ((|v_seq_158| > 0)) then (v_seq_158[v_int_213]) else ((if ((|v_seq_160| > 0)) then (v_seq_160[v_int_214]) else (v_bool_60)))) {
			var v_seq_161: seq<bool> := [];
			var v_int_215: int := 20;
			var v_map_84: map<set<bool>, bool> := map[{} := true, {false, true, false} := false, {false} := false, {false, true, true} := false, {false} := false];
			var v_set_2: set<bool> := {};
			var v_seq_162: seq<bool> := [];
			var v_int_216: int := -12;
			var v_map_85: map<bool, bool> := map[true := false, true := false, true := true, true := true, true := true];
			var v_bool_69: bool := true;
			var v_map_88: map<bool, bool> := map[false := false, false := true, true := true, true := false, false := false][false := false][(if (false) then (false) else (true)) := (if ((v_bool_69 in v_map_85)) then (v_map_85[v_bool_69]) else (true))];
			var v_map_86: map<bool, bool> := map[true := false, true := false];
			var v_bool_70: bool := false;
			var v_bool_72: bool := (match true {
				case _ => (if ((v_bool_70 in v_map_86)) then (v_map_86[v_bool_70]) else (false))
			});
			var v_map_87: map<bool, bool> := map[false := false, true := false];
			var v_bool_71: bool := true;
			var v_seq_163: seq<bool> := [false, false, false, false];
			var v_int_217: int := 28;
			var v_seq_164: seq<bool> := [true, true, true];
			var v_int_218: int := 6;
			v_array_17[1], v_bool_64, v_array_13[3] := (if ((match true {
				case _ => (if ((|v_seq_161| > 0)) then (v_seq_161[v_int_215]) else (false))
			})) then ((match false {
				case _ => (if ((v_set_2 in v_map_84)) then (v_map_84[v_set_2]) else (false))
			})) else ((if (v_int_int_bool_17.2) then ((if ((|v_seq_162| > 0)) then (v_seq_162[v_int_216]) else (true))) else (v_int_int_bool_42.2)))), (if ((v_bool_72 in v_map_88)) then (v_map_88[v_bool_72]) else ((if ((if ((v_bool_71 in v_map_87)) then (v_map_87[v_bool_71]) else (false))) then ((if (false) then (false) else (true))) else ((match true {
				case _ => false
			}))))), (match true {
				case _ => (if (v_bool_60) then ((if ((|v_seq_163| > 0)) then (v_seq_163[v_int_217]) else (false))) else ((if ((|v_seq_164| > 0)) then (v_seq_164[v_int_218]) else (false))))
			});
			var v_map_89: map<int, multiset<bool>> := map[2 := multiset{true, false}, 0 := multiset{false, true, true, false}, 17 := multiset{false, true, true, true}, 20 := multiset{false, true}];
			var v_int_219: int := -25;
			var v_map_92: map<bool, multiset<bool>> := map[true := multiset({false, false, false}), true := multiset({false})][true := multiset{true, true, true, true}][(true !in map[false := true, true := false, false := true, false := false]) := (if ((v_int_219 in v_map_89)) then (v_map_89[v_int_219]) else (multiset{false, false, false, true}))];
			var v_map_90: map<int, bool> := map[19 := false, -25 := false][14 := false];
			var v_int_220: int := (6 % 24);
			var v_bool_73: bool := (if ((v_int_220 in v_map_90)) then (v_map_90[v_int_220]) else (v_array_13[3]));
			var v_map_91: map<int, multiset<bool>> := map[26 := multiset({}), 23 := multiset{true, false, true}, 15 := multiset{true, true}, 8 := multiset{true, true, true, true}, 10 := multiset{false, true, false}][1 := multiset({false, false})];
			var v_int_222: int := v_int_int_bool_36.0;
			var v_seq_165: seq<multiset<bool>> := [multiset({true, true, false, false}), multiset({false}), multiset{true, false}];
			var v_int_221: int := 10;
			var v_seq_166: seq<int> := [14, 26];
			var v_int_223: int := 29;
			var v_seq_167: seq<int> := [11];
			var v_int_224: int := 23;
			var v_seq_168: seq<bool> := [true, true, false, false];
			var v_int_225: int := 14;
			var v_map_93: map<char, bool> := map['O' := true, 'z' := false, 'h' := true, 'K' := false]['h' := true][v_DT_1_1_real_char_2.2 := (if ((|v_seq_168| > 0)) then (v_seq_168[v_int_225]) else (true))];
			var v_char_11: char := v_DT_1_1_real_char_8.2;
			var v_seq_169: seq<set<char>> := [{}, {'N', 's'}];
			var v_int_226: int := 25;
			var v_map_94: map<char, bool> := (match 'C' {
				case _ => map['A' := false]['L' := false]
			});
			var v_char_12: char := (match 'f' {
				case _ => (match 'E' {
					case _ => 'A'
				})
			});
			var v_seq_170: seq<bool> := [false, false];
			var v_int_227: int := 17;
			var v_multiset_8: multiset<bool>, v_bool_74: bool, v_bool_75: bool, v_bool_76: bool, v_bool_77: bool := (if ((v_bool_73 in v_map_92)) then (v_map_92[v_bool_73]) else ((if ((v_int_222 in v_map_91)) then (v_map_91[v_int_222]) else ((if ((|v_seq_165| > 0)) then (v_seq_165[v_int_221]) else (multiset({false, true, false}))))))), (v_int_int_bool_23.1 >= (match -7 {
				case _ => (match 12 {
					case _ => 22
				})
			})), (if ((v_char_11 in v_map_93)) then (v_map_93[v_char_11]) else (((if ((|v_seq_169| > 0)) then (v_seq_169[v_int_226]) else ({'J'})) == (match 'M' {
				case _ => {'n'}
			})))), v_bool_real_4.0, (if ((v_char_12 in v_map_94)) then (v_map_94[v_char_12]) else ((if ((if ((|v_seq_170| > 0)) then (v_seq_170[v_int_227]) else (true))) then ((match 'r' {
				case _ => false
			})) else (('a' in {'M'})))));
		} else {
			var v_map_95: map<char, char> := map['q' := 'J', 'd' := 'g', 'c' := 'c', 'Q' := 'x', 'F' := 'T'];
			var v_char_13: char := 'T';
			var v_map_97: map<char, char> := (map['m' := 'X'] + map['S' := 'j', 'W' := 'l', 'F' := 'H', 'O' := 'i', 'J' := 'a'])[v_DT_1_1_real_char_13.2 := (if ((v_char_13 in v_map_95)) then (v_map_95[v_char_13]) else ('F'))];
			var v_map_96: map<char, char> := map['q' := 'F'];
			var v_char_14: char := 'F';
			var v_char_15: char := (match 'D' {
				case _ => v_DT_1_1_real_char_13.2
			});
			var v_seq_171: seq<bool> := [false, false, true, false];
			var v_seq_172: seq<bool> := (if ((|v_seq_171| > 0)) then (v_seq_171[29..4]) else (v_seq_171));
			var v_int_228: int := (match 'f' {
				case _ => 16
			});
			var v_seq_173: seq<char> := ['u', 'h', 'x'];
			var v_int_229: int := 28;
			var v_seq_174: seq<bool> := [true, true];
			var v_int_230: int := 12;
			v_char_3, v_char_4, v_char_10 := (if ((v_char_15 in v_map_97)) then (v_map_97[v_char_15]) else ((match 'O' {
				case _ => (match 'y' {
					case _ => 'd'
				})
			}))), (if ((if ((|v_seq_172| > 0)) then (v_seq_172[v_int_228]) else (v_real_bool_6.1))) then ((match 'i' {
				case _ => (if (true) then ('m') else ('Q'))
			})) else ((if ((if ((|v_seq_174| > 0)) then (v_seq_174[v_int_230]) else (false))) then ((match 'Z' {
				case _ => 'n'
			})) else (v_DT_1_1_real_char_12.2)))), v_DT_1_1_real_char_19.2;
		}
		var v_seq_175: seq<char> := [];
		var v_seq_176: seq<char> := v_seq_175;
		var v_int_231: int := 17;
		var v_int_232: int := safe_index_seq(v_seq_176, v_int_231);
		var v_int_233: int := v_int_232;
		var v_seq_177: seq<char> := (if ((|v_seq_175| > 0)) then (v_seq_175[v_int_233 := 'E']) else (v_seq_175));
		var v_seq_178: seq<char> := v_seq_177;
		var v_int_234: int := (28.95).Floor;
		var v_int_235: int := safe_index_seq(v_seq_178, v_int_234);
		var v_int_236: int := v_int_235;
		var v_seq_180: seq<char> := (if ((|v_seq_177| > 0)) then (v_seq_177[v_int_236 := (if (false) then ('S') else ('b'))]) else (v_seq_177));
		var v_seq_179: seq<int> := [23, -18, 11, 21];
		var v_int_237: int := 2;
		var v_int_238: int := ((if ((|v_seq_179| > 0)) then (v_seq_179[v_int_237]) else (18)) % v_int_int_bool_38.0);
		match (if ((|v_seq_180| > 0)) then (v_seq_180[v_int_238]) else (v_DT_1_1_real_char_4.2)) {
			case _ => {
				var v_seq_184: seq<bool> := [true];
				var v_seq_185: seq<bool> := (if ((|v_seq_184| > 0)) then (v_seq_184[29..5]) else (v_seq_184));
				var v_int_243: int := (match 'i' {
					case _ => 0
				});
				var v_map_102: map<char, bool> := map['C' := false, 'e' := true, 'z' := true, 'r' := false, 'Q' := false];
				var v_char_20: char := 'c';
				var v_map_103: map<char, bool> := map['n' := false, 'P' := true, 'S' := false, 'l' := false, 'J' := false]['g' := true];
				var v_char_21: char := (if (true) then ('Z') else ('n'));
				var v_seq_186: seq<bool> := [true, true];
				var v_int_244: int := 16;
				if (match 't' {
					case _ => (if ((v_char_21 in v_map_103)) then (v_map_103[v_char_21]) else ((if ((|v_seq_186| > 0)) then (v_seq_186[v_int_244]) else (false))))
				}) {
					return ;
				} else {
					return ;
				}
			}
			
		}
		
	}
	var v_int_245: int := (|map['B' := 'K', 'X' := 'K']['y' := 'i']| % v_int_int_bool_32.1);
	var v_seq_187: seq<char> := ['A'];
	var v_int_247: int := 2;
	var v_map_106: map<char, int> := map['M' := 10]['f' := -20][(if ((|v_seq_187| > 0)) then (v_seq_187[v_int_247]) else ('N')) := (match 'q' {
		case _ => -8
	})];
	var v_map_104: map<char, char> := map['o' := 'q']['i' := 'G'];
	var v_char_22: char := (if (false) then ('J') else ('K'));
	var v_seq_188: seq<char> := ['X'];
	var v_int_248: int := -18;
	var v_char_24: char := (if ((v_char_22 in v_map_104)) then (v_map_104[v_char_22]) else ((if ((|v_seq_188| > 0)) then (v_seq_188[v_int_248]) else ('P'))));
	var v_map_105: map<char, bool> := map['U' := false, 'r' := true, 'I' := true, 'x' := true, 'a' := false];
	var v_char_23: char := 'k';
	var v_int_246: int := (if ((v_char_24 in v_map_106)) then (v_map_106[v_char_24]) else ((if ((if ((v_char_23 in v_map_105)) then (v_map_105[v_char_23]) else (false))) then ((match 'p' {
		case _ => -11
	})) else ((match 'z' {
		case _ => 20
	})))));
	while (v_int_245 < v_int_246) 
		decreases v_int_246 - v_int_245;
		invariant (v_int_245 <= v_int_246);
	{
		v_int_245 := (v_int_245 + 1);
		assert true;
		expect true;
	}
	assert true;
	expect true;
	return ;
}
