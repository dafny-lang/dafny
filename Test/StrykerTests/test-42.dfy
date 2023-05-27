// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1 | DT_1_2(DT_1_2_1: T_1, DT_1_2_2: T_1) | DT_1_3
datatype DT_2<T_2, T_3> = DT_2_1 | DT_2_3(DT_2_3_1: T_3) | DT_2_4(DT_2_4_1: T_2, DT_2_4_2: T_3, DT_2_4_3: T_3)
datatype DT_3 = DT_3_1 | DT_3_2(DT_3_2_1: multiset<real>)
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: int) returns (ret_1: seq<int>)
{
	match 'V' {
		case _ => {
			
		}
		
	}
	
	return [];
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: bool, p_m_method_8_2: seq<int>, p_m_method_8_3: map<bool, int>, p_m_method_8_4: int) returns (ret_1: array<real>)
{
	var v_array_3: array<real> := new real[3] [21.16, 17.72, 0.68];
	return v_array_3;
}

method m_method_7(p_m_method_7_1: DT_2<real, bool>, p_m_method_7_2: seq<int>, p_m_method_7_3: (bool, int, int), p_m_method_7_4: int) returns (ret_1: array<real>)
{
	var v_char_7: char := (if (true) then ('r') else ('d'));
	var v_char_8: char := m_method_1(v_char_7);
	v_char_8 := v_char_8;
	if (if (false) then (true) else (true)) {
		
	}
	if p_m_method_7_1.DT_2_4_3 {
		assert true;
		expect true;
	} else {
		var v_map_6: map<char, bool> := map['U' := false, 'U' := true];
		var v_char_9: char := 'T';
		var v_bool_9: bool, v_multiset_1: multiset<char>, v_bool_10: bool := (20 !in []), (multiset({}) * multiset({'t', 'N'})), (if ((v_char_9 in v_map_6)) then (v_map_6[v_char_9]) else (true));
		var v_DT_1_3_12: DT_1<int> := DT_1_3;
		var v_DT_1_3_13: DT_1<int> := DT_1_3;
		var v_DT_1_3_14: DT_1<int> := DT_1_3;
		var v_seq_12: seq<DT_1<int>> := [v_DT_1_3_12, v_DT_1_3_13, v_DT_1_3_14];
		var v_int_33: int := 20;
		var v_DT_1_3_15: DT_1<int> := DT_1_3;
		v_DT_1_3_14 := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_33]) else (v_DT_1_3_15));
		var v_bool_11: bool := false;
		var v_seq_13: seq<int> := [7, 8, 19];
		var v_map_7: map<bool, int> := map[true := 18, false := 2, false := 15];
		var v_int_34: int := 11;
		var v_array_4: array<real> := m_method_8(v_bool_11, v_seq_13, v_map_7, v_int_34);
		return v_array_4;
	}
	var v_seq_14: seq<array<real>> := [];
	var v_int_35: int := 10;
	var v_array_5: array<real> := new real[3] [-14.53, -15.48, -23.41];
	return (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_35]) else (v_array_5));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: bool) returns (ret_1: DT_2<int, real>)
{
	var v_DT_2_1_3: DT_2<int, real> := DT_2_1;
	var v_DT_2_1_4: DT_2<int, real> := DT_2_1;
	return (match false {
		case _ => v_DT_2_1_4
	});
}

method m_method_5(p_m_method_5_1: DT_2<real, real>) returns (ret_1: seq<DT_1<int>>)
{
	var v_int_23: int := 25;
	var v_int_24: int := 12;
	while (v_int_23 < v_int_24) 
		decreases v_int_24 - v_int_23;
		invariant (v_int_23 <= v_int_24);
	{
		v_int_23 := (v_int_23 + 1);
		if false {
			var v_DT_1_3_3: DT_1<int> := DT_1_3;
			var v_DT_1_3_4: DT_1<int> := DT_1_3;
			var v_DT_1_3_5: DT_1<int> := DT_1_3;
			return [v_DT_1_3_3, v_DT_1_3_4, v_DT_1_3_5];
		} else {
			
		}
		assert true;
		expect true;
		var v_int_26: int, v_int_27: int := 0, 27;
		for v_int_25 := v_int_26 to v_int_27 
			invariant (v_int_27 - v_int_25 >= 0)
		{
			
		}
		assert true;
		expect true;
		return [];
	}
	var v_DT_1_3_6: DT_1<int> := DT_1_3;
	var v_DT_1_3_7: DT_1<int> := DT_1_3;
	var v_DT_1_3_8: DT_1<int> := DT_1_3;
	return [v_DT_1_3_6, v_DT_1_3_7, v_DT_1_3_8];
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: bool, p_m_method_4_3: char) returns (ret_1: map<bool, int>)
	requires ((p_m_method_4_2 == false) && (p_m_method_4_1 == 'N') && (p_m_method_4_3 == 'y'));
	ensures (((p_m_method_4_2 == false) && (p_m_method_4_1 == 'N') && (p_m_method_4_3 == 'y')) ==> ((ret_1 == map[false := 2, true := 12])));
{
	print "p_m_method_4_1", " ", (p_m_method_4_1 == 'N'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'y'), " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return map[false := 2, true := 12];
}

method m_method_3(p_m_method_3_1: map<bool, bool>, p_m_method_3_2: DT_1<int>, p_m_method_3_3: DT_2<int, real>, p_m_method_3_4: array<real>) returns (ret_1: bool)
	requires ((p_m_method_3_1 == map[false := false]) && (p_m_method_3_3.DT_2_1? && ((p_m_method_3_3 == DT_2_1))) && (p_m_method_3_2.DT_1_3? && ((p_m_method_3_2 == DT_1_3))) && p_m_method_3_4.Length == 3 && (-18.08 < p_m_method_3_4[0] < -17.88) && (26.05 < p_m_method_3_4[1] < 26.25) && (5.86 < p_m_method_3_4[2] < 6.06));
	ensures (((p_m_method_3_1 == map[false := false]) && (p_m_method_3_3.DT_2_1? && ((p_m_method_3_3 == DT_2_1))) && (p_m_method_3_2.DT_1_3? && ((p_m_method_3_2 == DT_1_3))) && p_m_method_3_4.Length == 3 && (-18.08 < p_m_method_3_4[0] < -17.88) && (26.05 < p_m_method_3_4[1] < 26.25) && (5.86 < p_m_method_3_4[2] < 6.06)) ==> ((ret_1 == true)));
{
	print "p_m_method_3_4[2]", " ", (p_m_method_3_4[2] == 5.96), " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_4[1]", " ", (p_m_method_3_4[1] == 26.15), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == map[false := false]), " ", "p_m_method_3_4[0]", " ", (p_m_method_3_4[0] == -17.98), " ", "p_m_method_3_4", " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
	return true;
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

method m_method_2(p_m_method_2_1: (int, real, real)) returns (ret_1: bool)
	requires (((p_m_method_2_1).0 == 9) && (11.03 < (p_m_method_2_1).1 < 11.23) && (3.69 < (p_m_method_2_1).2 < 3.89));
	ensures ((((p_m_method_2_1).0 == 9) && (11.03 < (p_m_method_2_1).1 < 11.23) && (3.69 < (p_m_method_2_1).2 < 3.89)) ==> ((ret_1 == true)));
{
	var v_map_2: map<bool, bool> := map[false := false];
	var v_DT_1_3_1: DT_1<int> := DT_1_3;
	var v_DT_1_3_2: DT_1<int> := v_DT_1_3_1;
	var v_DT_2_1_1: DT_2<int, real> := DT_2_1;
	var v_DT_2_1_2: DT_2<int, real> := v_DT_2_1_1;
	var v_array_1: array<real> := new real[3] [-17.98, 26.15, 5.96];
	var v_array_2: array<real> := v_array_1;
	var v_bool_4: bool := m_method_3(v_map_2, v_DT_1_3_2, v_DT_2_1_2, v_array_2);
	var v_int_real_real_11: (int, real, real) := (9, 11.13, 3.79);
	print "v_DT_1_3_1", " ", v_DT_1_3_1, " ", "v_DT_1_3_2", " ", v_DT_1_3_2, " ", "v_bool_4", " ", v_bool_4, " ", "v_map_2", " ", (v_map_2 == map[false := false]), " ", "p_m_method_2_1.0", " ", p_m_method_2_1.0, " ", "p_m_method_2_1.1", " ", (p_m_method_2_1.1 == 11.13), " ", "p_m_method_2_1", " ", (p_m_method_2_1 == v_int_real_real_11), " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "p_m_method_2_1.2", " ", (p_m_method_2_1.2 == 3.79), " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[1]", " ", (v_array_1[1] == 26.15), " ", "v_array_1[2]", " ", (v_array_1[2] == 5.96), " ", "v_array_1[0]", " ", (v_array_1[0] == -17.98), "\n";
	return v_bool_4;
}

method m_method_1(p_m_method_1_1: char) returns (ret_1: char)
	requires ((p_m_method_1_1 == 'd'));
	ensures (((p_m_method_1_1 == 'd')) ==> ((ret_1 == 'R')));
{
	var v_int_int_bool_1: (int, int, bool) := (19, 18, false);
	var v_int_int_int_1: (int, int, int) := (19, 13, 8);
	var v_int_int_bool_int_int_int_bool_1: ((int, int, bool), (int, int, int), bool) := (v_int_int_bool_1, v_int_int_int_1, true);
	var v_bool_1: bool, v_int_int_bool_int_int_int_bool_2: ((int, int, bool), (int, int, int), bool), v_seq_4: seq<multiset<int>>, v_char_1: char := true, v_int_int_bool_int_int_int_bool_1, [], 'U';
	match 21.34 {
		case 25.53 => {
			var v_bool_2: bool, v_bool_3: bool, v_int_8: int := true, true, 2;
			var v_map_1: map<set<real>, char> := map[{21.38, -10.17} := 'F', {15.50} := 'Y', {-8.04, -17.66, -15.34} := 't', {} := 'j'];
			var v_int_9: int, v_int_10: int := 1, 15;
			var v_int_11: int := 18;
			var v_int_12: int := 21;
			while (v_int_11 < v_int_12) 
				decreases v_int_12 - v_int_11;
				invariant (v_int_11 <= v_int_12);
			{
				v_int_11 := (v_int_11 + 1);
			}
			var v_int_13: int := 16;
			var v_int_14: int := 21;
			while (v_int_13 < v_int_14) 
				decreases v_int_14 - v_int_13;
				invariant (v_int_13 <= v_int_14);
			{
				v_int_13 := (v_int_13 + 1);
			}
		}
			case _ => {
			print "v_int_int_bool_int_int_int_bool_1.1", " ", v_int_int_bool_int_int_int_bool_1.1, " ", "v_bool_1", " ", v_bool_1, " ", "v_char_1", " ", (v_char_1 == 'U'), " ", "v_int_int_bool_int_int_int_bool_1.0", " ", v_int_int_bool_int_int_int_bool_1.0, " ", "v_int_int_bool_int_int_int_bool_1.2", " ", v_int_int_bool_int_int_int_bool_1.2, " ", "v_int_int_bool_int_int_int_bool_1", " ", v_int_int_bool_int_int_int_bool_1, " ", "v_int_int_bool_int_int_int_bool_2", " ", v_int_int_bool_int_int_int_bool_2, " ", "v_int_int_bool_1", " ", v_int_int_bool_1, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'd'), " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_int_int_bool_1.1", " ", v_int_int_bool_1.1, " ", "v_int_int_bool_1.2", " ", v_int_int_bool_1.2, " ", "v_int_int_int_1.2", " ", v_int_int_int_1.2, " ", "v_int_int_bool_1.0", " ", v_int_int_bool_1.0, " ", "v_int_int_int_1", " ", v_int_int_int_1, " ", "v_int_int_int_1.0", " ", v_int_int_int_1.0, " ", "v_int_int_int_1.1", " ", v_int_int_int_1.1, "\n";
			return 'R';
		}
		
	}
	
	return 'D';
}

method m_method_10(p_m_method_10_1: DT_2<real, real>, p_m_method_10_2: bool) returns (ret_1: real)
{
	var v_int_41: int := 4;
	var v_int_42: int := 13;
	while (v_int_41 < v_int_42) 
		decreases v_int_42 - v_int_41;
		invariant (v_int_41 <= v_int_42);
	{
		v_int_41 := (v_int_41 + 1);
		var v_int_43: int := 3;
		var v_int_44: int := 10;
		while (v_int_43 < v_int_44) 
			decreases v_int_44 - v_int_43;
			invariant (v_int_43 <= v_int_44);
		{
			v_int_43 := (v_int_43 + 1);
			return 2.13;
		}
	}
	var v_set_1: set<seq<bool>>, v_bool_13: bool := {[], [true, true], [true, false, true, false], []}, true;
	assert true;
	expect true;
	return -0.52;
}

method m_method_11(p_m_method_11_1: bool, p_m_method_11_2: char) returns (ret_1: seq<DT_3>)
{
	var v_bool_17: bool, v_bool_18: bool, v_bool_19: bool := true, true, false;
	var v_int_54: int, v_int_55: int := 25, 9;
	for v_int_53 := v_int_54 to v_int_55 
		invariant (v_int_55 - v_int_53 >= 0)
	{
		var v_DT_3_1_1: DT_3 := DT_3_1;
		return [v_DT_3_1_1];
	}
	var v_DT_3_1_2: DT_3 := DT_3_1;
	var v_DT_3_1_3: DT_3 := DT_3_1;
	var v_DT_3_1_4: DT_3 := DT_3_1;
	return [v_DT_3_1_2, v_DT_3_1_3, v_DT_3_1_4];
}

method Main() returns ()
{
	var v_seq_3: seq<map<char, bool>> := [map['f' := false, 'B' := false, 'Z' := true, 'y' := false], map['H' := false, 'E' := false, 'G' := true]];
	var v_int_7: int := 26;
	var v_seq_39: seq<map<char, bool>> := v_seq_3;
	var v_int_77: int := v_int_7;
	var v_int_78: int := safe_index_seq(v_seq_39, v_int_77);
	v_int_7 := v_int_78;
	var v_map_3: map<char, bool> := ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (map['w' := true, 'V' := true, 'U' := true])) - (if (false) then ({'z', 'g'}) else ({'l'})));
	var v_char_2: char := 'd';
	var v_char_3: char := m_method_1(v_char_2);
	var v_char_4: char := (match 'a' {
		case 'Z' => (if (false) then ('x') else ('u'))
		case _ => v_char_3
	});
	var v_int_real_real_1: (int, real, real) := (9, 11.13, 3.79);
	var v_int_real_real_2: (int, real, real) := (7, 22.20, 19.13);
	var v_int_real_real_3: (int, real, real) := (13, 8.75, 15.28);
	var v_int_real_real_4: (int, real, real) := (14, -25.12, -28.67);
	var v_seq_5: seq<(int, real, real)> := [v_int_real_real_1, v_int_real_real_2, v_int_real_real_3, v_int_real_real_4];
	var v_int_15: int := 7;
	var v_seq_40: seq<(int, real, real)> := v_seq_5;
	var v_int_79: int := v_int_15;
	var v_int_80: int := safe_index_seq(v_seq_40, v_int_79);
	v_int_15 := v_int_80;
	var v_int_real_real_5: (int, real, real) := (20, 19.95, 15.84);
	var v_int_real_real_6: (int, real, real) := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_15]) else (v_int_real_real_5));
	var v_bool_5: bool := m_method_2(v_int_real_real_6);
	if (if ((v_char_4 in v_map_3)) then (v_map_3[v_char_4]) else (v_bool_5)) {
		var v_seq_6: seq<bool> := [true];
		var v_int_18: int := 8;
		var v_seq_41: seq<bool> := v_seq_6;
		var v_int_81: int := v_int_18;
		var v_int_82: int := safe_index_seq(v_seq_41, v_int_81);
		v_int_18 := v_int_82;
		var v_seq_7: seq<seq<int>> := [[7, 11, 15], []];
		var v_int_19: int := 29;
		var v_seq_42: seq<seq<int>> := v_seq_7;
		var v_int_83: int := v_int_19;
		var v_int_84: int := safe_index_seq(v_seq_42, v_int_83);
		v_int_19 := v_int_84;
		var v_seq_8: seq<int> := (if ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_18]) else (false))) then ((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_19]) else ([]))) else ((match 22 {
			case _ => [1]
		})));
		var v_char_5: char := 'N';
		var v_bool_6: bool := false;
		var v_char_6: char := 'y';
		var v_map_4: map<bool, int> := m_method_4(v_char_5, v_bool_6, v_char_6);
		var v_map_5: map<bool, int> := v_map_4;
		var v_bool_7: bool := v_bool_5;
		var v_int_20: int := (if ((v_bool_7 in v_map_5)) then (v_map_5[v_bool_7]) else ((if (true) then (19) else (12))));
		var v_seq_43: seq<int> := v_seq_8;
		var v_int_85: int := v_int_20;
		var v_int_86: int := safe_index_seq(v_seq_43, v_int_85);
		v_int_20 := v_int_86;
		var v_int_16: int := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_20]) else (v_int_real_real_3.0));
		var v_int_17: int := v_int_19;
		while (v_int_16 < v_int_17) 
			decreases v_int_17 - v_int_16;
			invariant (v_int_16 <= v_int_17);
		{
			v_int_16 := (v_int_16 + 1);
			return ;
		}
		var v_int_real_real_12: (int, real, real) := (9, 11.13, 3.79);
		var v_int_real_real_13: (int, real, real) := (20, 19.95, 15.84);
		var v_int_real_real_14: (int, real, real) := (14, -25.12, -28.67);
		var v_int_real_real_15: (int, real, real) := (13, 8.75, 15.28);
		var v_int_real_real_16: (int, real, real) := (7, 22.20, 19.13);
		var v_int_real_real_17: (int, real, real) := (9, 11.13, 3.79);
		var v_int_real_real_18: (int, real, real) := (9, 11.13, 3.79);
		var v_int_real_real_19: (int, real, real) := (7, 22.20, 19.13);
		var v_int_real_real_20: (int, real, real) := (13, 8.75, 15.28);
		var v_int_real_real_21: (int, real, real) := (14, -25.12, -28.67);
		print "v_map_5", " ", (v_map_5 == map[false := 2, true := 12]), " ", "v_map_4", " ", (v_map_4 == map[false := 2, true := 12]), " ", "v_char_5", " ", (v_char_5 == 'N'), " ", "v_char_6", " ", (v_char_6 == 'y'), " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_bool_7", " ", v_bool_7, " ", "v_bool_6", " ", v_bool_6, " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_20", " ", v_int_20, " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == 15.28), " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -25.12), " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == -28.67), " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == 19.95), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == 3.79), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 22.20), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_12), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == 19.13), " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == 8.75), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_13), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_14), " ", "v_bool_5", " ", v_bool_5, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == 11.13), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_15), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_16), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_17), " ", "v_char_4", " ", (v_char_4 == 'R'), " ", "v_int_7", " ", v_int_7, " ", "v_map_3", " ", (v_map_3 == map['B' := false, 'f' := false, 'y' := false, 'Z' := true]), " ", "v_seq_5", " ", (v_seq_5 == [v_int_real_real_18, v_int_real_real_19, v_int_real_real_20, v_int_real_real_21]), " ", "v_seq_3", " ", (v_seq_3 == [map['B' := false, 'f' := false, 'y' := false, 'Z' := true], map['E' := false, 'G' := true, 'H' := false]]), " ", "v_int_15", " ", v_int_15, " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == 15.84), "\n";
	}
	var v_int_21: int := v_int_7;
	var v_int_22: int := v_int_7;
	while (v_int_21 < v_int_22) 
		decreases v_int_22 - v_int_21;
		invariant (v_int_21 <= v_int_22) && ((((v_int_21 == 0)) ==> ((((v_int_15 == 0)) && ((v_bool_5 == true))))));
	{
		v_int_21 := (v_int_21 + 1);
		var v_map_8: map<bool, bool> := (if (v_bool_5) then ((if (true) then (map[true := true, true := true, false := false, true := true, true := true]) else (map[true := false]))) else (map[true := true, false := true][true := true]));
		var v_DT_2_3_1: DT_2<real, real> := DT_2_3(-18.90);
		var v_DT_2_3_2: DT_2<real, real> := v_DT_2_3_1;
		var v_seq_9: seq<DT_1<int>> := m_method_5(v_DT_2_3_2);
		var v_seq_10: seq<DT_1<int>> := v_seq_9;
		var v_int_28: int := 16;
		var v_int_29: int := 15;
		var v_int_30: int := safe_modulus(v_int_28, v_int_29);
		var v_int_31: int := v_int_30;
		var v_DT_1_3_9: DT_1<int> := DT_1_3;
		var v_DT_1_3_10: DT_1<int> := DT_1_3;
		var v_seq_11: seq<DT_1<int>> := [v_DT_1_3_9, v_DT_1_3_10];
		var v_int_32: int := 25;
		var v_DT_1_3_11: DT_1<int> := DT_1_3;
		var v_DT_1_3_16: DT_1<int> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_31]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_32]) else (v_DT_1_3_11))));
		var v_bool_8: bool := v_bool_5;
		var v_DT_2_1_5: DT_2<int, real> := m_method_6(v_bool_8);
		var v_DT_2_1_6: DT_2<int, real> := v_DT_2_1_5;
		var v_DT_2_4_1: DT_2<real, bool> := DT_2_4(-14.50, true, false);
		var v_DT_2_4_2: DT_2<real, bool> := DT_2_4(20.55, true, true);
		var v_DT_2_4_3: DT_2<real, bool> := DT_2_4(-20.93, true, true);
		var v_DT_2_4_4: DT_2<real, bool> := (match 21.09 {
			case _ => v_DT_2_4_3
		});
		var v_int_38: int := 20;
		var v_seq_15: seq<int> := m_method_9(v_int_38);
		var v_seq_17: seq<int> := v_seq_15;
		var v_bool_int_int_1: (bool, int, int) := (false, 4, 11);
		var v_bool_int_int_2: (bool, int, int) := (true, 18, 1);
		var v_seq_16: seq<(bool, int, int)> := [v_bool_int_int_1, v_bool_int_int_2];
		var v_int_39: int := 8;
		var v_bool_int_int_3: (bool, int, int) := (true, 10, 26);
		var v_bool_int_int_4: (bool, int, int) := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_39]) else (v_bool_int_int_3));
		var v_int_40: int := v_bool_int_int_3.2;
		var v_array_6: array<real> := m_method_7(v_DT_2_4_4, v_seq_17, v_bool_int_int_4, v_int_40);
		var v_array_7: array<real> := v_array_6;
		var v_bool_12: bool := m_method_3(v_map_8, v_DT_1_3_16, v_DT_2_1_6, v_array_7);
		var v_map_10: map<real, bool> := (match true {
			case _ => map[9.49 := false]
		});
		var v_DT_2_3_3: DT_2<real, real> := DT_2_3(7.60);
		var v_DT_2_3_4: DT_2<real, real> := v_DT_2_3_3;
		var v_bool_14: bool := false;
		var v_real_1: real := m_method_10(v_DT_2_3_4, v_bool_14);
		var v_real_2: real := v_real_1;
		var v_map_9: map<bool, bool> := map[true := true, true := false, true := true, true := true];
		var v_DT_1_3_17: DT_1<int> := DT_1_3;
		var v_DT_1_3_18: DT_1<int> := v_DT_1_3_17;
		var v_DT_2_1_7: DT_2<int, real> := DT_2_1;
		var v_DT_2_1_8: DT_2<int, real> := v_DT_2_1_7;
		var v_array_8: array<real> := new real[4] [26.21, -0.08, 0.04, -6.43];
		var v_array_9: array<real> := v_array_8;
		var v_bool_15: bool := m_method_3(v_map_9, v_DT_1_3_18, v_DT_2_1_8, v_array_9);
		var v_map_11: map<real, bool> := (match false {
			case _ => map[-7.98 := false, -16.42 := true, -6.05 := true, -16.26 := false]
		});
		var v_seq_18: seq<real> := [-23.56, -8.41];
		var v_int_45: int := 6;
		var v_real_3: real := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_45]) else (-2.35));
		var v_int_real_real_7: (int, real, real) := (24, -24.19, 20.34);
		var v_int_real_real_8: (int, real, real) := v_int_real_real_7;
		var v_bool_16: bool := m_method_2(v_int_real_real_8);
		v_bool_5, v_bool_16, v_int_30, v_int_15 := v_bool_12, (if ((if ((v_real_2 in v_map_10)) then (v_map_10[v_real_2]) else (v_bool_15))) then ((v_bool_8 <== (if (true) then (false) else (true)))) else ((if ((v_real_3 in v_map_11)) then (v_map_11[v_real_3]) else (v_bool_16)))), v_int_21, v_bool_int_int_1.1;
		var v_seq_19: seq<set<set<real>>> := [{{}, {}, {7.54, -29.27, -13.35, 5.93}}, {{}, {27.24, 0.66}}, {}];
		var v_int_46: int := 6;
		var v_seq_20: seq<seq<set<set<real>>>> := [];
		var v_int_47: int := 28;
		var v_seq_21: seq<set<set<real>>> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_47]) else ([{{23.58, -24.84}, {-19.23, 20.54, -5.90}, {22.51, -3.08}}, {{}, {21.78}, {}}, {}, {{26.07, -18.45, -26.87}}]));
		var v_int_48: int := (14 - -29);
		var v_seq_22: seq<set<bool>> := [{true}];
		var v_int_49: int := 5;
		var v_seq_23: seq<set<bool>> := [{true, false}, {true, false}, {true, false, true}, {true}];
		var v_seq_24: seq<set<bool>> := (if ((|v_seq_23| > 0)) then (v_seq_23[23..22]) else (v_seq_23));
		var v_int_50: int := (19 * 15);
		var v_seq_25: seq<set<bool>> := [];
		var v_int_51: int := 10;
		var v_seq_26: seq<multiset<int>> := [multiset{}, multiset{14, 7, 2, 20}];
		var v_int_52: int := 5;
		var v_bool_20: bool := false;
		var v_char_10: char := 'y';
		var v_seq_27: seq<DT_3> := m_method_11(v_bool_20, v_char_10);
		var v_seq_28: seq<DT_3> := v_seq_27;
		var v_int_56: int := v_int_48;
		var v_DT_3_1_5: DT_3 := DT_3_1;
		var v_map_12: map<bool, DT_3> := map[false := v_DT_3_1_5];
		var v_bool_21: bool := false;
		var v_DT_3_1_6: DT_3 := DT_3_1;
		var v_set_2: set<set<real>>, v_set_3: set<bool>, v_multiset_2: multiset<int>, v_DT_3_1_7: DT_3 := (((map[{-12.20} := multiset{multiset{-11.63, 9.99, -25.97}, multiset{16.88}, multiset{1.17, 23.73, 17.52, -15.69}, multiset({})}, {} := multiset{multiset{}}, {} := multiset{multiset{}, multiset{-7.48, -11.32}, multiset({-12.40, -13.67})}]).Keys - (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_46]) else ({{14.08, 4.31, -25.25}}))) * (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_48]) else ((map[{10, 25, 3} := {20.94, 4.48, 16.24, 17.26}, {26} := {9.03, 13.99, 0.20}]).Values))), (((if ((|v_seq_22| > 0)) then (v_seq_22[v_int_49]) else ({false, false, true, true})) + ({true, true} * {false, false})) + (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_50]) else ((if ((|v_seq_25| > 0)) then (v_seq_25[v_int_51]) else ({true, true}))))), ((if ((match false {
			case _ => false
		})) then ((if (true) then (multiset{23, 0, 3, 18}) else (multiset{18, 4}))) else ((if ((|v_seq_26| > 0)) then (v_seq_26[v_int_52]) else (multiset{15, 23, 15})))) * ((match 5 {
			case _ => multiset{8, 13}
		}) + (multiset{14} * multiset({12, 20})))), (if (v_bool_14) then ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_56]) else ((if ((v_bool_21 in v_map_12)) then (v_map_12[v_bool_21]) else (v_DT_3_1_6))))) else (v_DT_3_1_6));
		var v_map_13: map<bool, bool> := map[false := true, true := true, true := true];
		var v_bool_22: bool := false;
		var v_int_real_real_9: (int, real, real) := (18, -4.15, 16.49);
		var v_int_real_real_10: (int, real, real) := v_int_real_real_9;
		var v_bool_23: bool := m_method_2(v_int_real_real_10);
		if (((if ((v_bool_22 in v_map_13)) then (v_map_13[v_bool_22]) else (true)) == v_bool_23) == v_bool_14) {
			var v_array_10: array<bool> := new bool[3] [false, true, false];
			var v_map_16: map<bool, int> := (map[false := 12, false := 28, true := -3, false := 3] - {false, false, false, false})[(true <==> false) := v_array_10.Length];
			var v_bool_26: bool := ((if (false) then (false) else (true)) in (map[false := false, false := false, true := true, true := false] + map[true := false]));
			var v_map_14: map<bool, map<bool, int>> := map[true := map[true := 5, false := 17, false := 18, false := 23], true := map[false := 22, false := 24, false := 28]];
			var v_bool_24: bool := true;
			var v_map_15: map<bool, int> := (if ((v_bool_24 in v_map_14)) then (v_map_14[v_bool_24]) else (map[true := 29, true := 3, false := 1, true := 1, false := 25]));
			var v_bool_25: bool := v_bool_14;
			var v_map_17: map<bool, int> := map[false := 26, false := 29, true := 18, true := 27, true := -14];
			var v_bool_27: bool := false;
			var v_map_18: map<bool, int> := (map[true := 27] + map[true := 24, false := 16, true := 12, false := 23, true := 17])[v_bool_15 := (if ((v_bool_27 in v_map_17)) then (v_map_17[v_bool_27]) else (5))];
			var v_bool_28: bool := (match 18 {
				case _ => (if (true) then (true) else (false))
			});
			var v_int_62: int, v_int_63: int := (if ((v_bool_26 in v_map_16)) then (v_map_16[v_bool_26]) else ((if ((v_bool_25 in v_map_15)) then (v_map_15[v_bool_25]) else ((26 - 6))))), (if ((v_bool_28 in v_map_18)) then (v_map_18[v_bool_28]) else (v_int_51));
			for v_int_57 := v_int_62 to v_int_63 
				invariant (v_int_63 - v_int_57 >= 0)
			{
				var v_map_19: map<int, int> := map[15 := 3, 12 := 29];
				var v_int_58: int := -23;
				var v_map_21: map<int, bool> := map[23 := false, 12 := true, 27 := false, 7 := true, 4 := true][26 := true][(if ((v_int_58 in v_map_19)) then (v_map_19[v_int_58]) else (8)) := (match 6 {
					case _ => false
				})];
				var v_seq_29: seq<int> := [];
				var v_seq_30: seq<int> := (if ((|v_seq_29| > 0)) then (v_seq_29[15..17]) else (v_seq_29));
				var v_map_20: map<int, int> := map[27 := 3, 11 := 8];
				var v_int_59: int := 9;
				var v_int_60: int := (if ((v_int_59 in v_map_20)) then (v_map_20[v_int_59]) else (23));
				var v_int_61: int := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_60]) else (v_int_48));
				if (if ((v_int_61 in v_map_21)) then (v_map_21[v_int_61]) else (((match 7 {
					case _ => 'W'
				}) <= (match 6 {
					case _ => 'u'
				})))) {
					return ;
				} else {
					return ;
				}
			}
			var v_seq_31: seq<int> := [9, 24];
			var v_seq_32: seq<int> := (if ((|v_seq_31| > 0)) then (v_seq_31[9..10]) else (v_seq_31));
			var v_seq_33: seq<int> := (if ((|v_seq_32| > 0)) then (v_seq_32[v_bool_int_int_2.1..0]) else (v_seq_32));
			var v_int_65: int := ((5 % 16) / v_bool_int_int_2.1);
			var v_array_11: array<int> := new int[4] [17, 9, -2, 22];
			var v_array_12: array<int> := new int[3] [24, -6, 19];
			var v_array_13: array<int> := new int[4];
			v_array_13[0] := 18;
			v_array_13[1] := 15;
			v_array_13[2] := 4;
			v_array_13[3] := 29;
			var v_array_14: array<int> := new int[5] [-21, 14, 7, 4, 19];
			var v_array_15: array<int> := new int[3] [22, -17, 11];
			var v_array_16: array<int> := new int[5] [-2, -2, 5, 20, 26];
			var v_array_17: array<int> := new int[3] [-8, 0, 9];
			var v_array_18: array<int> := new int[3] [1, 7, 15];
			var v_map_22: map<multiset<array<int>>, int> := map[multiset{v_array_11, v_array_12, v_array_13, v_array_14} := 13, multiset([]) := 8][multiset([v_array_15, v_array_16, v_array_17, v_array_18]) := 27];
			var v_array_19: array<int> := new int[5] [10, -25, 8, -5, 8];
			var v_array_20: array<int> := new int[3] [-18, 0, 25];
			var v_array_21: array<int> := new int[3] [9, 12, 23];
			var v_array_22: array<int> := new int[3] [5, 16, 29];
			var v_array_23: array<int> := new int[5] [5, 10, 9, 19, 27];
			var v_array_24: array<int> := new int[3] [18, 29, 5];
			var v_array_25: array<int> := new int[3] [-12, -7, 6];
			var v_array_26: array<int> := new int[4] [27, 16, 7, 0];
			var v_multiset_3: multiset<array<int>> := (multiset([v_array_19, v_array_20, v_array_21, v_array_22]) + multiset([v_array_23, v_array_24, v_array_25, v_array_26]));
			var v_map_23: map<real, bool> := map[20.82 := true];
			var v_real_4: real := -29.75;
			var v_map_24: map<real, map<real, real>> := map[19.01 := map[-3.26 := 0.18], 20.62 := map[10.97 := -20.47], -19.87 := map[21.68 := -18.97]];
			var v_real_5: real := -19.53;
			var v_int_75: int, v_int_76: int := (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_65]) else ((if ((v_multiset_3 in v_map_22)) then (v_map_22[v_multiset_3]) else (v_array_24[1])))), |(if ((if ((v_real_4 in v_map_23)) then (v_map_23[v_real_4]) else (false))) then ((map[-6.63 := 1.21, 12.39 := -5.67] - {-24.55, 23.78, 12.99})) else ((if ((v_real_5 in v_map_24)) then (v_map_24[v_real_5]) else (map[-12.60 := 7.74, 1.66 := 9.26, -1.61 := -24.77, -17.33 := -23.48]))))|;
			for v_int_64 := v_int_75 to v_int_76 
				invariant (v_int_76 - v_int_64 >= 0)
			{
				var v_array_27: array<real> := new real[3] [10.65, 8.21, -1.87];
				var v_seq_34: seq<int> := [20, 23];
				var v_int_67: int := 17;
				var v_map_25: map<real, int> := map[4.56 := 8, -29.22 := 0, -3.49 := 28][-7.82 := 4][(match -5.20 {
					case _ => -14.21
				}) := v_array_25[2]];
				var v_real_6: real := v_DT_2_3_1.DT_2_3_1;
				var v_seq_35: seq<int> := [26, 27, 12];
				var v_seq_36: seq<int> := v_seq_35;
				var v_int_68: int := 1;
				var v_int_69: int := safe_index_seq(v_seq_36, v_int_68);
				var v_int_70: int := v_int_69;
				var v_seq_38: seq<int> := (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_70 := 26]) else (v_seq_35));
				var v_seq_37: seq<int> := [15, 1, 20];
				var v_int_71: int := 5;
				var v_int_72: int := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_71]) else (26));
				var v_int_73: int, v_int_74: int := ((v_array_27.Length - v_int_52) + ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_67]) else (4)) * v_array_22[0])), (if ((v_real_6 in v_map_25)) then (v_map_25[v_real_6]) else ((if ((|v_seq_38| > 0)) then (v_seq_38[v_int_72]) else ((match 'V' {
					case _ => 1
				})))));
				for v_int_66 := v_int_73 to v_int_74 
					invariant (v_int_74 - v_int_66 >= 0)
				{
					return ;
				}
			}
			var v_map_27: map<real, bool> := v_map_10;
			var v_real_8: real := v_int_real_real_2.2;
			var v_map_26: map<real, bool> := map[23.93 := false, 1.29 := false, 25.87 := false, -2.19 := false];
			var v_real_7: real := 12.39;
			if (if ((v_real_8 in v_map_27)) then (v_map_27[v_real_8]) else ((if ((if (false) then (true) else (true))) then ((if ((v_real_7 in v_map_26)) then (v_map_26[v_real_7]) else (false))) else ((5 != -23))))) {
				return ;
			}
			break;
		}
		return ;
	}
	var v_int_real_real_22: (int, real, real) := (9, 11.13, 3.79);
	var v_int_real_real_23: (int, real, real) := (20, 19.95, 15.84);
	var v_int_real_real_24: (int, real, real) := (14, -25.12, -28.67);
	var v_int_real_real_25: (int, real, real) := (13, 8.75, 15.28);
	var v_int_real_real_26: (int, real, real) := (7, 22.20, 19.13);
	var v_int_real_real_27: (int, real, real) := (9, 11.13, 3.79);
	var v_int_real_real_28: (int, real, real) := (9, 11.13, 3.79);
	var v_int_real_real_29: (int, real, real) := (7, 22.20, 19.13);
	var v_int_real_real_30: (int, real, real) := (13, 8.75, 15.28);
	var v_int_real_real_31: (int, real, real) := (14, -25.12, -28.67);
	print "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == 15.28), " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -25.12), " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == -28.67), " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == 19.95), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == 3.79), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 22.20), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_22), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == 19.13), " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == 8.75), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_23), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_24), " ", "v_bool_5", " ", v_bool_5, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == 11.13), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_25), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_26), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_27), " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_char_4", " ", (v_char_4 == 'R'), " ", "v_int_7", " ", v_int_7, " ", "v_map_3", " ", (v_map_3 == map['B' := false, 'f' := false, 'y' := false, 'Z' := true]), " ", "v_seq_5", " ", (v_seq_5 == [v_int_real_real_28, v_int_real_real_29, v_int_real_real_30, v_int_real_real_31]), " ", "v_seq_3", " ", (v_seq_3 == [map['B' := false, 'f' := false, 'y' := false, 'Z' := true], map['E' := false, 'G' := true, 'H' := false]]), " ", "v_int_15", " ", v_int_15, " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == 15.84), "\n";
	return ;
}
