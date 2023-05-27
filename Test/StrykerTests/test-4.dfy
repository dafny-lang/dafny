// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2 | DT_1_4
datatype DT_2 = DT_2_1
datatype DT_3<T_3, T_4> = DT_3_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: (int, real, int), p_m_method_7_2: bool) returns (ret_1: (bool, int))
{
	var v_bool_int_9: (bool, int) := (true, -27);
	return v_bool_int_9;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: map<bool, int>) returns (ret_1: int)
	requires ((p_m_method_6_1 == map[true := 29])) || ((p_m_method_6_1 == map[false := 21]));
	ensures (((p_m_method_6_1 == map[false := 21])) ==> ((ret_1 == 0))) && (((p_m_method_6_1 == map[true := 29])) ==> ((ret_1 == 0)));
{
	var v_char_8: char := 'R';
	var v_real_5: real := 2.94;
	var v_bool_12: bool := m_method_1(v_char_8, v_real_5);
	var v_seq_14: seq<bool> := [true, true];
	var v_int_31: int := 14;
	var v_seq_82: seq<bool> := v_seq_14;
	var v_int_136: int := v_int_31;
	var v_int_137: int := safe_index_seq(v_seq_82, v_int_136);
	v_int_31 := v_int_137;
	if (v_bool_12 || (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_31]) else (false))) {
		assert ((p_m_method_6_1 == map[false := 21]) && (v_char_8 == 'R')) || ((p_m_method_6_1 == map[true := 29]) && (v_char_8 == 'R'));
		expect ((p_m_method_6_1 == map[false := 21]) && (v_char_8 == 'R')) || ((p_m_method_6_1 == map[true := 29]) && (v_char_8 == 'R'));
		assert ((v_seq_14 == [true, true]) && (v_bool_12 == true) && (p_m_method_6_1 == map[false := 21])) || ((v_seq_14 == [true, true]) && (v_bool_12 == true) && (p_m_method_6_1 == map[true := 29]));
		expect ((v_seq_14 == [true, true]) && (v_bool_12 == true) && (p_m_method_6_1 == map[false := 21])) || ((v_seq_14 == [true, true]) && (v_bool_12 == true) && (p_m_method_6_1 == map[true := 29]));
		print "v_seq_14", " ", v_seq_14, " ", "v_char_8", " ", (v_char_8 == 'R'), " ", "v_bool_12", " ", v_bool_12, " ", "v_int_31", " ", v_int_31, " ", "v_real_5", " ", (v_real_5 == 2.94), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == map[false := 21]), "\n";
	} else {
		if v_bool_12 {
			if v_bool_12 {
				var v_seq_15: seq<int> := ([9, 2, 29] + [22, 12, 20]);
				var v_int_32: int := (if (false) then (2) else (4));
				var v_seq_16: seq<((int, bool, bool), (bool, bool, int), (int, bool, int))> := [];
				var v_int_33: int := 19;
				var v_int_34: int := safe_index_seq(v_seq_16, v_int_33);
				return (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_32]) else (v_int_34));
			}
			assert true;
			expect true;
			var v_int_36: int, v_int_37: int := v_int_31, v_int_31;
			for v_int_35 := v_int_36 to v_int_37 
				invariant (v_int_37 - v_int_35 >= 0)
			{
				var v_bool_int_5: (bool, int) := (true, 12);
				var v_bool_int_6: (bool, int) := (false, 15);
				var v_bool_int_7: (bool, int) := (true, 15);
				var v_bool_int_8: (bool, int) := (true, 26);
				var v_map_4: map<(bool, int), int> := map[v_bool_int_5 := 25, v_bool_int_6 := 18, v_bool_int_7 := 7][v_bool_int_8 := 22];
				var v_int_real_int_1: (int, real, int) := (23, 24.48, 8);
				var v_int_real_int_2: (int, real, int) := v_int_real_int_1;
				var v_bool_13: bool := false;
				var v_bool_int_10: (bool, int) := m_method_7(v_int_real_int_2, v_bool_13);
				var v_bool_int_11: (bool, int) := v_bool_int_10;
				return (if ((v_bool_int_11 in v_map_4)) then (v_map_4[v_bool_int_11]) else ((16 % 18)));
			}
			var v_real_real_1: (real, real) := (13.05, 2.11);
			var v_int_real_2: (int, real) := (29, -26.23);
			var v_real_real_int_real_1: ((real, real), (int, real)) := (v_real_real_1, v_int_real_2);
			var v_real_real_2: (real, real) := (28.84, 6.72);
			var v_int_real_3: (int, real) := (0, 2.12);
			var v_real_real_int_real_2: ((real, real), (int, real)) := (v_real_real_2, v_int_real_3);
			var v_map_6: map<((real, real), (int, real)), int> := map[v_real_real_int_real_1 := -18][v_real_real_int_real_2 := 11];
			var v_real_real_real_1: (real, real, real) := (-22.84, 25.09, 1.00);
			var v_bool_bool_1: (bool, bool) := (false, true);
			var v_real_real_real_char_bool_bool_1: ((real, real, real), char, (bool, bool)) := (v_real_real_real_1, 'm', v_bool_bool_1);
			var v_real_real_3: (real, real) := (-7.72, 24.73);
			var v_int_real_4: (int, real) := (23, 28.72);
			var v_real_real_int_real_3: ((real, real), (int, real)) := (v_real_real_3, v_int_real_4);
			var v_map_5: map<((real, real, real), char, (bool, bool)), ((real, real), (int, real))> := map[v_real_real_real_char_bool_bool_1 := v_real_real_int_real_3];
			var v_real_real_real_2: (real, real, real) := (4.88, 1.59, -24.38);
			var v_bool_bool_2: (bool, bool) := (true, false);
			var v_real_real_real_char_bool_bool_2: ((real, real, real), char, (bool, bool)) := (v_real_real_real_2, 'z', v_bool_bool_2);
			var v_real_real_real_char_bool_bool_3: ((real, real, real), char, (bool, bool)) := v_real_real_real_char_bool_bool_2;
			var v_real_real_4: (real, real) := (26.65, -29.72);
			var v_int_real_5: (int, real) := (5, -3.64);
			var v_real_real_int_real_4: ((real, real), (int, real)) := (v_real_real_4, v_int_real_5);
			var v_real_real_int_real_5: ((real, real), (int, real)) := (if ((v_real_real_real_char_bool_bool_3 in v_map_5)) then (v_map_5[v_real_real_real_char_bool_bool_3]) else (v_real_real_int_real_4));
			var v_int_38: int := (if ((v_real_real_int_real_5 in v_map_6)) then (v_map_6[v_real_real_int_real_5]) else ((-5 / 22)));
			var v_int_40: int := 11;
			var v_int_41: int := -24;
			var v_int_42: int := safe_division(v_int_40, v_int_41);
			var v_int_39: int := ((16 / 23) % v_int_42);
			while (v_int_38 < v_int_39) 
				decreases v_int_39 - v_int_38;
				invariant (v_int_38 <= v_int_39);
			{
				v_int_38 := (v_int_38 + 1);
				return v_int_39;
			}
			var v_seq_17: seq<char> := (['n', 'V', 'K', 'h'] + ['B']);
			var v_int_43: int := v_int_42;
			var v_char_9: char, v_char_10: char, v_char_11: char := v_real_real_real_char_bool_bool_1.1, v_real_real_real_char_bool_bool_2.1, (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_43]) else ((if (true) then ('N') else ('z'))));
			if (v_int_41 > (match 'd' {
				case _ => 20
			})) {
				var v_seq_18: seq<seq<int>> := [[]];
				var v_int_44: int := 1;
				var v_seq_19: seq<int> := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_44]) else ([29, 17, 28]));
				var v_int_45: int := v_int_42;
				var v_map_7: map<char, int> := map['P' := 15, 'E' := 3, 'S' := 1];
				var v_char_12: char := 'b';
				return (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_45]) else ((if ((v_char_12 in v_map_7)) then (v_map_7[v_char_12]) else (-8))));
			}
			assert true;
			expect true;
			var v_seq_20: seq<map<char, char>> := [];
			var v_int_46: int := 6;
			var v_map_8: map<char, char> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_46]) else (map['N' := 'j', 'r' := 'N', 'a' := 'P', 'f' := 'a']));
			var v_char_13: char := v_real_real_real_char_bool_bool_1.1;
			v_char_8, v_char_13, v_char_10 := v_real_real_real_char_bool_bool_1.1, (if ((v_char_13 in v_map_8)) then (v_map_8[v_char_13]) else (v_char_8)), v_real_real_real_char_bool_bool_2.1;
			var v_seq_21: seq<int> := ([13, 13, 9] + [15, 10, 20, -5]);
			var v_int_47: int := (if (true) then (19) else (28));
			return (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_47]) else (v_int_43));
		}
	}
	print "v_seq_14", " ", v_seq_14, " ", "v_char_8", " ", (v_char_8 == 'R'), " ", "v_bool_12", " ", v_bool_12, " ", "v_int_31", " ", v_int_31, " ", "v_real_5", " ", (v_real_5 == 2.94), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == map[false := 21]), "\n";
	return v_int_31;
}

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: bool) returns (ret_1: real)
	requires ((p_m_method_5_1 == 'A') && (p_m_method_5_2 == false));
	ensures (((p_m_method_5_1 == 'A') && (p_m_method_5_2 == false)) ==> ((28.74 < ret_1 < 28.94)));
{
	print "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'A'), "\n";
	return 28.84;
}

method m_method_4(p_m_method_4_1: (bool, real, int), p_m_method_4_2: char, p_m_method_4_3: map<bool, int>) returns (ret_1: seq<bool>)
	requires ((p_m_method_4_2 == 'I') && ((p_m_method_4_1).0 == true) && (-15.27 < (p_m_method_4_1).1 < -15.07) && ((p_m_method_4_1).2 == 2) && (p_m_method_4_3 == map[true := 21]));
	ensures (((p_m_method_4_2 == 'I') && ((p_m_method_4_1).0 == true) && (-15.27 < (p_m_method_4_1).1 < -15.07) && ((p_m_method_4_1).2 == 2) && (p_m_method_4_3 == map[true := 21])) ==> (|ret_1| == 1 && (ret_1[0] == true)));
{
	var v_bool_real_int_3: (bool, real, int) := (true, -15.17, 2);
	print "p_m_method_4_1.1", " ", (p_m_method_4_1.1 == -15.17), " ", "p_m_method_4_1.2", " ", p_m_method_4_1.2, " ", "p_m_method_4_1", " ", (p_m_method_4_1 == v_bool_real_int_3), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == map[true := 21]), " ", "p_m_method_4_1.0", " ", p_m_method_4_1.0, " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'I'), "\n";
	return [true];
}

method m_method_3(p_m_method_3_1: (real, int, real)) returns (ret_1: char)
	requires ((5.34 < (p_m_method_3_1).0 < 5.54) && ((p_m_method_3_1).1 == 20) && (-27.63 < (p_m_method_3_1).2 < -27.43));
	ensures (((5.34 < (p_m_method_3_1).0 < 5.54) && ((p_m_method_3_1).1 == 20) && (-27.63 < (p_m_method_3_1).2 < -27.43)) ==> ((ret_1 == 'a')));
{
	if false {
		var v_int_17: int, v_int_18: int := 17, -17;
		for v_int_16 := v_int_17 to v_int_18 
			invariant (v_int_18 - v_int_16 >= 0)
		{
			return 's';
		}
		var v_DT_1_4_5: DT_1<bool, set<int>> := DT_1_4;
		var v_bool_map_DT_1_4_1: (bool, map<bool, bool>, DT_1<bool, set<int>>) := (false, map[false := true, true := true, true := false], v_DT_1_4_5);
		var v_DT_1_4_6: DT_1<bool, set<int>> := DT_1_4;
		var v_DT_1_4_bool_1: (DT_1<bool, set<int>>, bool) := (v_DT_1_4_6, true);
		v_bool_map_DT_1_4_1, v_DT_1_4_bool_1 := v_bool_map_DT_1_4_1, v_DT_1_4_bool_1;
		var v_int_real_1: (int, real) := (24, -13.71);
		var v_bool_int_real_char_1: (bool, (int, real), char) := (false, v_int_real_1, 'U');
		var v_bool_bool_real_1: (bool, bool, real) := (true, false, 26.20);
		var v_bool_bool_real_int_1: ((bool, bool, real), int) := (v_bool_bool_real_1, 7);
		v_bool_int_real_char_1, v_bool_bool_real_int_1 := v_bool_int_real_char_1, v_bool_bool_real_int_1;
		match false {
			case _ => {
				return 'I';
			}
			
		}
		
	}
	var v_real_int_real_3: (real, int, real) := (5.44, 20, -27.53);
	print "p_m_method_3_1.2", " ", (p_m_method_3_1.2 == -27.53), " ", "p_m_method_3_1.0", " ", (p_m_method_3_1.0 == 5.44), " ", "p_m_method_3_1.1", " ", p_m_method_3_1.1, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == v_real_int_real_3), "\n";
	return 'a';
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

method m_method_2(p_m_method_2_1: bool) returns (ret_1: seq<bool>)
	requires ((p_m_method_2_1 == false));
	ensures (((p_m_method_2_1 == false)) ==> (|ret_1| == 1 && (ret_1[0] == true)));
{
	var v_real_int_real_1: (real, int, real) := (5.44, 20, -27.53);
	var v_real_int_real_2: (real, int, real) := v_real_int_real_1;
	var v_char_2: char := m_method_3(v_real_int_real_2);
	var v_bool_int_1: (bool, int) := (false, 12);
	var v_int_bool_int_1: (int, (bool, int)) := (21, v_bool_int_1);
	var v_bool_int_2: (bool, int) := (true, 17);
	var v_int_bool_int_2: (int, (bool, int)) := (15, v_bool_int_2);
	var v_bool_int_3: (bool, int) := (false, 23);
	var v_int_bool_int_3: (int, (bool, int)) := (8, v_bool_int_3);
	var v_map_1: map<(int, (bool, int)), char> := map[v_int_bool_int_1 := 'p', v_int_bool_int_2 := 'z', v_int_bool_int_3 := 'Q'];
	var v_bool_int_4: (bool, int) := (false, 11);
	var v_int_bool_int_4: (int, (bool, int)) := (-3, v_bool_int_4);
	var v_int_bool_int_5: (int, (bool, int)) := v_int_bool_int_4;
	var v_seq_3: seq<bool> := [false, false];
	var v_int_19: int := 0;
	var v_char_3: char, v_char_4: char, v_bool_7: bool, v_real_2: real := v_char_2, (if ((v_int_bool_int_5 in v_map_1)) then (v_map_1[v_int_bool_int_5]) else ('b')), (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_19]) else (false)), v_real_int_real_1.2;
	var v_bool_real_int_1: (bool, real, int) := (true, -15.17, 2);
	var v_bool_real_int_2: (bool, real, int) := v_bool_real_int_1;
	var v_char_5: char := 'I';
	var v_map_2: map<bool, int> := map[true := 21];
	var v_seq_4: seq<bool> := m_method_4(v_bool_real_int_2, v_char_5, v_map_2);
	var v_real_int_real_4: (real, int, real) := (5.44, 20, -27.53);
	var v_real_int_real_5: (real, int, real) := (5.44, 20, -27.53);
	var v_bool_real_int_4: (bool, real, int) := (true, -15.17, 2);
	var v_bool_real_int_5: (bool, real, int) := (true, -15.17, 2);
	var v_bool_int_12: (bool, int) := (false, 12);
	var v_int_bool_int_6: (int, (bool, int)) := (21, v_bool_int_12);
	var v_bool_int_13: (bool, int) := (true, 17);
	var v_int_bool_int_7: (int, (bool, int)) := (15, v_bool_int_13);
	var v_bool_int_14: (bool, int) := (false, 23);
	var v_int_bool_int_8: (int, (bool, int)) := (8, v_bool_int_14);
	print "v_real_int_real_2", " ", (v_real_int_real_2 == v_real_int_real_4), " ", "v_bool_int_2.1", " ", v_bool_int_2.1, " ", "v_bool_int_3.0", " ", v_bool_int_3.0, " ", "v_real_int_real_1", " ", (v_real_int_real_1 == v_real_int_real_5), " ", "v_bool_int_1.1", " ", v_bool_int_1.1, " ", "v_bool_int_2.0", " ", v_bool_int_2.0, " ", "v_bool_int_4.1", " ", v_bool_int_4.1, " ", "v_bool_int_3.1", " ", v_bool_int_3.1, " ", "v_bool_int_4.0", " ", v_bool_int_4.0, " ", "v_bool_int_1.0", " ", v_bool_int_1.0, " ", "v_int_19", " ", v_int_19, " ", "v_bool_7", " ", v_bool_7, " ", "v_bool_int_1", " ", v_bool_int_1, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_bool_int_3", " ", v_bool_int_3, " ", "v_bool_int_2", " ", v_bool_int_2, " ", "v_bool_real_int_2", " ", (v_bool_real_int_2 == v_bool_real_int_4), " ", "v_bool_real_int_1", " ", (v_bool_real_int_1 == v_bool_real_int_5), " ", "v_bool_int_4", " ", v_bool_int_4, " ", "v_bool_real_int_1.2", " ", v_bool_real_int_1.2, " ", "v_real_int_real_1.2", " ", (v_real_int_real_1.2 == -27.53), " ", "v_int_bool_int_1.0", " ", v_int_bool_int_1.0, " ", "v_char_3", " ", (v_char_3 == 'a'), " ", "v_char_2", " ", (v_char_2 == 'a'), " ", "v_real_int_real_1.0", " ", (v_real_int_real_1.0 == 5.44), " ", "v_char_5", " ", (v_char_5 == 'I'), " ", "v_real_int_real_1.1", " ", v_real_int_real_1.1, " ", "v_char_4", " ", (v_char_4 == 'b'), " ", "v_int_bool_int_5", " ", v_int_bool_int_5, " ", "v_int_bool_int_4", " ", v_int_bool_int_4, " ", "v_int_bool_int_3", " ", v_int_bool_int_3, " ", "v_int_bool_int_2", " ", v_int_bool_int_2, " ", "v_int_bool_int_1", " ", v_int_bool_int_1, " ", "v_int_bool_int_2.1", " ", v_int_bool_int_2.1, " ", "v_int_bool_int_3.0", " ", v_int_bool_int_3.0, " ", "v_map_1", " ", (v_map_1 == map[v_int_bool_int_6 := 'p', v_int_bool_int_7 := 'z', v_int_bool_int_8 := 'Q']), " ", "v_int_bool_int_1.1", " ", v_int_bool_int_1.1, " ", "v_int_bool_int_2.0", " ", v_int_bool_int_2.0, " ", "v_int_bool_int_4.1", " ", v_int_bool_int_4.1, " ", "v_int_bool_int_3.1", " ", v_int_bool_int_3.1, " ", "v_int_bool_int_4.0", " ", v_int_bool_int_4.0, " ", "v_map_2", " ", (v_map_2 == map[true := 21]), " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_real_2", " ", (v_real_2 == -27.53), " ", "v_bool_real_int_1.0", " ", v_bool_real_int_1.0, " ", "v_bool_real_int_1.1", " ", (v_bool_real_int_1.1 == -15.17), "\n";
	return v_seq_4;
}

method m_method_1(p_m_method_1_1: char, p_m_method_1_2: real) returns (ret_1: bool)
	requires ((p_m_method_1_1 == 'T') && (28.74 < p_m_method_1_2 < 28.94)) || ((p_m_method_1_1 == 'x') && (21.17 < p_m_method_1_2 < 21.37)) || ((p_m_method_1_1 == 'R') && (2.84 < p_m_method_1_2 < 3.04));
	ensures (((p_m_method_1_1 == 'T') && (28.74 < p_m_method_1_2 < 28.94)) ==> ((ret_1 == true))) && (((p_m_method_1_1 == 'R') && (2.84 < p_m_method_1_2 < 3.04)) ==> ((ret_1 == true))) && (((p_m_method_1_1 == 'x') && (21.17 < p_m_method_1_2 < 21.37)) ==> ((ret_1 == true)));
{
	var v_bool_1: bool, v_bool_2: bool, v_bool_3: bool, v_bool_4: bool, v_bool_5: bool := false, true, false, true, true;
	if true {
		
	} else {
		var v_int_7: int := 0;
		var v_int_8: int := 4;
		while (v_int_7 < v_int_8) 
			decreases v_int_8 - v_int_7;
			invariant (v_int_7 <= v_int_8);
		{
			v_int_7 := (v_int_7 + 1);
			var v_int_10: int, v_int_11: int := -25, 16;
			for v_int_9 := v_int_10 to v_int_11 
				invariant (v_int_11 - v_int_9 >= 0)
			{
				return false;
			}
			return true;
		}
		if true {
			var v_int_12: int := 24;
			var v_int_13: int := 7;
			while (v_int_12 < v_int_13) 
				decreases v_int_13 - v_int_12;
				invariant (v_int_12 <= v_int_13);
			{
				v_int_12 := (v_int_12 + 1);
				return true;
			}
			var v_int_14: int := -6;
			var v_int_15: int := 6;
			while (v_int_14 < v_int_15) 
				decreases v_int_15 - v_int_14;
				invariant (v_int_14 <= v_int_15);
			{
				v_int_14 := (v_int_14 + 1);
			}
			assert true;
			expect true;
			return true;
		}
		var v_DT_1_2_1: DT_1<DT_1<int, real>, set<real>> := DT_1_2;
		v_DT_1_2_1 := v_DT_1_2_1;
		assert true;
		expect true;
		return false;
	}
	print "v_bool_1", " ", v_bool_1, " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 21.27), " ", "v_bool_3", " ", v_bool_3, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'x'), " ", "v_bool_2", " ", v_bool_2, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, "\n";
	return true;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	if false {
		
	}
	var v_real_int_1: (real, int) := (9.84, 5);
	var v_real_int_2: (real, int) := (-11.44, 26);
	var v_real_int_3: (real, int) := (14.23, 21);
	var v_real_int_4: (real, int) := (-23.50, -18);
	var v_real_int_5: (real, int) := (27.95, 0);
	var v_real_int_6: (real, int) := (-25.35, 13);
	var v_real_int_7: (real, int) := (16.85, 29);
	var v_real_int_8: (real, int) := (0.73, 28);
	var v_real_int_9: (real, int) := (1.51, 6);
	var v_real_int_10: (real, int) := (16.15, 12);
	var v_real_int_11: (real, int) := (28.08, 8);
	var v_real_int_12: (real, int) := (26.37, 5);
	var v_real_int_13: (real, int) := (21.47, 17);
	var v_real_int_14: (real, int) := (7.23, 4);
	var v_real_int_15: (real, int) := (-0.88, 14);
	var v_real_int_16: (real, int) := (1.53, 11);
	var v_real_int_17: (real, int) := (24.90, -2);
	var v_real_int_18: (real, int) := (-15.25, 6);
	var v_real_int_19: (real, int) := (-26.49, 6);
	var v_real_int_20: (real, int) := (25.59, 24);
	var v_real_int_21: (real, int) := (-27.55, 28);
	var v_real_int_22: (real, int) := (-10.97, 11);
	var v_real_int_23: (real, int) := (29.38, 19);
	var v_real_int_24: (real, int) := (3.78, 0);
	var v_real_int_25: (real, int) := (14.24, -16);
	var v_real_int_26: (real, int) := (-26.15, 24);
	var v_real_int_27: (real, int) := (11.81, 0);
	var v_DT_1_4_1: DT_1<bool, set<int>> := DT_1_4;
	var v_DT_1_4_2: DT_1<bool, set<int>> := DT_1_4;
	var v_DT_1_4_3: DT_1<bool, set<int>> := DT_1_4;
	var v_DT_1_4_4: DT_1<bool, set<int>> := DT_1_4;
	var v_char_1: char := 'x';
	var v_real_1: real := 21.27;
	var v_bool_6: bool := m_method_1(v_char_1, v_real_1);
	var v_int_int_real_1: (int, int, real) := (1, 4, -5.27);
	var v_map_int_int_real_1: (map<bool, int>, (int, int, real)) := (map[false := 23, true := 5], v_int_int_real_1);
	var v_int_int_real_2: (int, int, real) := (-17, 17, -4.64);
	var v_map_int_int_real_2: (map<bool, int>, (int, int, real)) := (map[true := 18, false := 22], v_int_int_real_2);
	var v_map_3: map<(map<bool, int>, (int, int, real)), bool> := map[v_map_int_int_real_1 := false, v_map_int_int_real_2 := false];
	var v_int_int_real_3: (int, int, real) := (29, 15, 5.60);
	var v_map_int_int_real_3: (map<bool, int>, (int, int, real)) := (map[false := 11, true := 16], v_int_int_real_3);
	var v_map_int_int_real_4: (map<bool, int>, (int, int, real)) := v_map_int_int_real_3;
	var v_bool_8: bool := (if ((v_map_int_int_real_4 in v_map_3)) then (v_map_3[v_map_int_int_real_4]) else (false));
	var v_seq_5: seq<bool> := m_method_2(v_bool_8);
	var v_seq_6: seq<seq<set<set<real>>>> := ([[{{-2.59, -0.87}, {12.83, 23.69}}, {{-9.81, -11.61, -23.64}, {20.51, -6.01, 25.59, -27.89}}], [{{16.09, 19.68, -4.88}, {}}], [{{11.16, -8.49, 0.28, -1.30}, {29.24}}, {{}, {10.16, 21.19}}, {{}, {-20.49, 27.78, 3.75, 26.55}, {13.02}, {12.22}}], [{}]] + [[{{8.44, 25.85}}], [{{-12.95}}], [{{3.88, -16.17}, {-16.57}, {-17.64, -24.91}}, {{13.44, 12.58}, {-0.41}}, {{27.02, -5.21, 25.70}}]]);
	var v_int_20: int := v_int_int_real_1.1;
	var v_seq_7: seq<set<set<real>>> := [];
	var v_seq_9: seq<set<set<real>>> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_20]) else ((if ((|v_seq_7| > 0)) then (v_seq_7[19..11]) else (v_seq_7))));
	var v_seq_8: seq<int> := (match 'W' {
		case 'p' => [14, 3]
		case 'D' => [16]
		case _ => [16]
	});
	var v_int_21: int := v_real_int_22.1;
	var v_seq_79: seq<int> := v_seq_8;
	var v_int_126: int := v_int_21;
	var v_int_127: int := safe_index_seq(v_seq_79, v_int_126);
	v_int_21 := v_int_127;
	var v_int_22: int := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_21]) else (v_real_int_17.1));
	var v_seq_80: seq<set<set<real>>> := v_seq_9;
	var v_int_128: int := v_int_22;
	var v_int_129: int := safe_index_seq(v_seq_80, v_int_128);
	v_int_22 := v_int_129;
	var v_seq_10: seq<set<set<real>>> := [{{-14.58, 15.86, 9.16}, {-29.41, 19.25}, {}, {18.99, 21.83, -25.32}}, {{}, {-7.36}, {-16.68, 6.07}, {6.28}}, {{-14.43, 25.14}, {-25.60, 29.24, -15.41, 26.05}}, {{-21.74, -5.51}}];
	var v_int_23: int := 6;
	var v_seq_11: seq<set<set<real>>> := [{{18.02, 29.18, -7.14, 18.16}}, {}];
	var v_int_24: int := 27;
	var v_char_7: char := (if (false) then ('B') else ('T'));
	var v_char_6: char := 'A';
	var v_bool_9: bool := false;
	var v_real_3: real := m_method_5(v_char_6, v_bool_9);
	var v_real_4: real := v_real_3;
	var v_bool_10: bool := m_method_1(v_char_7, v_real_4);
	var v_int_25: int := 15;
	var v_int_26: int := 12;
	var v_int_27: int := safe_division(v_int_25, v_int_26);
	var v_set_1: set<seq<int>>, v_bool_11: bool, v_set_2: set<set<real>>, v_int_28: int := (((map[[13] := {v_real_int_1, v_real_int_2, v_real_int_3}, [26, 18] := {v_real_int_4, v_real_int_5, v_real_int_6, v_real_int_7}, [28, 19, 17, 25] := {v_real_int_8, v_real_int_9, v_real_int_10, v_real_int_11}, [-22, 22] := {v_real_int_12, v_real_int_13, v_real_int_14, v_real_int_15}, [24] := {v_real_int_16, v_real_int_17}] + map[[6] := {v_real_int_18, v_real_int_19, v_real_int_20, v_real_int_21}, [8, 29, 12, 21] := {v_real_int_22, v_real_int_23, v_real_int_24}, [] := {v_real_int_25, v_real_int_26, v_real_int_27}]) - (map[v_DT_1_4_1 := [7, 19, -23, 3]]).Values)).Keys, ((if (v_bool_6) then (v_bool_6) else ((if (true) then (false) else (false)))) in v_seq_5), (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_22]) else (((if ((|v_seq_10| > 0)) then (v_seq_10[v_int_23]) else ({{}, {-25.09, 23.94, -2.12}, {3.20}})) - (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_24]) else ({{7.49}, {-28.91, -17.70, 29.23}, {1.63}, {5.32, -19.86, 1.28, -13.01}}))))), (if (v_bool_10) then ((v_int_27 + v_real_int_18.1)) else (v_int_23));
	var v_array_1: array<bool> := new bool[4] [true, false, false, false];
	var v_array_2: array<bool> := new bool[4] [false, true, true, false];
	var v_array_3: array<bool> := new bool[4] [false, true, false, true];
	var v_seq_12: seq<array<bool>> := [v_array_1, v_array_2, v_array_3];
	var v_seq_81: seq<array<bool>> := v_seq_12;
	var v_int_132: int := -8;
	var v_int_133: int := 20;
	var v_int_134: int, v_int_135: int := safe_subsequence(v_seq_81, v_int_132, v_int_133);
	var v_int_130: int, v_int_131: int := v_int_134, v_int_135;
	var v_seq_13: seq<array<bool>> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_130..v_int_131]) else (v_seq_12));
	var v_int_30: int := v_real_int_4.1;
	var v_array_4: array<bool> := new bool[4] [true, true, false, false];
	var v_array_5: array<bool> := new bool[5] [false, true, true, false, true];
	var v_map_9: map<bool, int> := ((map[true := 6, false := 21] - {true}) - ({true} * {true}));
	var v_int_48: int := m_method_6(v_map_9);
	var v_int_94: int, v_int_95: int := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_30]) else ((if (true) then (v_array_4) else (v_array_5)))).Length, v_int_48;
	for v_int_29 := v_int_94 downto v_int_95 
		invariant (v_int_29 - v_int_95 >= 0) && ((((v_int_29 == 3)) ==> ((((v_char_1 == 'x')) && ((v_char_6 == 'A')) && ((v_char_7 == 'T'))))))
	{
		var v_map_10: map<char, char> := map['p' := 'R'];
		var v_char_14: char := 'n';
		var v_seq_22: seq<char> := (['o'] + ['M']);
		var v_map_11: map<bool, int> := map[true := 29];
		var v_int_49: int := m_method_6(v_map_11);
		var v_int_50: int := v_int_49;
		var v_map_12: map<char, char> := map['w' := 'D', 'i' := 'w'];
		var v_char_15: char := 'Q';
		match (if (((if (true) then ('X') else ('Z')) < v_char_7)) then ((if ((false && true)) then ((if (false) then ('Q') else ('a'))) else ((if ((v_char_14 in v_map_10)) then (v_map_10[v_char_14]) else ('k'))))) else ((if ((|v_seq_22| > 0)) then (v_seq_22[v_int_50]) else ((if ((v_char_15 in v_map_12)) then (v_map_12[v_char_15]) else ('e')))))) {
			case 'R' => {
				var v_map_13: map<char, bool> := map['y' := false, 'x' := true];
				var v_char_16: char := 'd';
				var v_seq_23: seq<bool> := [false, true];
				var v_int_51: int := 5;
				var v_map_15: map<char, bool> := (map['L' := true, 'm' := true, 'd' := true] + map['j' := true, 'F' := false, 'C' := true]);
				var v_map_14: map<char, char> := map['M' := 'g', 'H' := 'e', 'A' := 'q'];
				var v_char_17: char := 'T';
				var v_char_18: char := (if ((v_char_17 in v_map_14)) then (v_map_14[v_char_17]) else ('J'));
				if (match 'J' {
					case _ => v_array_5[2]
				}) {
					
				} else {
					match (if (v_array_2[3]) then ((match 'v' {
						case _ => (if (false) then ('V') else ('I'))
					})) else (v_char_14)) {
						case _ => {
							return ;
						}
						
					}
					
				}
				return ;
			}
				case _ => {
				var v_real_int_28: (real, int) := (-26.49, 6);
				var v_real_int_29: (real, int) := (16.15, 12);
				var v_real_int_30: (real, int) := (28.08, 8);
				var v_real_int_31: (real, int) := (26.37, 5);
				var v_real_int_32: (real, int) := (21.47, 17);
				var v_real_int_33: (real, int) := (7.23, 4);
				var v_real_int_34: (real, int) := (-0.88, 14);
				var v_real_int_35: (real, int) := (1.53, 11);
				var v_real_int_36: (real, int) := (24.90, -2);
				var v_real_int_37: (real, int) := (-15.25, 6);
				var v_int_int_real_4: (int, int, real) := (-17, 17, -4.64);
				var v_int_int_real_5: (int, int, real) := (1, 4, -5.27);
				var v_int_int_real_6: (int, int, real) := (-17, 17, -4.64);
				var v_map_int_int_real_5: (map<bool, int>, (int, int, real)) := (map[false := 22, true := 18], v_int_int_real_6);
				var v_int_int_real_7: (int, int, real) := (1, 4, -5.27);
				var v_map_int_int_real_6: (map<bool, int>, (int, int, real)) := (map[false := 23, true := 5], v_int_int_real_7);
				var v_int_int_real_8: (int, int, real) := (-17, 17, -4.64);
				var v_map_int_int_real_7: (map<bool, int>, (int, int, real)) := (map[false := 22, true := 18], v_int_int_real_8);
				var v_int_int_real_9: (int, int, real) := (1, 4, -5.27);
				var v_map_int_int_real_8: (map<bool, int>, (int, int, real)) := (map[false := 23, true := 5], v_int_int_real_9);
				var v_int_int_real_10: (int, int, real) := (29, 15, 5.60);
				var v_map_int_int_real_9: (map<bool, int>, (int, int, real)) := (map[false := 11, true := 16], v_int_int_real_10);
				var v_int_int_real_11: (int, int, real) := (29, 15, 5.60);
				var v_map_int_int_real_10: (map<bool, int>, (int, int, real)) := (map[false := 11, true := 16], v_int_int_real_11);
				var v_real_int_38: (real, int) := (1.51, 6);
				var v_real_int_39: (real, int) := (0.73, 28);
				var v_real_int_40: (real, int) := (16.85, 29);
				var v_real_int_41: (real, int) := (-25.35, 13);
				var v_real_int_42: (real, int) := (27.95, 0);
				var v_real_int_43: (real, int) := (-23.50, -18);
				var v_real_int_44: (real, int) := (14.23, 21);
				var v_real_int_45: (real, int) := (-11.44, 26);
				var v_real_int_46: (real, int) := (9.84, 5);
				var v_int_int_real_12: (int, int, real) := (29, 15, 5.60);
				var v_int_int_real_13: (int, int, real) := (-17, 17, -4.64);
				var v_int_int_real_14: (int, int, real) := (1, 4, -5.27);
				var v_int_int_real_15: (int, int, real) := (29, 15, 5.60);
				var v_real_int_47: (real, int) := (25.59, 24);
				var v_real_int_48: (real, int) := (-27.55, 28);
				var v_real_int_49: (real, int) := (-10.97, 11);
				var v_real_int_50: (real, int) := (29.38, 19);
				var v_real_int_51: (real, int) := (3.78, 0);
				var v_real_int_52: (real, int) := (14.24, -16);
				var v_real_int_53: (real, int) := (-26.15, 24);
				var v_real_int_54: (real, int) := (11.81, 0);
				print "v_char_15", " ", (v_char_15 == 'Q'), " ", "v_char_14", " ", (v_char_14 == 'n'), " ", "v_int_49", " ", v_int_49, " ", "v_seq_22", " ", (v_seq_22 == ['o', 'M']), " ", "v_map_11", " ", (v_map_11 == map[true := 29]), " ", "v_int_29", " ", v_int_29, " ", "v_map_12", " ", (v_map_12 == map['w' := 'D', 'i' := 'w']), " ", "v_map_10", " ", (v_map_10 == map['p' := 'R']), " ", "v_int_50", " ", v_int_50, " ", "v_real_int_19", " ", (v_real_int_19 == v_real_int_28), " ", "v_array_5[3]", " ", v_array_5[3], " ", "v_real_int_16.1", " ", v_real_int_16.1, " ", "v_real_int_4.0", " ", (v_real_int_4.0 == -23.50), " ", "v_real_int_4.1", " ", v_real_int_4.1, " ", "v_real_int_8.0", " ", (v_real_int_8.0 == 0.73), " ", "v_int_48", " ", v_int_48, " ", "v_real_int_8.1", " ", v_real_int_8.1, " ", "v_real_int_10", " ", (v_real_int_10 == v_real_int_29), " ", "v_real_int_11", " ", (v_real_int_11 == v_real_int_30), " ", "v_real_int_12", " ", (v_real_int_12 == v_real_int_31), " ", "v_real_int_12.1", " ", v_real_int_12.1, " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_real_int_13", " ", (v_real_int_13 == v_real_int_32), " ", "v_real_int_16.0", " ", (v_real_int_16.0 == 1.53), " ", "v_real_int_14", " ", (v_real_int_14 == v_real_int_33), " ", "v_real_int_15", " ", (v_real_int_15 == v_real_int_34), " ", "v_real_int_16", " ", (v_real_int_16 == v_real_int_35), " ", "v_map_int_int_real_2.0", " ", (v_map_int_int_real_2.0 == map[false := 22, true := 18]), " ", "v_real_int_12.0", " ", (v_real_int_12.0 == 26.37), " ", "v_real_int_17", " ", (v_real_int_17 == v_real_int_36), " ", "v_array_5[2]", " ", v_array_5[2], " ", "v_real_int_18", " ", (v_real_int_18 == v_real_int_37), " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_array_5[4]", " ", v_array_5[4], " ", "v_map_int_int_real_2.1", " ", (v_map_int_int_real_2.1 == v_int_int_real_4), " ", "v_set_2", " ", (v_set_2 == {{25.85, 8.44}}), " ", "v_set_1", " ", (v_set_1 == {[], [6], [24], [26, 18], [28, 19, 17, 25], [13], [-22, 22], [8, 29, 12, 21]}), " ", "v_real_int_24.1", " ", v_real_int_24.1, " ", "v_real_int_24.0", " ", (v_real_int_24.0 == 3.78), " ", "v_real_1", " ", (v_real_1 == 21.27), " ", "v_bool_11", " ", v_bool_11, " ", "v_real_3", " ", (v_real_3 == 28.84), " ", "v_real_int_20.1", " ", v_real_int_20.1, " ", "v_real_4", " ", (v_real_4 == 28.84), " ", "v_real_int_20.0", " ", (v_real_int_20.0 == 25.59), " ", "v_bool_10", " ", v_bool_10, " ", "v_int_30", " ", v_int_30, " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_real_int_17.1", " ", v_real_int_17.1, " ", "v_real_int_17.0", " ", (v_real_int_17.0 == 24.90), " ", "v_real_int_3.0", " ", (v_real_int_3.0 == 14.23), " ", "v_real_int_3.1", " ", v_real_int_3.1, " ", "v_int_int_real_3.2", " ", (v_int_int_real_3.2 == 5.60), " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_int_int_real_3.1", " ", v_int_int_real_3.1, " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_int_int_real_3.0", " ", v_int_int_real_3.0, " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_real_int_7.0", " ", (v_real_int_7.0 == 16.85), " ", "v_real_int_7.1", " ", v_real_int_7.1, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_real_int_13.1", " ", v_real_int_13.1, " ", "v_real_int_13.0", " ", (v_real_int_13.0 == 21.47), " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_map_int_int_real_1.0", " ", (v_map_int_int_real_1.0 == map[false := 23, true := 5]), " ", "v_array_5[0]", " ", v_array_5[0], " ", "v_map_int_int_real_1.1", " ", (v_map_int_int_real_1.1 == v_int_int_real_5), " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_char_1", " ", (v_char_1 == 'x'), " ", "v_map_9", " ", (v_map_9 == map[false := 21]), " ", "v_char_7", " ", (v_char_7 == 'T'), " ", "v_char_6", " ", (v_char_6 == 'A'), " ", "v_map_int_int_real_2", " ", (v_map_int_int_real_2 == v_map_int_int_real_5), " ", "v_map_int_int_real_1", " ", (v_map_int_int_real_1 == v_map_int_int_real_6), " ", "v_map_3", " ", (v_map_3 == map[v_map_int_int_real_7 := false, v_map_int_int_real_8 := false]), " ", "v_map_int_int_real_4", " ", (v_map_int_int_real_4 == v_map_int_int_real_9), " ", "v_map_int_int_real_3", " ", (v_map_int_int_real_3 == v_map_int_int_real_10), " ", "v_real_int_25.0", " ", (v_real_int_25.0 == 14.24), " ", "v_real_int_25.1", " ", v_real_int_25.1, " ", "v_real_int_21.0", " ", (v_real_int_21.0 == -27.55), " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_real_int_21.1", " ", v_real_int_21.1, " ", "v_array_5[1]", " ", v_array_5[1], " ", "v_DT_1_4_4", " ", v_DT_1_4_4, " ", "v_DT_1_4_3", " ", v_DT_1_4_3, " ", "v_real_int_18.0", " ", (v_real_int_18.0 == -15.25), " ", "v_DT_1_4_2", " ", v_DT_1_4_2, " ", "v_real_int_18.1", " ", v_real_int_18.1, " ", "v_DT_1_4_1", " ", v_DT_1_4_1, " ", "v_real_int_2.0", " ", (v_real_int_2.0 == -11.44), " ", "v_real_int_2.1", " ", v_real_int_2.1, " ", "v_real_int_9", " ", (v_real_int_9 == v_real_int_38), " ", "v_real_int_8", " ", (v_real_int_8 == v_real_int_39), " ", "v_real_int_7", " ", (v_real_int_7 == v_real_int_40), " ", "v_real_int_6", " ", (v_real_int_6 == v_real_int_41), " ", "v_int_int_real_2.2", " ", (v_int_int_real_2.2 == -4.64), " ", "v_real_int_5", " ", (v_real_int_5 == v_real_int_42), " ", "v_int_int_real_2.1", " ", v_int_int_real_2.1, " ", "v_real_int_4", " ", (v_real_int_4 == v_real_int_43), " ", "v_int_int_real_2.0", " ", v_int_int_real_2.0, " ", "v_real_int_3", " ", (v_real_int_3 == v_real_int_44), " ", "v_real_int_6.0", " ", (v_real_int_6.0 == -25.35), " ", "v_real_int_2", " ", (v_real_int_2 == v_real_int_45), " ", "v_real_int_6.1", " ", v_real_int_6.1, " ", "v_real_int_1", " ", (v_real_int_1 == v_real_int_46), " ", "v_real_int_14.0", " ", (v_real_int_14.0 == 7.23), " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_real_int_14.1", " ", v_real_int_14.1, " ", "v_real_int_10.0", " ", (v_real_int_10.0 == 16.15), " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_real_int_10.1", " ", v_real_int_10.1, " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_real_int_26.1", " ", v_real_int_26.1, " ", "v_real_int_26.0", " ", (v_real_int_26.0 == -26.15), " ", "v_real_int_22.1", " ", v_real_int_22.1, " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_real_int_22.0", " ", (v_real_int_22.0 == -10.97), " ", "v_array_4[2]", " ", v_array_4[2], " ", "v_real_int_19.1", " ", v_real_int_19.1, " ", "v_real_int_19.0", " ", (v_real_int_19.0 == -26.49), " ", "v_real_int_1.1", " ", v_real_int_1.1, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_real_int_5.0", " ", (v_real_int_5.0 == 27.95), " ", "v_real_int_1.0", " ", (v_real_int_1.0 == 9.84), " ", "v_bool_6", " ", v_bool_6, " ", "v_real_int_9.1", " ", v_real_int_9.1, " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_int_int_real_1.2", " ", (v_int_int_real_1.2 == -5.27), " ", "v_int_22", " ", v_int_22, " ", "v_int_int_real_1.1", " ", v_int_int_real_1.1, " ", "v_int_21", " ", v_int_21, " ", "v_real_int_5.1", " ", v_real_int_5.1, " ", "v_int_int_real_1.0", " ", v_int_int_real_1.0, " ", "v_int_int_real_3", " ", (v_int_int_real_3 == v_int_int_real_12), " ", "v_seq_10", " ", (v_seq_10 == [{{}, {-29.41, 19.25}, {9.16, 15.86, -14.58}, {18.99, 21.83, -25.32}}, {{}, {6.07, -16.68}, {-7.36}, {6.28}}, {{25.14, -14.43}, {29.24, 26.05, -25.60, -15.41}}, {{-5.51, -21.74}}]), " ", "v_int_28", " ", v_int_28, " ", "v_int_int_real_2", " ", (v_int_int_real_2 == v_int_int_real_13), " ", "v_seq_11", " ", (v_seq_11 == [{{18.16, -7.14, 18.02, 29.18}}, {}]), " ", "v_int_27", " ", v_int_27, " ", "v_int_int_real_1", " ", (v_int_int_real_1 == v_int_int_real_14), " ", "v_int_26", " ", v_int_26, " ", "v_seq_12", " ", (v_seq_12 == [v_array_1, v_array_2, v_array_3]), " ", "v_real_int_9.0", " ", (v_real_int_9.0 == 1.51), " ", "v_int_25", " ", v_int_25, " ", "v_seq_13", " ", (v_seq_13 == []), " ", "v_real_int_15.1", " ", v_real_int_15.1, " ", "v_real_int_15.0", " ", (v_real_int_15.0 == -0.88), " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_int_20", " ", v_int_20, " ", "v_real_int_11.1", " ", v_real_int_11.1, " ", "v_real_int_11.0", " ", (v_real_int_11.0 == 28.08), " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_map_int_int_real_3.0", " ", (v_map_int_int_real_3.0 == map[false := 11, true := 16]), " ", "v_map_int_int_real_3.1", " ", (v_map_int_int_real_3.1 == v_int_int_real_15), " ", "v_real_int_27.1", " ", v_real_int_27.1, " ", "v_seq_9", " ", (v_seq_9 == [{{25.85, 8.44}}]), " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", (v_seq_7 == []), " ", "v_seq_6", " ", (v_seq_6 == [[{{-0.87, -2.59}, {12.83, 23.69}}, {{-6.01, 25.59, -27.89, 20.51}, {-23.64, -9.81, -11.61}}], [{{}, {19.68, -4.88, 16.09}}], [{{29.24}, {0.28, -1.30, 11.16, -8.49}}, {{}, {21.19, 10.16}}, {{}, {13.02}, {12.22}, {27.78, 26.55, -20.49, 3.75}}], [{}], [{{25.85, 8.44}}], [{{-12.95}}], [{{-16.17, 3.88}, {-24.91, -17.64}, {-16.57}}, {{13.44, 12.58}, {-0.41}}, {{27.02, -5.21, 25.70}}]]), " ", "v_seq_5", " ", v_seq_5, " ", "v_real_int_20", " ", (v_real_int_20 == v_real_int_47), " ", "v_real_int_21", " ", (v_real_int_21 == v_real_int_48), " ", "v_real_int_22", " ", (v_real_int_22 == v_real_int_49), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_real_int_23", " ", (v_real_int_23 == v_real_int_50), " ", "v_real_int_23.1", " ", v_real_int_23.1, " ", "v_real_int_24", " ", (v_real_int_24 == v_real_int_51), " ", "v_real_int_27.0", " ", (v_real_int_27.0 == 11.81), " ", "v_real_int_25", " ", (v_real_int_25 == v_real_int_52), " ", "v_real_int_26", " ", (v_real_int_26 == v_real_int_53), " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_real_int_27", " ", (v_real_int_27 == v_real_int_54), " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_real_int_23.0", " ", (v_real_int_23.0 == 29.38), "\n";
				return ;
			}
			
		}
		
	}
	var v_map_28: map<char, int> := map['z' := 25, 'u' := 1, 'O' := 20, 'Q' := 11, 'z' := 14];
	var v_char_31: char := 'M';
	var v_map_29: map<char, int> := map['P' := -2, 'v' := 29, 'e' := 18];
	var v_char_32: char := 'p';
	var v_map_30: map<char, int> := map['p' := -10, 'T' := 27, 'Q' := 22];
	var v_char_33: char := 'L';
	var v_seq_55: seq<int> := [21, 2, 11, 1];
	var v_int_97: int := 16;
	var v_seq_56: seq<int> := [27];
	var v_seq_57: seq<int> := v_seq_56;
	var v_int_98: int := 13;
	var v_int_99: int := safe_index_seq(v_seq_57, v_int_98);
	var v_int_100: int := v_int_99;
	var v_seq_58: seq<int> := (if ((|v_seq_56| > 0)) then (v_seq_56[v_int_100 := 14]) else (v_seq_56));
	var v_int_101: int := (14 * 24);
	var v_seq_59: seq<int> := [8, 8, 1, 13];
	var v_seq_60: seq<int> := (if ((|v_seq_59| > 0)) then (v_seq_59[-11..0]) else (v_seq_59));
	var v_seq_61: seq<int> := v_seq_60;
	var v_int_102: int := (22 / 9);
	var v_int_103: int := safe_index_seq(v_seq_61, v_int_102);
	var v_int_104: int := v_int_103;
	var v_map_31: map<char, int> := map['L' := 4, 'P' := 23, 'e' := 9];
	var v_char_34: char := 't';
	var v_seq_62: seq<int> := (if ((|v_seq_60| > 0)) then (v_seq_60[v_int_104 := (if ((v_char_34 in v_map_31)) then (v_map_31[v_char_34]) else (5))]) else (v_seq_60));
	var v_int_105: int := v_int_94;
	var v_int_124: int, v_int_125: int := (match 'R' {
		case _ => (if ((|v_seq_58| > 0)) then (v_seq_58[v_int_101]) else ((if (true) then (29) else (29))))
	}), (if ((|v_seq_62| > 0)) then (v_seq_62[v_int_105]) else (v_real_int_25.1));
	for v_int_96 := v_int_124 to v_int_125 
		invariant (v_int_125 - v_int_96 >= 0)
	{
		var v_map_32: map<char, real> := map['R' := 26.58, 'a' := -15.69, 'n' := -18.17, 'n' := 2.03]['P' := 13.43];
		var v_seq_63: seq<char> := ['Y', 'V', 'D'];
		var v_int_106: int := 19;
		var v_char_35: char := (if ((|v_seq_63| > 0)) then (v_seq_63[v_int_106]) else ('s'));
		if ((if ((if (true) then (false) else (true))) then (v_real_int_15.0) else (v_real_int_10.0)) <= (if ((v_char_35 in v_map_32)) then (v_map_32[v_char_35]) else (v_real_int_10.0))) {
			continue;
		}
		assert true;
		expect true;
		var v_seq_64: seq<bool> := [true, false];
		var v_int_107: int := -13;
		var v_seq_65: seq<bool> := [false, true, false];
		var v_int_108: int := 15;
		var v_seq_66: seq<char> := ['n', 'I', 'B'];
		var v_seq_67: seq<char> := v_seq_66;
		var v_int_109: int := 26;
		var v_int_110: int := safe_index_seq(v_seq_67, v_int_109);
		var v_int_111: int := v_int_110;
		var v_seq_68: seq<char> := (if ((|v_seq_66| > 0)) then (v_seq_66[v_int_111 := 'm']) else (v_seq_66));
		var v_int_112: int := v_int_107;
		var v_map_33: map<char, bool> := map['U' := true, 'q' := false, 'M' := true];
		var v_char_36: char := 'r';
		var v_seq_69: seq<char> := ['e', 'W', 'u'];
		var v_seq_70: seq<char> := v_seq_69;
		var v_int_113: int := 14;
		var v_int_114: int := safe_index_seq(v_seq_70, v_int_113);
		var v_int_115: int := v_int_114;
		var v_seq_71: seq<char> := ['I', 'G'];
		var v_seq_72: seq<char> := v_seq_71;
		var v_int_116: int := 7;
		var v_int_117: int := safe_index_seq(v_seq_72, v_int_116);
		var v_int_118: int := v_int_117;
		var v_seq_73: seq<char> := (if ((if ((v_char_36 in v_map_33)) then (v_map_33[v_char_36]) else (false))) then ((if ((|v_seq_69| > 0)) then (v_seq_69[v_int_115 := 'c']) else (v_seq_69))) else ((if ((|v_seq_71| > 0)) then (v_seq_71[v_int_118 := 'l']) else (v_seq_71))));
		var v_map_35: map<char, int> := map['y' := 19, 'o' := 8]['C' := 8];
		var v_char_38: char := (if (false) then ('r') else ('W'));
		var v_map_34: map<char, int> := map['y' := 19, 'u' := 17, 'J' := 23];
		var v_char_37: char := 'w';
		var v_int_119: int := (if ((v_char_38 in v_map_35)) then (v_map_35[v_char_38]) else ((if ((v_char_37 in v_map_34)) then (v_map_34[v_char_37]) else (5))));
		var v_map_36: map<char, char> := map['a' := 'H'];
		var v_char_39: char := 'b';
		v_char_36, v_char_37 := (if (((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_107]) else (true)) == (if ((|v_seq_65| > 0)) then (v_seq_65[v_int_108]) else (false)))) then (v_char_7) else ((if ((|v_seq_68| > 0)) then (v_seq_68[v_int_112]) else ((match 'Q' {
			case _ => 'E'
		}))))), (if ((|v_seq_73| > 0)) then (v_seq_73[v_int_119]) else ((match 'I' {
			case _ => v_char_1
		})));
		var v_map_38: map<char, char> := map['Q' := 'N', 'p' := 'A', 'b' := 'k']['G' := 'r'];
		var v_map_37: map<char, char> := map['Q' := 'h', 'J' := 'i', 's' := 's', 'r' := 'W', 'v' := 'a'];
		var v_char_40: char := 'n';
		var v_char_41: char := (if ((v_char_40 in v_map_37)) then (v_map_37[v_char_40]) else ('B'));
		var v_map_39: map<char, char> := map['H' := 'h', 'G' := 'O', 'A' := 'Y', 'm' := 'K', 'd' := 'w']['S' := 'D'];
		var v_seq_74: seq<char> := ['U', 'v', 'B', 'J'];
		var v_int_120: int := 22;
		var v_char_42: char := (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_120]) else ('j'));
		var v_seq_75: seq<char> := ['j', 'H', 'p'];
		var v_int_121: int := 22;
		var v_seq_76: seq<char> := ['w', 'P'];
		var v_seq_77: seq<char> := (if ((|v_seq_76| > 0)) then (v_seq_76[13..10]) else (v_seq_76));
		var v_int_122: int := (if (true) then (13) else (13));
		var v_seq_78: seq<char> := ['G', 'B', 'X', 'n'];
		var v_int_123: int := 2;
		v_char_35, v_char_38 := (match 'B' {
			case _ => (if ((|v_seq_77| > 0)) then (v_seq_77[v_int_122]) else ((if ((|v_seq_78| > 0)) then (v_seq_78[v_int_123]) else ('F'))))
		}), v_char_36;
		continue;
	}
	assert true;
	expect true;
	return ;
}
