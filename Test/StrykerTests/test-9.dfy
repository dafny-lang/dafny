// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_4(p_m_method_4_1: char) returns (ret_1: seq<(real, real)>)
{
	var v_real_real_50: (real, real) := (28.37, 16.58);
	return [v_real_real_50];
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char) returns (ret_1: char)
{
	var v_char_3: char, v_char_4: char, v_char_5: char, v_char_6: char := p_m_method_3_2, (match 'C' {
		case _ => 'u'
	}), (match 'N' {
		case _ => 'b'
	}), (if (false) then ('L') else ('k'));
	var v_char_7: char, v_char_8: char, v_char_9: char, v_char_10: char, v_char_11: char := v_char_5, v_char_6, (match 'R' {
		case _ => 'T'
	}), (match 'E' {
		case _ => 'o'
	}), p_m_method_3_2;
	v_char_11 := v_char_6;
	var v_seq_19: seq<bool> := [true];
	var v_int_40: int := 14;
	if (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_40]) else (true)) {
		var v_map_9: map<char, char> := map['L' := 'w', 'O' := 'D', 'z' := 'x'];
		var v_char_12: char := 'R';
		return (if ((v_char_12 in v_map_9)) then (v_map_9[v_char_12]) else ('B'));
	} else {
		var v_map_10: map<char, char> := map['q' := 'N', 'I' := 'H', 'D' := 'p', 'u' := 'H'];
		var v_char_13: char := 'B';
		return (if ((v_char_13 in v_map_10)) then (v_map_10[v_char_13]) else ('Y'));
	}
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

method m_method_2(p_m_method_2_1: (int, real)) returns (ret_1: seq<seq<bool>>)
{
	return [[true, true, true], [false, false, false], []];
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: char, p_m_method_1_3: (real, real), p_m_method_1_4: int) returns (ret_1: seq<bool>, ret_2: int, ret_3: (real, int, bool), ret_4: (int, real), ret_5: DT_1<bool, int>)
{
	var v_seq_7: seq<map<bool, seq<bool>>> := [map[false := [true, true], true := [false], true := [false, true, true, false], false := [true, true, false]], map[false := [], true := [false, false, true, true], false := [false, false, true, false], false := [false]], map[false := [true, false, false, true]], map[false := [false, true, true, true], false := [false, false]]];
	var v_seq_8: seq<map<bool, seq<bool>>> := v_seq_7;
	var v_int_24: int := 4;
	var v_int_25: int := safe_index_seq(v_seq_8, v_int_24);
	var v_int_26: int := v_int_25;
	var v_seq_9: seq<map<bool, seq<bool>>> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_26 := map[true := [true, false, true, false], true := [false, false, false]]]) else (v_seq_7));
	var v_int_27: int := (match false {
		case _ => 8
	});
	var v_map_2: map<bool, seq<bool>> := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_27]) else (map[false := [false]][true := [false]]));
	var v_bool_2: bool := p_m_method_1_1;
	var v_int_real_1: (int, real) := (8, 8.71);
	var v_int_real_2: (int, real) := v_int_real_1;
	var v_seq_10: seq<seq<bool>> := m_method_2(v_int_real_2);
	var v_seq_11: seq<seq<bool>> := v_seq_10;
	var v_int_28: int := 28;
	var v_int_29: int := 19;
	var v_int_30: int := safe_modulus(v_int_28, v_int_29);
	var v_int_31: int := v_int_30;
	var v_DT_1_1_1: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_2: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_3: DT_1<bool, int> := DT_1_1;
	var v_real_int_bool_1: (real, int, bool) := (2.70, 11, false);
	var v_real_int_bool_2: (real, int, bool) := (-8.23, 19, false);
	var v_DT_1_1_4: DT_1<bool, int> := DT_1_1;
	var v_real_int_bool_3: (real, int, bool) := (-14.69, 29, true);
	var v_real_int_bool_4: (real, int, bool) := (0.63, 2, true);
	var v_DT_1_1_5: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_6: DT_1<bool, int> := DT_1_1;
	var v_real_int_bool_5: (real, int, bool) := (9.51, 1, true);
	var v_real_int_bool_6: (real, int, bool) := (-8.22, 10, false);
	var v_DT_1_1_7: DT_1<bool, int> := DT_1_1;
	var v_real_int_bool_7: (real, int, bool) := (18.21, 21, false);
	var v_real_int_bool_8: (real, int, bool) := (-16.53, -6, true);
	var v_real_int_bool_9: (real, int, bool) := (-14.17, 18, false);
	var v_DT_1_1_8: DT_1<bool, int> := DT_1_1;
	var v_map_3: map<DT_1<bool, int>, seq<(real, int, bool)>> := (map[v_DT_1_1_1 := [], v_DT_1_1_2 := [], v_DT_1_1_3 := [v_real_int_bool_1, v_real_int_bool_2]] + map[v_DT_1_1_4 := [v_real_int_bool_3, v_real_int_bool_4], v_DT_1_1_5 := [], v_DT_1_1_6 := [v_real_int_bool_5, v_real_int_bool_6], v_DT_1_1_7 := [v_real_int_bool_7, v_real_int_bool_8, v_real_int_bool_9], v_DT_1_1_8 := []]);
	var v_DT_1_1_9: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_10: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_11: DT_1<bool, int> := DT_1_1;
	var v_seq_12: seq<DT_1<bool, int>> := [v_DT_1_1_9, v_DT_1_1_10, v_DT_1_1_11];
	var v_int_32: int := -26;
	var v_DT_1_1_12: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_13: DT_1<bool, int> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_32]) else (v_DT_1_1_12));
	var v_real_int_bool_10: (real, int, bool) := (21.34, 7, false);
	var v_real_int_bool_11: (real, int, bool) := (19.82, 9, true);
	var v_seq_13: seq<(real, int, bool)> := [v_real_int_bool_10, v_real_int_bool_11];
	var v_seq_14: seq<(real, int, bool)> := v_seq_13;
	var v_int_33: int := 15;
	var v_int_34: int := safe_index_seq(v_seq_14, v_int_33);
	var v_int_35: int := v_int_34;
	var v_real_int_bool_12: (real, int, bool) := (5.45, 11, true);
	var v_seq_15: seq<(real, int, bool)> := (if ((v_DT_1_1_13 in v_map_3)) then (v_map_3[v_DT_1_1_13]) else ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_35 := v_real_int_bool_12]) else (v_seq_13))));
	var v_int_36: int := v_int_real_1.0;
	var v_real_int_bool_13: (real, int, bool) := (8.29, 11, true);
	var v_real_int_bool_14: (real, int, bool) := (-18.75, 2, true);
	var v_seq_16: seq<(real, int, bool)> := [];
	var v_int_37: int := 16;
	var v_real_int_bool_15: (real, int, bool) := (-6.98, 25, true);
	var v_map_4: map<bool, set<int>> := map[false := {17, -23}];
	var v_bool_3: bool := false;
	var v_DT_1_1_14: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_15: DT_1<bool, int> := DT_1_1;
	var v_map_5: map<DT_1<bool, int>, bool> := map[v_DT_1_1_14 := false, v_DT_1_1_15 := true];
	var v_DT_1_1_16: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_17: DT_1<bool, int> := v_DT_1_1_16;
	var v_DT_1_1_18: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_19: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_20: DT_1<bool, int> := DT_1_1;
	var v_DT_1_1_21: DT_1<bool, int> := DT_1_1;
	return (if ((v_bool_2 in v_map_2)) then (v_map_2[v_bool_2]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_31]) else ((match 16 {
		case _ => []
	}))))), v_int_30, (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_36]) else ((match false {
		case _ => (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_37]) else (v_real_int_bool_15))
	}))), v_int_real_1, (if (((if (true) then ({3}) else ({})) != (if ((v_bool_3 in v_map_4)) then (v_map_4[v_bool_3]) else ({26, 6, -18, 21})))) then (v_DT_1_1_10) else ((if ((if ((v_DT_1_1_17 in v_map_5)) then (v_map_5[v_DT_1_1_17]) else (true))) then ((match true {
		case _ => v_DT_1_1_19
	})) else ((if (true) then (v_DT_1_1_20) else (v_DT_1_1_21))))));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_3: seq<multiset<char>> := [];
	var v_int_8: int := 8;
	var v_int_9: int := safe_index_seq(v_seq_3, v_int_8);
	var v_seq_4: seq<int> := [7, 25, 15];
	var v_int_10: int := 26;
	var v_seq_36: seq<int> := v_seq_4;
	var v_int_72: int := v_int_10;
	var v_int_73: int := safe_index_seq(v_seq_36, v_int_72);
	v_int_10 := v_int_73;
	var v_seq_5: seq<int> := [(if ((|v_seq_4| > 0)) then (v_seq_4[v_int_10]) else (2))];
	var v_int_11: int := 28;
	var v_seq_37: seq<int> := v_seq_5;
	var v_int_74: int := v_int_11;
	var v_int_75: int := safe_index_seq(v_seq_37, v_int_74);
	v_int_11 := v_int_75;
	var v_int_59: int, v_int_60: int := (match 'l' {
		case 'W' => -15
		case _ => (v_int_9 + v_int_8)
	}), (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_11]) else (v_int_10));
	for v_int_7 := v_int_59 downto v_int_60 
		invariant (v_int_7 - v_int_60 >= 0)
	{
		var v_int_57: int, v_int_58: int := v_int_11, v_int_11;
		for v_int_12 := v_int_57 downto v_int_58 
			invariant (v_int_12 - v_int_58 >= 0)
		{
			var v_real_real_1: (real, real) := (22.81, -12.50);
			var v_real_real_2: (real, real) := (-8.96, -3.66);
			var v_real_real_3: (real, real) := (8.49, 17.22);
			var v_real_real_4: (real, real) := (29.06, -18.94);
			var v_real_real_5: (real, real) := (-22.02, -2.18);
			var v_real_real_6: (real, real) := (-21.73, -2.61);
			var v_real_real_7: (real, real) := (14.86, 27.16);
			var v_real_real_8: (real, real) := (-8.27, 19.59);
			var v_real_real_9: (real, real) := (14.99, 12.92);
			var v_real_real_10: (real, real) := (13.54, -15.92);
			var v_real_real_11: (real, real) := (-16.69, -22.54);
			var v_real_real_12: (real, real) := (8.75, -1.26);
			var v_real_real_13: (real, real) := (14.64, 20.73);
			var v_real_real_14: (real, real) := (-18.81, 25.65);
			var v_real_real_15: (real, real) := (-26.09, 10.53);
			var v_real_real_16: (real, real) := (-21.65, 11.93);
			var v_real_real_17: (real, real) := (-22.05, -0.89);
			var v_real_real_18: (real, real) := (29.81, -0.32);
			var v_real_real_19: (real, real) := (-22.99, -19.48);
			var v_real_real_20: (real, real) := (9.12, -19.42);
			var v_real_real_21: (real, real) := (17.20, 9.22);
			var v_real_real_22: (real, real) := (13.67, -4.32);
			var v_real_real_23: (real, real) := (-14.88, 4.36);
			var v_real_real_24: (real, real) := (-29.21, -0.37);
			var v_real_real_25: (real, real) := (0.26, -21.73);
			var v_real_real_26: (real, real) := (-13.19, 17.23);
			var v_real_real_27: (real, real) := (11.79, -9.98);
			var v_real_real_28: (real, real) := (23.04, -29.55);
			var v_real_real_29: (real, real) := (16.97, -8.13);
			var v_real_real_30: (real, real) := (29.79, -13.61);
			var v_real_real_31: (real, real) := (18.86, 7.70);
			var v_real_real_32: (real, real) := (9.08, 22.11);
			var v_real_real_33: (real, real) := (12.41, 26.58);
			var v_real_real_34: (real, real) := (-11.01, 4.29);
			var v_seq_6: seq<map<seq<(real, real)>, char>> := ([map[[v_real_real_1, v_real_real_2, v_real_real_3, v_real_real_4] := 'H', [] := 'B'], map[[v_real_real_5, v_real_real_6, v_real_real_7] := 'Q'], map[[v_real_real_8, v_real_real_9, v_real_real_10, v_real_real_11] := 'E', [v_real_real_12, v_real_real_13] := 'q', [v_real_real_14] := 'p', [v_real_real_15, v_real_real_16, v_real_real_17] := 'L', [v_real_real_18, v_real_real_19, v_real_real_20] := 'P']] + [map[[v_real_real_21, v_real_real_22, v_real_real_23, v_real_real_24] := 'F', [] := 'M'], map[[v_real_real_25, v_real_real_26, v_real_real_27, v_real_real_28] := 'J', [v_real_real_29, v_real_real_30, v_real_real_31, v_real_real_32] := 'N'], map[[] := 'V', [v_real_real_33, v_real_real_34] := 'v']]);
			var v_bool_bool_bool_1: (bool, bool, bool) := (false, true, true);
			var v_map_1: map<(bool, bool, bool), int> := map[v_bool_bool_bool_1 := 15];
			var v_bool_bool_bool_2: (bool, bool, bool) := (false, true, true);
			var v_bool_bool_bool_3: (bool, bool, bool) := v_bool_bool_bool_2;
			var v_int_13: int := (if ((v_bool_bool_bool_3 in v_map_1)) then (v_map_1[v_bool_bool_bool_3]) else (1));
			var v_real_real_35: (real, real) := (-21.63, -22.73);
			var v_real_real_36: (real, real) := (26.02, -19.51);
			var v_real_real_37: (real, real) := (29.65, -18.51);
			var v_real_real_38: (real, real) := (0.27, 9.41);
			var v_int_14: int := 2;
			var v_int_15: int := 23;
			var v_int_16: int := safe_division(v_int_14, v_int_15);
			var v_int_20: int := (match 18 {
				case _ => v_int_12
			});
			var v_int_17: int := 29;
			var v_int_18: int := 29;
			var v_int_19: int := safe_division(v_int_17, v_int_18);
			var v_int_21: int := (v_int_19 * (if (false) then (25) else (1)));
			var v_int_22: int := safe_division(v_int_20, v_int_21);
			var v_real_int_1: (real, int) := (2.42, 29);
			var v_real_real_39: (real, real) := (-14.91, -23.14);
			var v_bool_bool_1: (bool, bool) := (true, true);
			var v_real_int_real_real_bool_bool_1: ((real, int), (real, real), (bool, bool)) := (v_real_int_1, v_real_real_39, v_bool_bool_1);
			var v_real_int_2: (real, int) := (-19.32, 23);
			var v_real_real_40: (real, real) := (20.06, -3.32);
			var v_bool_bool_2: (bool, bool) := (false, false);
			var v_real_int_real_real_bool_bool_2: ((real, int), (real, real), (bool, bool)) := (v_real_int_2, v_real_real_40, v_bool_bool_2);
			var v_real_int_3: (real, int) := (-7.71, 6);
			var v_real_real_41: (real, real) := (15.70, -4.88);
			var v_bool_bool_3: (bool, bool) := (false, false);
			var v_real_int_real_real_bool_bool_3: ((real, int), (real, real), (bool, bool)) := (v_real_int_3, v_real_real_41, v_bool_bool_3);
			var v_real_int_4: (real, int) := (5.22, 13);
			var v_real_real_42: (real, real) := (-23.11, -0.52);
			var v_bool_bool_4: (bool, bool) := (true, false);
			var v_real_int_real_real_bool_bool_4: ((real, int), (real, real), (bool, bool)) := (v_real_int_4, v_real_real_42, v_bool_bool_4);
			var v_real_int_5: (real, int) := (-2.46, 8);
			var v_real_real_43: (real, real) := (15.47, 9.00);
			var v_bool_bool_5: (bool, bool) := (false, false);
			var v_real_int_real_real_bool_bool_5: ((real, int), (real, real), (bool, bool)) := (v_real_int_5, v_real_real_43, v_bool_bool_5);
			var v_real_int_6: (real, int) := (15.67, 28);
			var v_real_real_44: (real, real) := (-7.77, -3.20);
			var v_bool_bool_6: (bool, bool) := (true, true);
			var v_real_int_real_real_bool_bool_6: ((real, int), (real, real), (bool, bool)) := (v_real_int_6, v_real_real_44, v_bool_bool_6);
			var v_real_int_7: (real, int) := (14.84, 10);
			var v_real_real_45: (real, real) := (-5.86, -5.61);
			var v_bool_bool_7: (bool, bool) := (true, true);
			var v_real_int_real_real_bool_bool_7: ((real, int), (real, real), (bool, bool)) := (v_real_int_7, v_real_real_45, v_bool_bool_7);
			var v_real_int_8: (real, int) := (11.97, -8);
			var v_real_real_46: (real, real) := (2.41, -8.00);
			var v_bool_bool_8: (bool, bool) := (false, false);
			var v_real_int_real_real_bool_bool_8: ((real, int), (real, real), (bool, bool)) := (v_real_int_8, v_real_real_46, v_bool_bool_8);
			var v_real_int_9: (real, int) := (-21.41, -3);
			var v_real_real_47: (real, real) := (11.08, 22.53);
			var v_bool_bool_9: (bool, bool) := (false, true);
			var v_real_int_real_real_bool_bool_9: ((real, int), (real, real), (bool, bool)) := (v_real_int_9, v_real_real_47, v_bool_bool_9);
			var v_real_int_10: (real, int) := (-21.60, 15);
			var v_real_real_48: (real, real) := (-16.30, 25.56);
			var v_bool_bool_10: (bool, bool) := (false, true);
			var v_real_int_real_real_bool_bool_10: ((real, int), (real, real), (bool, bool)) := (v_real_int_10, v_real_real_48, v_bool_bool_10);
			var v_real_int_11: (real, int) := (26.38, 5);
			var v_real_real_49: (real, real) := (27.80, -5.54);
			var v_bool_bool_11: (bool, bool) := (false, false);
			var v_real_int_real_real_bool_bool_11: ((real, int), (real, real), (bool, bool)) := (v_real_int_11, v_real_real_49, v_bool_bool_11);
			var v_set_1: set<char>, v_int_23: int, v_bool_1: bool := ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_13]) else ((map[[v_real_real_35] := 'R'] + map[[v_real_real_36, v_real_real_37, v_real_real_38] := 'D'])))).Values, v_int_22, (((if (false) then (map[v_real_int_real_real_bool_bool_1 := false, v_real_int_real_real_bool_bool_2 := true, v_real_int_real_real_bool_bool_3 := false]) else (map[v_real_int_real_real_bool_bool_4 := true, v_real_int_real_real_bool_bool_5 := true, v_real_int_real_real_bool_bool_6 := true]))).Keys != (({} - {v_real_int_real_real_bool_bool_7, v_real_int_real_real_bool_bool_8, v_real_int_real_real_bool_bool_9, v_real_int_real_real_bool_bool_10}) * (match 3 {
				case _ => {v_real_int_real_real_bool_bool_11}
			})));
			var v_array_1: array<multiset<bool>> := new multiset<bool>[5] [multiset{false, false}, multiset{true, false}, multiset({true, true, true, true}), multiset{false, true, true, true}, multiset{false, false, true}];
			var v_array_2: array<multiset<bool>> := new multiset<bool>[5] [multiset{true, false}, multiset{true, true, false}, multiset{true}, multiset{true, true, false, true}, multiset{true, true, false, true}];
			var v_array_3: array<multiset<bool>> := new multiset<bool>[5] [multiset{true, false, false, true}, multiset({}), multiset{true, false, false, false}, multiset{true, false}, multiset({true, false, true})];
			var v_array_4: array<multiset<bool>> := new multiset<bool>[3] [multiset{true, true}, multiset({true}), multiset({})];
			var v_array_5: array<multiset<bool>> := new multiset<bool>[3] [multiset{true, true}, multiset({true, true}), multiset{true, true}];
			var v_array_6: array<multiset<bool>> := new multiset<bool>[3] [multiset({}), multiset{false}, multiset{true, true, true}];
			var v_array_7: array<multiset<bool>> := new multiset<bool>[4];
			v_array_7[0] := multiset{true, false};
			v_array_7[1] := multiset{false, true, false, false};
			v_array_7[2] := multiset{false, true};
			v_array_7[3] := multiset{false, true};
			var v_array_8: array<multiset<bool>> := new multiset<bool>[3] [multiset{false}, multiset{false, false, true}, multiset{}];
			var v_array_9: array<multiset<bool>> := new multiset<bool>[4] [multiset{false, false, false, false}, multiset{true}, multiset({}), multiset{false, false, true, false}];
			var v_array_10: array<multiset<bool>> := new multiset<bool>[5] [multiset{false, true, false, true}, multiset{false, true, false}, multiset({}), multiset({true, true}), multiset{}];
			var v_array_11: array<multiset<bool>> := new multiset<bool>[4] [multiset({}), multiset{false}, multiset{true, true, false, false}, multiset({false, true, false, false})];
			var v_array_12: array<multiset<bool>> := new multiset<bool>[3] [multiset({false, true}), multiset({false, true, false, true}), multiset{false, false, false}];
			var v_array_13: array<multiset<bool>> := new multiset<bool>[5] [multiset{}, multiset{false}, multiset{false}, multiset({false, false, true}), multiset{false, false, true}];
			var v_array_14: array<multiset<bool>> := new multiset<bool>[5] [multiset{true}, multiset{true, true}, multiset{false, false}, multiset{true, false, true}, multiset{true, true, false, false}];
			var v_array_15: array<multiset<bool>> := new multiset<bool>[3] [multiset{false, false, true}, multiset{false, true, true, true}, multiset({})];
			var v_map_6: map<char, map<array<multiset<bool>>, bool>> := map['O' := map[v_array_1 := false, v_array_2 := false, v_array_3 := false, v_array_4 := false, v_array_5 := false], 'K' := map[v_array_6 := false, v_array_7 := false, v_array_8 := false, v_array_9 := true, v_array_10 := true], 'Q' := map[v_array_11 := true, v_array_12 := false, v_array_13 := false, v_array_14 := true], 'Y' := map[v_array_15 := false]];
			var v_char_1: char := 'N';
			var v_array_16: array<multiset<bool>> := new multiset<bool>[5] [multiset{true, false, true}, multiset{true}, multiset({false, true}), multiset{}, multiset({true, false, false, true})];
			var v_array_17: array<multiset<bool>> := new multiset<bool>[3] [multiset{true, false, false, true}, multiset({false, false, true}), multiset({false, false, false})];
			var v_array_18: array<multiset<bool>> := new multiset<bool>[5] [multiset({true, true, false, true}), multiset({false}), multiset{true}, multiset({false}), multiset{true}];
			var v_array_19: array<multiset<bool>> := new multiset<bool>[3] [multiset{false, true, false}, multiset{true, false, false, true}, multiset{}];
			var v_map_7: map<array<multiset<bool>>, bool> := (if ((v_char_1 in v_map_6)) then (v_map_6[v_char_1]) else (map[v_array_16 := true, v_array_17 := true, v_array_18 := false, v_array_19 := false]));
			var v_array_20: array<multiset<bool>> := v_array_17;
			var v_bool_4: bool := ((if ((v_array_20 in v_map_7)) then (v_map_7[v_array_20]) else ((false || false))) != v_bool_bool_7.1);
			var v_map_8: map<char, char> := map['r' := 'c', 'v' := 'P', 'B' := 'l', 'c' := 'a'];
			var v_char_2: char := 'g';
			var v_map_13: map<int, char> := (match false {
				case _ => map[28 := 'y']
			})[(10 - 23) := (if ((v_char_2 in v_map_8)) then (v_map_8[v_char_2]) else ('I'))];
			var v_seq_17: seq<int> := [27, 2, 16];
			var v_int_38: int := 10;
			var v_seq_18: seq<int> := [22, -29];
			var v_int_39: int := 8;
			var v_int_41: int := ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_38]) else (5)) % (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_39]) else (23)));
			var v_char_16: char := (if (true) then ('O') else ('D'));
			var v_map_11: map<char, char> := map['z' := 'E'];
			var v_char_14: char := 'I';
			var v_char_17: char := (if ((v_char_14 in v_map_11)) then (v_map_11[v_char_14]) else ('b'));
			var v_map_12: map<char, char> := map['A' := 'Y', 'J' := 'I', 'V' := 'U', 'c' := 'a'];
			var v_char_15: char := 'b';
			var v_char_18: char := (if ((v_char_15 in v_map_12)) then (v_map_12[v_char_15]) else ('N'));
			var v_char_19: char := m_method_3(v_char_16, v_char_17, v_char_18);
			var v_char_21: char := (if ((v_int_41 in v_map_13)) then (v_map_13[v_int_41]) else (v_char_19));
			var v_char_20: char := 'i';
			var v_seq_20: seq<(real, real)> := m_method_4(v_char_20);
			var v_seq_21: seq<(real, real)> := [];
			var v_seq_22: seq<(real, real)> := v_seq_21;
			var v_int_42: int := 6;
			var v_int_43: int := safe_index_seq(v_seq_22, v_int_42);
			var v_int_44: int := v_int_43;
			var v_real_real_51: (real, real) := (-10.19, 7.92);
			var v_seq_23: seq<(real, real)> := (v_seq_20 + (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_44 := v_real_real_51]) else (v_seq_21)));
			var v_int_45: int := -19;
			var v_int_46: int := -12;
			var v_int_47: int := safe_division(v_int_45, v_int_46);
			var v_int_48: int := (match 'C' {
				case _ => v_int_47
			});
			var v_seq_24: seq<seq<(real, real)>> := [];
			var v_int_49: int := 1;
			var v_real_real_52: (real, real) := (28.23, -16.15);
			var v_real_real_53: (real, real) := (28.69, 25.65);
			var v_real_real_54: (real, real) := (14.27, -8.71);
			var v_seq_25: seq<(real, real)> := (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_49]) else ([v_real_real_52, v_real_real_53, v_real_real_54]));
			var v_int_50: int := v_int_38;
			var v_real_real_55: (real, real) := (-27.32, -25.51);
			var v_real_real_56: (real, real) := (0.50, -18.15);
			var v_real_real_57: (real, real) := (25.37, 7.22);
			var v_seq_26: seq<(real, real)> := [v_real_real_55, v_real_real_56, v_real_real_57];
			var v_int_51: int := 26;
			var v_real_real_58: (real, real) := (13.64, 23.04);
			var v_real_real_59: (real, real) := (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_48]) else ((if ((|v_seq_25| > 0)) then (v_seq_25[v_int_50]) else ((if ((|v_seq_26| > 0)) then (v_seq_26[v_int_51]) else (v_real_real_58))))));
			var v_seq_27: seq<int> := (if (true) then ([8, 1]) else ([12, 7, 25, 2]));
			var v_int_52: int := (22 % 29);
			var v_int_53: int := (((16 / 29) * (15 / 14)) / (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_52]) else ((12 / 13))));
			var v_seq_28: seq<bool>, v_int_54: int, v_real_int_bool_16: (real, int, bool), v_int_real_3: (int, real), v_DT_1_1_22: DT_1<bool, int> := m_method_1(v_bool_4, v_char_21, v_real_real_59, v_int_53);
			v_seq_28, v_int_18, v_real_int_bool_16, v_int_real_3, v_DT_1_1_22 := v_seq_28, v_int_54, v_real_int_bool_16, v_int_real_3, v_DT_1_1_22;
			var v_map_15: map<char, char> := v_map_8;
			var v_map_14: map<char, char> := map['x' := 'Z', 'd' := 'h', 'y' := 'f'];
			var v_char_22: char := 'E';
			var v_char_23: char := (if ((v_char_22 in v_map_14)) then (v_map_14[v_char_22]) else ('H'));
			var v_map_16: map<char, map<char, bool>> := map['G' := map['i' := false, 'r' := true, 'j' := false, 't' := false], 'A' := map['B' := true, 'u' := true, 's' := false, 'M' := false], 'M' := map['z' := false]];
			var v_char_24: char := 'b';
			var v_map_17: map<char, bool> := (if ((v_char_24 in v_map_16)) then (v_map_16[v_char_24]) else (map['I' := true, 'V' := true]));
			var v_char_25: char := v_char_14;
			var v_map_18: map<char, char> := map['H' := 'c'];
			var v_char_26: char := 'a';
			var v_map_19: map<char, char> := v_map_12;
			var v_char_27: char := v_char_1;
			var v_seq_29: seq<char> := ['z', 'j', 'u'];
			var v_int_55: int := 20;
			var v_seq_30: seq<char> := ['M', 'l', 'g'];
			var v_int_56: int := 26;
			v_char_18, v_char_1, v_char_19, v_char_15 := (if (v_bool_bool_3.0) then (v_char_14) else ((if ((v_char_23 in v_map_15)) then (v_map_15[v_char_23]) else (v_char_17)))), (if ((if ((v_char_25 in v_map_17)) then (v_map_17[v_char_25]) else (v_bool_bool_8.1))) then ((if ((match 'a' {
				case _ => true
			})) then ((match 'y' {
				case _ => 'o'
			})) else ((if (true) then ('S') else ('F'))))) else ((if ((match 'C' {
				case _ => false
			})) then (v_char_16) else ((if ((v_char_26 in v_map_18)) then (v_map_18[v_char_26]) else ('F')))))), v_char_19, (match 'r' {
				case _ => (if ((match 'w' {
					case _ => false
				})) then ((if (false) then ('C') else ('I'))) else ((if ((|v_seq_30| > 0)) then (v_seq_30[v_int_56]) else ('m'))))
			});
			return ;
		}
		print "v_int_57", " ", v_int_57, " ", "v_int_58", " ", v_int_58, " ", "v_int_7", " ", v_int_7, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, "\n";
		return ;
	}
	assert true;
	expect true;
	var v_seq_31: seq<bool> := [];
	var v_int_61: int := 3;
	var v_seq_32: seq<bool> := [false, false, true, false];
	var v_int_62: int := -16;
	var v_map_20: map<char, seq<char>> := map['N' := ['p', 'Q', 'B', 'P'], 'C' := [], 't' := ['b'], 'D' := ['r']];
	var v_char_28: char := 'O';
	var v_seq_33: seq<char> := (if ((v_char_28 in v_map_20)) then (v_map_20[v_char_28]) else (['P']));
	var v_int_63: int := v_int_62;
	var v_map_21: map<char, char> := map['n' := 'v', 'a' := 'c', 'W' := 'v', 'O' := 'I', 's' := 'p'];
	var v_char_29: char := 'h';
	var v_map_22: map<char, char> := (match 'b' {
		case _ => map['f' := 'i', 'x' := 'H', 'B' := 'r', 'k' := 'V']
	});
	var v_char_30: char := (match 'A' {
		case _ => 'S'
	});
	match (if ((if ((if (true) then (false) else (false))) then ((if ((|v_seq_31| > 0)) then (v_seq_31[v_int_61]) else (false))) else ((if ((|v_seq_32| > 0)) then (v_seq_32[v_int_62]) else (false))))) then ((if ((|v_seq_33| > 0)) then (v_seq_33[v_int_63]) else ((if ((v_char_29 in v_map_21)) then (v_map_21[v_char_29]) else ('P'))))) else ((if ((v_char_30 in v_map_22)) then (v_map_22[v_char_30]) else (v_char_29)))) {
		case _ => {
			return ;
		}
		
	}
	
	var v_seq_35: seq<set<char>> := [{'F', 'q', 'P', 'A'}, {}, {'V', 'g', 's'}];
	var v_int_71: int := 20;
	var v_map_37: map<char, bool> := ((map['D' := false, 'd' := true] - {'g', 'D', 'Z', 'P'}) - (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_71]) else ({'q', 'e', 'C'})));
	var v_char_45: char := v_char_28;
	var v_map_36: map<char, bool> := map['m' := true, 't' := true, 'Z' := true]['C' := true];
	var v_char_44: char := v_char_28;
	var v_map_35: map<char, bool> := map['h' := true, 'z' := false];
	var v_char_43: char := 'd';
	if (if ((v_char_45 in v_map_37)) then (v_map_37[v_char_45]) else ((if ((v_char_44 in v_map_36)) then (v_map_36[v_char_44]) else ((if ((v_char_43 in v_map_35)) then (v_map_35[v_char_43]) else (false)))))) {
		return ;
	} else {
		return ;
	}
}
