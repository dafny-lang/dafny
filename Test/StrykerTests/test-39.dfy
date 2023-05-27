// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1
datatype DT_2<T_1, T_2> = DT_2_1 | DT_2_2(DT_2_2_1: T_2, DT_2_2_2: T_2, DT_2_2_3: T_1)
datatype DT_3<T_3> = DT_3_1 | DT_3_3(DT_3_3_1: T_3, DT_3_3_2: T_3, DT_3_3_3: T_3, DT_3_3_4: T_3)
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

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: bool, p_m_method_3_3: seq<real>, p_m_method_3_4: char) returns (ret_1: seq<seq<DT_2<map<int, bool>, int>>>)
	requires ((p_m_method_3_1 == 28) && |p_m_method_3_3| == 2 && (-15.31 < p_m_method_3_3[0] < -15.11) && (28.06 < p_m_method_3_3[1] < 28.26) && (p_m_method_3_2 == false) && (p_m_method_3_4 == 'H'));
	ensures (((p_m_method_3_1 == 28) && |p_m_method_3_3| == 2 && (-15.31 < p_m_method_3_3[0] < -15.11) && (28.06 < p_m_method_3_3[1] < 28.26) && (p_m_method_3_2 == false) && (p_m_method_3_4 == 'H')) ==> (|ret_1| == 2 && |ret_1[0]| == 1 && (ret_1[0][0].DT_2_2? && ((ret_1[0][0].DT_2_2_1 == 1) && (ret_1[0][0].DT_2_2_2 == 26) && (ret_1[0][0].DT_2_2_3 == map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]))) && |ret_1[1]| == 0));
{
	var v_array_1: array<char> := new char[3] ['H', 'O', 'P'];
	var v_DT_2_2_1: DT_2<map<int, bool>, int> := DT_2_2(14, 28, map[19 := false]);
	var v_array_2: array<char>, v_DT_2_2_2: DT_2<map<int, bool>, int>, v_seq_5: seq<seq<int>> := v_array_1, v_DT_2_2_1, [[28, 14, 8, 0], [25, 23], [], []];
	if false {
		
	} else {
		
	}
	var v_DT_2_2_3: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[28 := true, 9 := false, 27 := true, 1 := false, 3 := false]);
	var v_DT_2_2_18: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	var v_DT_2_2_19: DT_2<map<int, bool>, int> := DT_2_2(14, 28, map[19 := false]);
	var v_DT_2_2_20: DT_2<map<int, bool>, int> := DT_2_2(14, 28, map[19 := false]);
	print "v_DT_2_2_3.DT_2_2_3", " ", (v_DT_2_2_3.DT_2_2_3 == map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]), " ", "v_DT_2_2_3.DT_2_2_2", " ", v_DT_2_2_3.DT_2_2_2, " ", "v_DT_2_2_3.DT_2_2_1", " ", v_DT_2_2_3.DT_2_2_1, " ", "v_DT_2_2_3", " ", (v_DT_2_2_3 == v_DT_2_2_18), " ", "v_DT_2_2_1.DT_2_2_1", " ", v_DT_2_2_1.DT_2_2_1, " ", "v_DT_2_2_2", " ", (v_DT_2_2_2 == v_DT_2_2_19), " ", "v_DT_2_2_1", " ", (v_DT_2_2_1 == v_DT_2_2_20), " ", "v_DT_2_2_1.DT_2_2_2", " ", v_DT_2_2_1.DT_2_2_2, " ", "v_DT_2_2_1.DT_2_2_3", " ", (v_DT_2_2_1.DT_2_2_3 == map[19 := false]), " ", "v_seq_5", " ", v_seq_5, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[1]", " ", (v_array_1[1] == 'O'), " ", "v_array_1[2]", " ", (v_array_1[2] == 'P'), " ", "v_array_1[0]", " ", (v_array_1[0] == 'H'), " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 'H'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == [-15.21, 28.16]), "\n";
	return [[v_DT_2_2_3], []];
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

method m_method_2(p_m_method_2_1: int) returns (ret_1: int)
	requires ((p_m_method_2_1 == 10));
	ensures (((p_m_method_2_1 == 10)) ==> ((ret_1 == 23)));
{
	var v_real_1: real, v_multiset_1: multiset<bool> := 20.30, multiset{true, false, false};
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_real_1", " ", (v_real_1 == 20.30), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{false, false, true}), "\n";
	return 23;
}

method m_method_1(p_m_method_1_1: int) returns (ret_1: char)
	requires ((p_m_method_1_1 == -234));
	ensures (((p_m_method_1_1 == -234)) ==> ((ret_1 == 'D')));
{
	var v_seq_3: seq<map<int, char>> := [map[1 := 'L', 13 := 'l', 14 := 'U'], map[16 := 'o', 20 := 'v', -20 := 'N', 6 := 'M']];
	var v_int_7: int := 26;
	var v_seq_11: seq<map<int, char>> := v_seq_3;
	var v_int_16: int := v_int_7;
	var v_int_17: int := safe_index_seq(v_seq_11, v_int_16);
	v_int_7 := v_int_17;
	var v_map_1: map<int, char> := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (map[23 := 'b', 10 := 't']));
	var v_int_8: int := (if (true) then (23) else (-22));
	print "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_seq_3", " ", (v_seq_3 == [map[1 := 'L', 13 := 'l', 14 := 'U'], map[16 := 'o', -20 := 'N', 20 := 'v', 6 := 'M']]), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[1 := 'L', 13 := 'l', 14 := 'U']), "\n";
	return (if ((v_int_8 in v_map_1)) then (v_map_1[v_int_8]) else ((if (false) then ('y') else ('D'))));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_int_9: int := 10;
	var v_int_10: int := m_method_2(v_int_9);
	var v_int_11: int := (match true {
		case false => v_int_10
		case true => (-26 * 9)
		case _ => (9 - 24)
	});
	var v_char_1: char := m_method_1(v_int_11);
	var v_map_2: map<seq<char>, multiset<char>> := map[['G', 'j', 'F', 'a'] := multiset({'e', 'g'}), ['S', 'g'] := multiset({'L'})];
	var v_seq_4: seq<char> := ['P', 'U', 'J'];
	var v_int_12: int := 28;
	var v_bool_1: bool := false;
	var v_seq_6: seq<real> := [-15.21, 28.16];
	var v_char_2: char := 'H';
	var v_seq_7: seq<seq<DT_2<map<int, bool>, int>>> := m_method_3(v_int_12, v_bool_1, v_seq_6, v_char_2);
	var v_seq_8: seq<seq<DT_2<map<int, bool>, int>>> := v_seq_7;
	var v_int_13: int := (if (true) then (15) else (19));
	var v_seq_12: seq<seq<DT_2<map<int, bool>, int>>> := v_seq_8;
	var v_int_18: int := v_int_13;
	var v_int_19: int := safe_index_seq(v_seq_12, v_int_18);
	v_int_13 := v_int_19;
	var v_DT_2_2_4: DT_2<map<int, bool>, int> := DT_2_2(3, 1, map[23 := true, 2 := true]);
	var v_DT_2_2_5: DT_2<map<int, bool>, int> := DT_2_2(-9, 3, map[21 := false, 17 := false, 8 := true, 10 := false]);
	var v_DT_2_2_6: DT_2<map<int, bool>, int> := DT_2_2(-7, 29, map[11 := false]);
	var v_DT_2_2_7: DT_2<map<int, bool>, int> := DT_2_2(1, 6, map[28 := true, 27 := false, 10 := false]);
	var v_DT_2_2_8: DT_2<map<int, bool>, int> := DT_2_2(-20, 4, map[12 := false, 18 := false, 9 := false, 20 := false, 29 := true]);
	var v_DT_2_2_9: DT_2<map<int, bool>, int> := DT_2_2(29, 28, map[11 := false, 28 := true]);
	var v_DT_2_2_10: DT_2<map<int, bool>, int> := DT_2_2(4, 1, map[22 := false]);
	var v_seq_9: seq<DT_2<map<int, bool>, int>> := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_13]) else ((match 'h' {
		case _ => [v_DT_2_2_7, v_DT_2_2_8, v_DT_2_2_9, v_DT_2_2_10]
	})));
	var v_int_14: int := (match 'N' {
		case 'O' => (3 / 10)
		case _ => v_int_12
	});
	var v_seq_13: seq<DT_2<map<int, bool>, int>> := v_seq_9;
	var v_int_20: int := v_int_14;
	var v_int_21: int := safe_index_seq(v_seq_13, v_int_20);
	v_int_14 := v_int_21;
	var v_seq_10: seq<DT_2<map<int, bool>, int>> := v_seq_9;
	var v_int_15: int := (-15.77).Floor;
	var v_real_bool_bool_1: (real, bool, bool) := (-8.53, true, false);
	var v_real_real_real_1: (real, real, real) := (-2.75, 27.92, -24.95);
	var v_DT_3_3_1: DT_3<real> := DT_3_3(20.56, 5.71, 28.08, -15.40);
	var v_real_bool_bool_real_real_real_DT_3_3_1: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_1, v_real_real_real_1, v_DT_3_3_1);
	var v_DT_2_2_11: DT_2<map<int, bool>, int> := DT_2_2(23, 12, map[29 := false, 23 := true, 22 := true]);
	var v_real_bool_bool_2: (real, bool, bool) := (-16.70, true, false);
	var v_real_real_real_2: (real, real, real) := (-17.51, 23.00, -5.24);
	var v_DT_3_3_2: DT_3<real> := DT_3_3(21.47, -16.74, 14.44, -9.73);
	var v_real_bool_bool_real_real_real_DT_3_3_2: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_2, v_real_real_real_2, v_DT_3_3_2);
	var v_DT_2_2_12: DT_2<map<int, bool>, int> := DT_2_2(23, 28, map[7 := true, 23 := false, 28 := false, 3 := false]);
	var v_real_bool_bool_3: (real, bool, bool) := (21.99, true, true);
	var v_real_real_real_3: (real, real, real) := (-14.81, 14.29, -20.36);
	var v_DT_3_3_3: DT_3<real> := DT_3_3(-21.08, 22.22, 21.60, 6.67);
	var v_real_bool_bool_real_real_real_DT_3_3_3: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_3, v_real_real_real_3, v_DT_3_3_3);
	var v_DT_2_2_13: DT_2<map<int, bool>, int> := DT_2_2(19, 27, map[-23 := false, -28 := false]);
	var v_real_bool_bool_4: (real, bool, bool) := (26.64, true, true);
	var v_real_real_real_4: (real, real, real) := (-9.90, 21.68, -15.50);
	var v_DT_3_3_4: DT_3<real> := DT_3_3(-13.53, 7.13, 19.71, -25.85);
	var v_real_bool_bool_real_real_real_DT_3_3_4: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_4, v_real_real_real_4, v_DT_3_3_4);
	var v_DT_2_2_14: DT_2<map<int, bool>, int> := DT_2_2(5, -5, map[24 := false]);
	var v_real_bool_bool_5: (real, bool, bool) := (5.45, false, true);
	var v_real_real_real_5: (real, real, real) := (13.67, 0.55, -0.95);
	var v_DT_3_3_5: DT_3<real> := DT_3_3(-28.87, 6.89, -18.83, 14.34);
	var v_real_bool_bool_real_real_real_DT_3_3_5: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_5, v_real_real_real_5, v_DT_3_3_5);
	var v_DT_2_2_15: DT_2<map<int, bool>, int> := DT_2_2(19, 8, map[3 := true, 19 := false, 29 := false]);
	var v_map_3: map<((real, bool, bool), (real, real, real), DT_3<real>), DT_2<map<int, bool>, int>> := map[v_real_bool_bool_real_real_real_DT_3_3_1 := v_DT_2_2_11, v_real_bool_bool_real_real_real_DT_3_3_2 := v_DT_2_2_12, v_real_bool_bool_real_real_real_DT_3_3_3 := v_DT_2_2_13, v_real_bool_bool_real_real_real_DT_3_3_4 := v_DT_2_2_14, v_real_bool_bool_real_real_real_DT_3_3_5 := v_DT_2_2_15];
	var v_real_bool_bool_6: (real, bool, bool) := (21.18, true, true);
	var v_real_real_real_6: (real, real, real) := (-4.32, -4.08, 24.40);
	var v_DT_3_3_6: DT_3<real> := DT_3_3(-23.07, 7.86, -9.81, -15.48);
	var v_real_bool_bool_real_real_real_DT_3_3_6: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_6, v_real_real_real_6, v_DT_3_3_6);
	var v_real_bool_bool_real_real_real_DT_3_3_7: ((real, bool, bool), (real, real, real), DT_3<real>) := v_real_bool_bool_real_real_real_DT_3_3_6;
	var v_DT_2_2_16: DT_2<map<int, bool>, int> := DT_2_2(17, 21, map[-16 := true, -20 := false, -29 := false, 19 := true]);
	var v_DT_1_1_2: DT_1, v_bool_2: bool, v_char_3: char, v_bool_3: bool, v_DT_2_2_17: DT_2<map<int, bool>, int> := v_DT_1_1_1, true, v_char_1, (v_char_1 in ((multiset{'l'} + multiset{'o', 'H'}) * (if ((v_seq_4 in v_map_2)) then (v_map_2[v_seq_4]) else (multiset({'c', 'k', 't'}))))), (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_14]) else ((if ((|v_seq_10| > 0)) then (v_seq_10[v_int_15]) else ((if ((v_real_bool_bool_real_real_real_DT_3_3_7 in v_map_3)) then (v_map_3[v_real_bool_bool_real_real_real_DT_3_3_7]) else (v_DT_2_2_16))))));
	var v_real_bool_bool_7: (real, bool, bool) := (26.64, true, true);
	var v_real_bool_bool_8: (real, bool, bool) := (21.18, true, true);
	var v_real_real_real_7: (real, real, real) := (-4.32, -4.08, 24.40);
	var v_DT_3_3_7: DT_3<real> := DT_3_3(-23.07, 7.86, -9.81, -15.48);
	var v_real_bool_bool_real_real_real_DT_3_3_8: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_8, v_real_real_real_7, v_DT_3_3_7);
	var v_real_real_real_8: (real, real, real) := (-9.90, 21.68, -15.50);
	var v_real_bool_bool_9: (real, bool, bool) := (21.18, true, true);
	var v_real_real_real_9: (real, real, real) := (-4.32, -4.08, 24.40);
	var v_DT_3_3_8: DT_3<real> := DT_3_3(-23.07, 7.86, -9.81, -15.48);
	var v_real_bool_bool_real_real_real_DT_3_3_9: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_9, v_real_real_real_9, v_DT_3_3_8);
	var v_DT_3_3_9: DT_3<real> := DT_3_3(-13.53, 7.13, 19.71, -25.85);
	var v_real_bool_bool_10: (real, bool, bool) := (-8.53, true, false);
	var v_real_real_real_10: (real, real, real) := (-2.75, 27.92, -24.95);
	var v_DT_3_3_10: DT_3<real> := DT_3_3(20.56, 5.71, 28.08, -15.40);
	var v_real_bool_bool_real_real_real_DT_3_3_10: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_10, v_real_real_real_10, v_DT_3_3_10);
	var v_real_bool_bool_11: (real, bool, bool) := (21.99, true, true);
	var v_real_real_real_11: (real, real, real) := (-14.81, 14.29, -20.36);
	var v_DT_3_3_11: DT_3<real> := DT_3_3(-21.08, 22.22, 21.60, 6.67);
	var v_real_bool_bool_real_real_real_DT_3_3_11: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_11, v_real_real_real_11, v_DT_3_3_11);
	var v_real_bool_bool_12: (real, bool, bool) := (-16.70, true, false);
	var v_real_real_real_12: (real, real, real) := (-17.51, 23.00, -5.24);
	var v_DT_3_3_12: DT_3<real> := DT_3_3(21.47, -16.74, 14.44, -9.73);
	var v_real_bool_bool_real_real_real_DT_3_3_12: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_12, v_real_real_real_12, v_DT_3_3_12);
	var v_real_bool_bool_13: (real, bool, bool) := (5.45, false, true);
	var v_real_real_real_13: (real, real, real) := (13.67, 0.55, -0.95);
	var v_DT_3_3_13: DT_3<real> := DT_3_3(-28.87, 6.89, -18.83, 14.34);
	var v_real_bool_bool_real_real_real_DT_3_3_13: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_13, v_real_real_real_13, v_DT_3_3_13);
	var v_real_bool_bool_14: (real, bool, bool) := (26.64, true, true);
	var v_real_real_real_14: (real, real, real) := (-9.90, 21.68, -15.50);
	var v_DT_3_3_14: DT_3<real> := DT_3_3(-13.53, 7.13, 19.71, -25.85);
	var v_real_bool_bool_real_real_real_DT_3_3_14: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_14, v_real_real_real_14, v_DT_3_3_14);
	var v_real_real_real_15: (real, real, real) := (-14.81, 14.29, -20.36);
	var v_DT_3_3_15: DT_3<real> := DT_3_3(-21.08, 22.22, 21.60, 6.67);
	var v_real_bool_bool_15: (real, bool, bool) := (21.99, true, true);
	var v_real_real_real_16: (real, real, real) := (13.67, 0.55, -0.95);
	var v_real_real_real_17: (real, real, real) := (-9.90, 21.68, -15.50);
	var v_real_real_real_18: (real, real, real) := (-4.32, -4.08, 24.40);
	var v_real_real_real_19: (real, real, real) := (-2.75, 27.92, -24.95);
	var v_real_real_real_20: (real, real, real) := (-14.81, 14.29, -20.36);
	var v_real_real_real_21: (real, real, real) := (-17.51, 23.00, -5.24);
	var v_real_bool_bool_16: (real, bool, bool) := (5.45, false, true);
	var v_real_real_real_22: (real, real, real) := (13.67, 0.55, -0.95);
	var v_DT_3_3_16: DT_3<real> := DT_3_3(-28.87, 6.89, -18.83, 14.34);
	var v_real_bool_bool_real_real_real_DT_3_3_15: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_16, v_real_real_real_22, v_DT_3_3_16);
	var v_DT_2_2_21: DT_2<map<int, bool>, int> := DT_2_2(19, 8, map[3 := true, 19 := false, 29 := false]);
	var v_real_bool_bool_17: (real, bool, bool) := (21.99, true, true);
	var v_real_real_real_23: (real, real, real) := (-14.81, 14.29, -20.36);
	var v_DT_3_3_17: DT_3<real> := DT_3_3(-21.08, 22.22, 21.60, 6.67);
	var v_real_bool_bool_real_real_real_DT_3_3_16: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_17, v_real_real_real_23, v_DT_3_3_17);
	var v_DT_2_2_22: DT_2<map<int, bool>, int> := DT_2_2(19, 27, map[-23 := false, -28 := false]);
	var v_real_bool_bool_18: (real, bool, bool) := (-16.70, true, false);
	var v_real_real_real_24: (real, real, real) := (-17.51, 23.00, -5.24);
	var v_DT_3_3_18: DT_3<real> := DT_3_3(21.47, -16.74, 14.44, -9.73);
	var v_real_bool_bool_real_real_real_DT_3_3_17: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_18, v_real_real_real_24, v_DT_3_3_18);
	var v_DT_2_2_23: DT_2<map<int, bool>, int> := DT_2_2(23, 28, map[3 := false, 7 := true, 23 := false, 28 := false]);
	var v_real_bool_bool_19: (real, bool, bool) := (-8.53, true, false);
	var v_real_real_real_25: (real, real, real) := (-2.75, 27.92, -24.95);
	var v_DT_3_3_19: DT_3<real> := DT_3_3(20.56, 5.71, 28.08, -15.40);
	var v_real_bool_bool_real_real_real_DT_3_3_18: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_19, v_real_real_real_25, v_DT_3_3_19);
	var v_DT_2_2_24: DT_2<map<int, bool>, int> := DT_2_2(23, 12, map[22 := true, 23 := true, 29 := false]);
	var v_real_bool_bool_20: (real, bool, bool) := (26.64, true, true);
	var v_real_real_real_26: (real, real, real) := (-9.90, 21.68, -15.50);
	var v_DT_3_3_20: DT_3<real> := DT_3_3(-13.53, 7.13, 19.71, -25.85);
	var v_real_bool_bool_real_real_real_DT_3_3_19: ((real, bool, bool), (real, real, real), DT_3<real>) := (v_real_bool_bool_20, v_real_real_real_26, v_DT_3_3_20);
	var v_DT_2_2_25: DT_2<map<int, bool>, int> := DT_2_2(5, -5, map[24 := false]);
	var v_DT_3_3_21: DT_3<real> := DT_3_3(21.47, -16.74, 14.44, -9.73);
	var v_real_bool_bool_21: (real, bool, bool) := (21.18, true, true);
	var v_real_real_real_27: (real, real, real) := (-4.32, -4.08, 24.40);
	var v_DT_3_3_22: DT_3<real> := DT_3_3(-23.07, 7.86, -9.81, -15.48);
	var v_real_bool_bool_22: (real, bool, bool) := (26.64, true, true);
	var v_real_bool_bool_23: (real, bool, bool) := (5.45, false, true);
	var v_real_bool_bool_24: (real, bool, bool) := (21.18, true, true);
	var v_real_bool_bool_25: (real, bool, bool) := (-8.53, true, false);
	var v_real_bool_bool_26: (real, bool, bool) := (-16.70, true, false);
	var v_real_bool_bool_27: (real, bool, bool) := (-16.70, true, false);
	var v_real_real_real_28: (real, real, real) := (-17.51, 23.00, -5.24);
	var v_real_bool_bool_28: (real, bool, bool) := (21.99, true, true);
	var v_DT_2_2_26: DT_2<map<int, bool>, int> := DT_2_2(23, 12, map[22 := true, 23 := true, 29 := false]);
	var v_DT_2_2_27: DT_2<map<int, bool>, int> := DT_2_2(23, 28, map[3 := false, 7 := true, 23 := false, 28 := false]);
	var v_DT_2_2_28: DT_2<map<int, bool>, int> := DT_2_2(19, 27, map[-23 := false, -28 := false]);
	var v_DT_2_2_29: DT_2<map<int, bool>, int> := DT_2_2(5, -5, map[24 := false]);
	var v_DT_2_2_30: DT_2<map<int, bool>, int> := DT_2_2(19, 8, map[3 := true, 19 := false, 29 := false]);
	var v_DT_2_2_31: DT_2<map<int, bool>, int> := DT_2_2(17, 21, map[-20 := false, 19 := true, -29 := false, -16 := true]);
	var v_DT_2_2_32: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	var v_real_bool_bool_29: (real, bool, bool) := (5.45, false, true);
	var v_real_real_real_29: (real, real, real) := (13.67, 0.55, -0.95);
	var v_DT_3_3_23: DT_3<real> := DT_3_3(-28.87, 6.89, -18.83, 14.34);
	var v_real_bool_bool_30: (real, bool, bool) := (-8.53, true, false);
	var v_real_real_real_30: (real, real, real) := (-2.75, 27.92, -24.95);
	var v_DT_3_3_24: DT_3<real> := DT_3_3(20.56, 5.71, 28.08, -15.40);
	var v_DT_2_2_33: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	var v_DT_3_3_25: DT_3<real> := DT_3_3(20.56, 5.71, 28.08, -15.40);
	var v_DT_3_3_26: DT_3<real> := DT_3_3(-21.08, 22.22, 21.60, 6.67);
	var v_DT_3_3_27: DT_3<real> := DT_3_3(21.47, -16.74, 14.44, -9.73);
	var v_DT_3_3_28: DT_3<real> := DT_3_3(-28.87, 6.89, -18.83, 14.34);
	var v_DT_3_3_29: DT_3<real> := DT_3_3(-13.53, 7.13, 19.71, -25.85);
	var v_DT_3_3_30: DT_3<real> := DT_3_3(-23.07, 7.86, -9.81, -15.48);
	var v_DT_2_2_34: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	var v_DT_2_2_35: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	var v_DT_2_2_36: DT_2<map<int, bool>, int> := DT_2_2(1, 26, map[1 := false, 3 := false, 9 := false, 27 := true, 28 := true]);
	print "v_real_bool_bool_real_real_real_DT_3_3_4.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_4.0 == v_real_bool_bool_7), " ", "v_real_bool_bool_real_real_real_DT_3_3_7", " ", (v_real_bool_bool_real_real_real_DT_3_3_7 == v_real_bool_bool_real_real_real_DT_3_3_8), " ", "v_real_bool_bool_real_real_real_DT_3_3_4.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_4.1 == v_real_real_real_8), " ", "v_real_bool_bool_real_real_real_DT_3_3_6", " ", (v_real_bool_bool_real_real_real_DT_3_3_6 == v_real_bool_bool_real_real_real_DT_3_3_9), " ", "v_real_bool_bool_real_real_real_DT_3_3_4.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_4.2 == v_DT_3_3_9), " ", "v_real_bool_bool_real_real_real_DT_3_3_1", " ", (v_real_bool_bool_real_real_real_DT_3_3_1 == v_real_bool_bool_real_real_real_DT_3_3_10), " ", "v_real_bool_bool_real_real_real_DT_3_3_3", " ", (v_real_bool_bool_real_real_real_DT_3_3_3 == v_real_bool_bool_real_real_real_DT_3_3_11), " ", "v_real_bool_bool_real_real_real_DT_3_3_2", " ", (v_real_bool_bool_real_real_real_DT_3_3_2 == v_real_bool_bool_real_real_real_DT_3_3_12), " ", "v_real_bool_bool_real_real_real_DT_3_3_5", " ", (v_real_bool_bool_real_real_real_DT_3_3_5 == v_real_bool_bool_real_real_real_DT_3_3_13), " ", "v_real_bool_bool_real_real_real_DT_3_3_4", " ", (v_real_bool_bool_real_real_real_DT_3_3_4 == v_real_bool_bool_real_real_real_DT_3_3_14), " ", "v_DT_3_3_1.DT_3_3_2", " ", (v_DT_3_3_1.DT_3_3_2 == 5.71), " ", "v_DT_3_3_1.DT_3_3_3", " ", (v_DT_3_3_1.DT_3_3_3 == 28.08), " ", "v_DT_3_3_1.DT_3_3_1", " ", (v_DT_3_3_1.DT_3_3_1 == 20.56), " ", "v_DT_3_3_1.DT_3_3_4", " ", (v_DT_3_3_1.DT_3_3_4 == -15.40), " ", "v_real_bool_bool_5.1", " ", v_real_bool_bool_5.1, " ", "v_DT_2_2_15.DT_2_2_1", " ", v_DT_2_2_15.DT_2_2_1, " ", "v_real_bool_bool_5.2", " ", v_real_bool_bool_5.2, " ", "v_DT_2_2_15.DT_2_2_2", " ", v_DT_2_2_15.DT_2_2_2, " ", "v_DT_2_2_15.DT_2_2_3", " ", (v_DT_2_2_15.DT_2_2_3 == map[3 := true, 19 := false, 29 := false]), " ", "v_real_bool_bool_1.0", " ", (v_real_bool_bool_1.0 == -8.53), " ", "v_real_bool_bool_5.0", " ", (v_real_bool_bool_5.0 == 5.45), " ", "v_real_bool_bool_1.1", " ", v_real_bool_bool_1.1, " ", "v_real_bool_bool_1.2", " ", v_real_bool_bool_1.2, " ", "v_real_real_real_3.0", " ", (v_real_real_real_3.0 == -14.81), " ", "v_real_real_real_3.2", " ", (v_real_real_real_3.2 == -20.36), " ", "v_real_real_real_3.1", " ", (v_real_real_real_3.1 == 14.29), " ", "v_DT_3_3_2.DT_3_3_4", " ", (v_DT_3_3_2.DT_3_3_4 == -9.73), " ", "v_DT_3_3_2.DT_3_3_3", " ", (v_DT_3_3_2.DT_3_3_3 == 14.44), " ", "v_DT_3_3_2.DT_3_3_2", " ", (v_DT_3_3_2.DT_3_3_2 == -16.74), " ", "v_DT_3_3_2.DT_3_3_1", " ", (v_DT_3_3_2.DT_3_3_1 == 21.47), " ", "v_real_bool_bool_real_real_real_DT_3_3_3.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_3.1 == v_real_real_real_15), " ", "v_real_bool_bool_real_real_real_DT_3_3_3.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_3.2 == v_DT_3_3_15), " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_real_real_real_6.1", " ", (v_real_real_real_6.1 == -4.08), " ", "v_real_real_real_6.0", " ", (v_real_real_real_6.0 == -4.32), " ", "v_real_real_real_6.2", " ", (v_real_real_real_6.2 == 24.40), " ", "v_real_bool_bool_real_real_real_DT_3_3_3.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_3.0 == v_real_bool_bool_15), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_real_bool_bool_4.2", " ", v_real_bool_bool_4.2, " ", "v_char_1", " ", (v_char_1 == 'D'), " ", "v_real_real_real_5", " ", (v_real_real_real_5 == v_real_real_real_16), " ", "v_real_real_real_4", " ", (v_real_real_real_4 == v_real_real_real_17), " ", "v_char_3", " ", (v_char_3 == 'D'), " ", "v_char_2", " ", (v_char_2 == 'H'), " ", "v_real_real_real_6", " ", (v_real_real_real_6 == v_real_real_real_18), " ", "v_real_real_real_1", " ", (v_real_real_real_1 == v_real_real_real_19), " ", "v_real_bool_bool_4.0", " ", (v_real_bool_bool_4.0 == 26.64), " ", "v_real_bool_bool_4.1", " ", v_real_bool_bool_4.1, " ", "v_real_real_real_3", " ", (v_real_real_real_3 == v_real_real_real_20), " ", "v_real_real_real_2", " ", (v_real_real_real_2 == v_real_real_real_21), " ", "v_map_3", " ", (v_map_3 == map[v_real_bool_bool_real_real_real_DT_3_3_15 := v_DT_2_2_21, v_real_bool_bool_real_real_real_DT_3_3_16 := v_DT_2_2_22, v_real_bool_bool_real_real_real_DT_3_3_17 := v_DT_2_2_23, v_real_bool_bool_real_real_real_DT_3_3_18 := v_DT_2_2_24, v_real_bool_bool_real_real_real_DT_3_3_19 := v_DT_2_2_25]), " ", "v_map_2", " ", (v_map_2 == map[['G', 'j', 'F', 'a'] := multiset{'e', 'g'}, ['S', 'g'] := multiset{'L'}]), " ", "v_DT_3_3_5.DT_3_3_4", " ", (v_DT_3_3_5.DT_3_3_4 == 14.34), " ", "v_real_real_real_2.1", " ", (v_real_real_real_2.1 == 23.00), " ", "v_DT_3_3_5.DT_3_3_3", " ", (v_DT_3_3_5.DT_3_3_3 == -18.83), " ", "v_real_real_real_2.0", " ", (v_real_real_real_2.0 == -17.51), " ", "v_DT_3_3_5.DT_3_3_2", " ", (v_DT_3_3_5.DT_3_3_2 == 6.89), " ", "v_DT_3_3_5.DT_3_3_1", " ", (v_DT_3_3_5.DT_3_3_1 == -28.87), " ", "v_real_real_real_2.2", " ", (v_real_real_real_2.2 == -5.24), " ", "v_real_bool_bool_real_real_real_DT_3_3_2.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_2.2 == v_DT_3_3_21), " ", "v_real_bool_bool_real_real_real_DT_3_3_6.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_6.0 == v_real_bool_bool_21), " ", "v_real_bool_bool_real_real_real_DT_3_3_6.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_6.1 == v_real_real_real_27), " ", "v_real_bool_bool_real_real_real_DT_3_3_6.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_6.2 == v_DT_3_3_22), " ", "v_real_bool_bool_4", " ", (v_real_bool_bool_4 == v_real_bool_bool_22), " ", "v_real_real_real_5.2", " ", (v_real_real_real_5.2 == -0.95), " ", "v_real_bool_bool_5", " ", (v_real_bool_bool_5 == v_real_bool_bool_23), " ", "v_real_real_real_5.1", " ", (v_real_real_real_5.1 == 0.55), " ", "v_DT_3_3_4.DT_3_3_3", " ", (v_DT_3_3_4.DT_3_3_3 == 19.71), " ", "v_real_bool_bool_6", " ", (v_real_bool_bool_6 == v_real_bool_bool_24), " ", "v_DT_3_3_4.DT_3_3_4", " ", (v_DT_3_3_4.DT_3_3_4 == -25.85), " ", "v_DT_3_3_4.DT_3_3_1", " ", (v_DT_3_3_4.DT_3_3_1 == -13.53), " ", "v_real_bool_bool_1", " ", (v_real_bool_bool_1 == v_real_bool_bool_25), " ", "v_DT_3_3_4.DT_3_3_2", " ", (v_DT_3_3_4.DT_3_3_2 == 7.13), " ", "v_real_bool_bool_2", " ", (v_real_bool_bool_2 == v_real_bool_bool_26), " ", "v_real_bool_bool_real_real_real_DT_3_3_2.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_2.0 == v_real_bool_bool_27), " ", "v_real_bool_bool_real_real_real_DT_3_3_2.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_2.1 == v_real_real_real_28), " ", "v_real_bool_bool_3", " ", (v_real_bool_bool_3 == v_real_bool_bool_28), " ", "v_DT_2_2_11", " ", (v_DT_2_2_11 == v_DT_2_2_26), " ", "v_DT_2_2_12", " ", (v_DT_2_2_12 == v_DT_2_2_27), " ", "v_DT_2_2_13", " ", (v_DT_2_2_13 == v_DT_2_2_28), " ", "v_DT_2_2_14", " ", (v_DT_2_2_14 == v_DT_2_2_29), " ", "v_DT_2_2_15", " ", (v_DT_2_2_15 == v_DT_2_2_30), " ", "v_DT_2_2_16", " ", (v_DT_2_2_16 == v_DT_2_2_31), " ", "v_DT_2_2_17", " ", (v_DT_2_2_17 == v_DT_2_2_32), " ", "v_DT_2_2_12.DT_2_2_1", " ", v_DT_2_2_12.DT_2_2_1, " ", "v_DT_2_2_12.DT_2_2_2", " ", v_DT_2_2_12.DT_2_2_2, " ", "v_DT_2_2_12.DT_2_2_3", " ", (v_DT_2_2_12.DT_2_2_3 == map[3 := false, 7 := true, 23 := false, 28 := false]), " ", "v_DT_3_3_3.DT_3_3_2", " ", (v_DT_3_3_3.DT_3_3_2 == 22.22), " ", "v_DT_2_2_13.DT_2_2_2", " ", v_DT_2_2_13.DT_2_2_2, " ", "v_DT_3_3_3.DT_3_3_3", " ", (v_DT_3_3_3.DT_3_3_3 == 21.60), " ", "v_DT_2_2_13.DT_2_2_1", " ", v_DT_2_2_13.DT_2_2_1, " ", "v_DT_3_3_3.DT_3_3_4", " ", (v_DT_3_3_3.DT_3_3_4 == 6.67), " ", "v_DT_2_2_13.DT_2_2_3", " ", (v_DT_2_2_13.DT_2_2_3 == map[-23 := false, -28 := false]), " ", "v_real_bool_bool_3.1", " ", v_real_bool_bool_3.1, " ", "v_real_bool_bool_3.2", " ", v_real_bool_bool_3.2, " ", "v_real_bool_bool_3.0", " ", (v_real_bool_bool_3.0 == 21.99), " ", "v_DT_3_3_3.DT_3_3_1", " ", (v_DT_3_3_3.DT_3_3_1 == -21.08), " ", "v_real_real_real_1.0", " ", (v_real_real_real_1.0 == -2.75), " ", "v_real_real_real_1.2", " ", (v_real_real_real_1.2 == -24.95), " ", "v_real_real_real_1.1", " ", (v_real_real_real_1.1 == 27.92), " ", "v_real_real_real_5.0", " ", (v_real_real_real_5.0 == 13.67), " ", "v_bool_1", " ", v_bool_1, " ", "v_real_bool_bool_real_real_real_DT_3_3_5.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_5.0 == v_real_bool_bool_29), " ", "v_real_bool_bool_real_real_real_DT_3_3_5.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_5.1 == v_real_real_real_29), " ", "v_bool_3", " ", v_bool_3, " ", "v_real_bool_bool_real_real_real_DT_3_3_5.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_5.2 == v_DT_3_3_23), " ", "v_bool_2", " ", v_bool_2, " ", "v_real_real_real_4.2", " ", (v_real_real_real_4.2 == -15.50), " ", "v_DT_2_2_14.DT_2_2_2", " ", v_DT_2_2_14.DT_2_2_2, " ", "v_DT_2_2_14.DT_2_2_3", " ", (v_DT_2_2_14.DT_2_2_3 == map[24 := false]), " ", "v_real_bool_bool_real_real_real_DT_3_3_1.0", " ", (v_real_bool_bool_real_real_real_DT_3_3_1.0 == v_real_bool_bool_30), " ", "v_DT_2_2_14.DT_2_2_1", " ", v_DT_2_2_14.DT_2_2_1, " ", "v_real_bool_bool_real_real_real_DT_3_3_1.1", " ", (v_real_bool_bool_real_real_real_DT_3_3_1.1 == v_real_real_real_30), " ", "v_real_bool_bool_real_real_real_DT_3_3_1.2", " ", (v_real_bool_bool_real_real_real_DT_3_3_1.2 == v_DT_3_3_24), " ", "v_seq_10", " ", (v_seq_10 == [v_DT_2_2_33]), " ", "v_real_bool_bool_6.2", " ", v_real_bool_bool_6.2, " ", "v_real_bool_bool_6.0", " ", (v_real_bool_bool_6.0 == 21.18), " ", "v_real_bool_bool_6.1", " ", v_real_bool_bool_6.1, " ", "v_DT_3_3_6.DT_3_3_2", " ", (v_DT_3_3_6.DT_3_3_2 == 7.86), " ", "v_DT_2_2_16.DT_2_2_1", " ", v_DT_2_2_16.DT_2_2_1, " ", "v_DT_3_3_6.DT_3_3_1", " ", (v_DT_3_3_6.DT_3_3_1 == -23.07), " ", "v_DT_3_3_1", " ", (v_DT_3_3_1 == v_DT_3_3_25), " ", "v_DT_3_3_6.DT_3_3_4", " ", (v_DT_3_3_6.DT_3_3_4 == -15.48), " ", "v_DT_2_2_16.DT_2_2_3", " ", (v_DT_2_2_16.DT_2_2_3 == map[-20 := false, 19 := true, -29 := false, -16 := true]), " ", "v_DT_3_3_6.DT_3_3_3", " ", (v_DT_3_3_6.DT_3_3_3 == -9.81), " ", "v_DT_2_2_16.DT_2_2_2", " ", v_DT_2_2_16.DT_2_2_2, " ", "v_real_bool_bool_2.2", " ", v_real_bool_bool_2.2, " ", "v_DT_3_3_3", " ", (v_DT_3_3_3 == v_DT_3_3_26), " ", "v_DT_3_3_2", " ", (v_DT_3_3_2 == v_DT_3_3_27), " ", "v_real_bool_bool_2.0", " ", (v_real_bool_bool_2.0 == -16.70), " ", "v_DT_3_3_5", " ", (v_DT_3_3_5 == v_DT_3_3_28), " ", "v_real_bool_bool_2.1", " ", v_real_bool_bool_2.1, " ", "v_DT_3_3_4", " ", (v_DT_3_3_4 == v_DT_3_3_29), " ", "v_DT_3_3_6", " ", (v_DT_3_3_6 == v_DT_3_3_30), " ", "v_seq_9", " ", (v_seq_9 == [v_DT_2_2_34]), " ", "v_seq_8", " ", (v_seq_8 == [[v_DT_2_2_35], []]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_7", " ", (v_seq_7 == [[v_DT_2_2_36], []]), " ", "v_int_11", " ", v_int_11, " ", "v_seq_6", " ", (v_seq_6 == [-15.21, 28.16]), " ", "v_seq_4", " ", (v_seq_4 == ['P', 'U', 'J']), " ", "v_DT_2_2_11.DT_2_2_1", " ", v_DT_2_2_11.DT_2_2_1, " ", "v_DT_2_2_11.DT_2_2_2", " ", v_DT_2_2_11.DT_2_2_2, " ", "v_int_15", " ", v_int_15, " ", "v_real_real_real_4.1", " ", (v_real_real_real_4.1 == 21.68), " ", "v_int_14", " ", v_int_14, " ", "v_real_real_real_4.0", " ", (v_real_real_real_4.0 == -9.90), " ", "v_DT_2_2_11.DT_2_2_3", " ", (v_DT_2_2_11.DT_2_2_3 == map[22 := true, 23 := true, 29 := false]), "\n";
	return ;
}
