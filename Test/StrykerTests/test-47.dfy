// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_3(DT_1_3_1: T_2, DT_1_3_2: T_2, DT_1_3_3: T_2, DT_1_3_4: T_1)
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

method m_method_2(p_m_method_2_1: char) returns (ret_1: seq<bool>)
	requires ((p_m_method_2_1 == 'K'));
	ensures (((p_m_method_2_1 == 'K')) ==> (|ret_1| == 4 && (ret_1[0] == false) && (ret_1[1] == false) && (ret_1[2] == true) && (ret_1[3] == true)));
{
	assert ((p_m_method_2_1 == 'K'));
	expect ((p_m_method_2_1 == 'K'));
	var v_array_5: array<real> := new real[3] [17.03, -13.16, -12.47];
	var v_DT_1_3_1: DT_1<array<real>, int> := DT_1_3(-3, 11, 20, v_array_5);
	var v_array_6: array<real> := new real[3] [-20.04, -0.62, 9.14];
	var v_DT_1_3_2: DT_1<array<real>, int> := DT_1_3(28, 4, 11, v_array_6);
	var v_bool_1: bool, v_int_14: int, v_set_1: set<DT_1<array<real>, int>>, v_int_15: int, v_seq_5: seq<seq<real>> := true, 2, {v_DT_1_3_1, v_DT_1_3_2}, 2, [[-20.90, -10.19, 24.87, 23.59], [], [-21.38, 18.58, 21.96, 28.80], [26.79]];
	var v_DT_1_3_3: DT_1<array<real>, int> := DT_1_3(-3, 11, 20, v_array_5);
	var v_DT_1_3_4: DT_1<array<real>, int> := DT_1_3(28, 4, 11, v_array_6);
	var v_DT_1_3_5: DT_1<array<real>, int> := DT_1_3(-3, 11, 20, v_array_5);
	var v_DT_1_3_6: DT_1<array<real>, int> := DT_1_3(28, 4, 11, v_array_6);
	print "v_array_6[2]", " ", (v_array_6[2] == 9.14), " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_3_1", " ", (v_DT_1_3_1 == v_DT_1_3_3), " ", "v_DT_1_3_2.DT_1_3_4", " ", (v_DT_1_3_2.DT_1_3_4 == v_array_6), " ", "v_DT_1_3_2.DT_1_3_3", " ", v_DT_1_3_2.DT_1_3_3, " ", "v_DT_1_3_2.DT_1_3_2", " ", v_DT_1_3_2.DT_1_3_2, " ", "v_DT_1_3_2", " ", (v_DT_1_3_2 == v_DT_1_3_4), " ", "v_DT_1_3_2.DT_1_3_1", " ", v_DT_1_3_2.DT_1_3_1, " ", "p_m_method_2_1", " ", (p_m_method_2_1 == 'K'), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_DT_1_3_1.DT_1_3_4", " ", (v_DT_1_3_1.DT_1_3_4 == v_array_5), " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_seq_5", " ", (v_seq_5 == [[-20.90, -10.19, 24.87, 23.59], [], [-21.38, 18.58, 21.96, 28.80], [26.79]]), " ", "v_set_1", " ", (v_set_1 == {v_DT_1_3_5, v_DT_1_3_6}), " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_5[0]", " ", (v_array_5[0] == 17.03), " ", "v_DT_1_3_1.DT_1_3_2", " ", v_DT_1_3_1.DT_1_3_2, " ", "v_DT_1_3_1.DT_1_3_3", " ", v_DT_1_3_1.DT_1_3_3, " ", "v_array_5[2]", " ", (v_array_5[2] == -12.47), " ", "v_array_6[0]", " ", (v_array_6[0] == -20.04), " ", "v_array_5[1]", " ", (v_array_5[1] == -13.16), " ", "v_DT_1_3_1.DT_1_3_1", " ", v_DT_1_3_1.DT_1_3_1, " ", "v_array_6[1]", " ", (v_array_6[1] == -0.62), "\n";
	return [false, false, true, true];
}

method m_method_1(p_m_method_1_1: seq<bool>, p_m_method_1_2: char) returns (ret_1: bool)
	requires (|p_m_method_1_1| == 5 && (p_m_method_1_1[0] == true) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == false) && (p_m_method_1_1[3] == true) && (p_m_method_1_1[4] == true) && (p_m_method_1_2 == 'l'));
	ensures ((|p_m_method_1_1| == 5 && (p_m_method_1_1[0] == true) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == false) && (p_m_method_1_1[3] == true) && (p_m_method_1_1[4] == true) && (p_m_method_1_2 == 'l')) ==> ((ret_1 == true)));
{
	var v_bool_bool_1: (bool, bool) := (true, true);
	var v_bool_bool_2: (bool, bool) := (false, true);
	var v_bool_bool_3: (bool, bool) := (false, false);
	var v_bool_bool_4: (bool, bool) := (true, true);
	var v_map_3: map<multiset<(bool, bool)>, int> := (map[multiset({v_bool_bool_1, v_bool_bool_2, v_bool_bool_3, v_bool_bool_4}) := 20] - {});
	var v_bool_bool_5: (bool, bool) := (false, false);
	var v_bool_bool_6: (bool, bool) := (false, true);
	var v_bool_bool_7: (bool, bool) := (true, false);
	var v_bool_bool_8: (bool, bool) := (false, true);
	var v_bool_bool_9: (bool, bool) := (true, false);
	var v_bool_bool_10: (bool, bool) := (false, false);
	var v_bool_bool_11: (bool, bool) := (true, true);
	var v_bool_bool_12: (bool, bool) := (true, true);
	var v_bool_bool_13: (bool, bool) := (false, false);
	var v_bool_bool_14: (bool, bool) := (false, false);
	var v_bool_bool_15: (bool, bool) := (true, false);
	var v_bool_bool_16: (bool, bool) := (true, false);
	var v_map_2: map<int, multiset<(bool, bool)>> := map[18 := multiset({}), 12 := multiset({v_bool_bool_5, v_bool_bool_6, v_bool_bool_7, v_bool_bool_8}), 25 := multiset{v_bool_bool_9}, 0 := multiset{v_bool_bool_10, v_bool_bool_11, v_bool_bool_12}, 22 := multiset{v_bool_bool_13, v_bool_bool_14, v_bool_bool_15, v_bool_bool_16}];
	var v_int_11: int := 26;
	var v_bool_bool_17: (bool, bool) := (true, false);
	var v_bool_bool_18: (bool, bool) := (true, false);
	var v_bool_bool_19: (bool, bool) := (false, false);
	var v_bool_bool_20: (bool, bool) := (false, true);
	var v_multiset_1: multiset<(bool, bool)> := (if ((v_int_11 in v_map_2)) then (v_map_2[v_int_11]) else (multiset{v_bool_bool_17, v_bool_bool_18, v_bool_bool_19, v_bool_bool_20}));
	var v_seq_4: seq<bool> := [false, false, true];
	var v_int_12: int := 15;
	var v_int_13: int := safe_index_seq(v_seq_4, v_int_12);
	v_int_11 := (if ((v_multiset_1 in v_map_3)) then (v_map_3[v_multiset_1]) else (v_int_13));
	var v_DT_1_1_1: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_2: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_3: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_4: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_5: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_6: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_7: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_8: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_9: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_10: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_11: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_12: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_13: DT_1<int, real> := DT_1_1;
	var v_bool_bool_21: (bool, bool) := (false, false);
	var v_bool_bool_22: (bool, bool) := (true, false);
	var v_bool_bool_23: (bool, bool) := (true, false);
	var v_bool_bool_24: (bool, bool) := (false, true);
	var v_bool_bool_25: (bool, bool) := (true, true);
	var v_bool_bool_26: (bool, bool) := (false, false);
	var v_bool_bool_27: (bool, bool) := (false, true);
	var v_bool_bool_28: (bool, bool) := (false, false);
	var v_bool_bool_29: (bool, bool) := (true, true);
	var v_bool_bool_30: (bool, bool) := (true, true);
	var v_bool_bool_31: (bool, bool) := (false, false);
	var v_bool_bool_32: (bool, bool) := (false, false);
	var v_bool_bool_33: (bool, bool) := (true, false);
	var v_bool_bool_34: (bool, bool) := (true, false);
	var v_bool_bool_35: (bool, bool) := (true, false);
	var v_bool_bool_36: (bool, bool) := (false, false);
	var v_bool_bool_37: (bool, bool) := (true, false);
	var v_bool_bool_38: (bool, bool) := (false, true);
	print "v_bool_bool_11.0", " ", v_bool_bool_11.0, " ", "v_bool_bool_11.1", " ", v_bool_bool_11.1, " ", "v_bool_bool_13.0", " ", v_bool_bool_13.0, " ", "v_bool_bool_13.1", " ", v_bool_bool_13.1, " ", "v_bool_bool_15.0", " ", v_bool_bool_15.0, " ", "v_bool_bool_9", " ", v_bool_bool_9, " ", "v_bool_bool_5", " ", v_bool_bool_5, " ", "v_bool_bool_6", " ", v_bool_bool_6, " ", "v_bool_bool_7", " ", v_bool_bool_7, " ", "v_bool_bool_8", " ", v_bool_bool_8, " ", "v_bool_bool_1", " ", v_bool_bool_1, " ", "v_bool_bool_2", " ", v_bool_bool_2, " ", "v_bool_bool_3", " ", v_bool_bool_3, " ", "v_bool_bool_4", " ", v_bool_bool_4, " ", "v_bool_bool_15.1", " ", v_bool_bool_15.1, " ", "v_bool_bool_17.0", " ", v_bool_bool_17.0, " ", "v_bool_bool_17.1", " ", v_bool_bool_17.1, " ", "v_bool_bool_19.0", " ", v_bool_bool_19.0, " ", "v_bool_bool_19.1", " ", v_bool_bool_19.1, " ", "v_bool_bool_20", " ", v_bool_bool_20, " ", "v_bool_bool_7.1", " ", v_bool_bool_7.1, " ", "v_bool_bool_7.0", " ", v_bool_bool_7.0, " ", "v_bool_bool_9.1", " ", v_bool_bool_9.1, " ", "v_bool_bool_9.0", " ", v_bool_bool_9.0, " ", "v_multiset_1", " ", (v_multiset_1 == multiset{v_bool_bool_21, v_bool_bool_22, v_bool_bool_23, v_bool_bool_24}), " ", "v_bool_bool_1.1", " ", v_bool_bool_1.1, " ", "v_bool_bool_1.0", " ", v_bool_bool_1.0, " ", "v_bool_bool_3.1", " ", v_bool_bool_3.1, " ", "v_bool_bool_3.0", " ", v_bool_bool_3.0, " ", "v_bool_bool_5.1", " ", v_bool_bool_5.1, " ", "v_bool_bool_5.0", " ", v_bool_bool_5.0, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_bool_10.0", " ", v_bool_bool_10.0, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_bool_bool_10.1", " ", v_bool_bool_10.1, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_bool_bool_12.0", " ", v_bool_bool_12.0, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_bool_bool_12.1", " ", v_bool_bool_12.1, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_bool_bool_14.0", " ", v_bool_bool_14.0, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_bool_bool_14.1", " ", v_bool_bool_14.1, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_bool_bool_17", " ", v_bool_bool_17, " ", "v_bool_bool_16", " ", v_bool_bool_16, " ", "v_bool_bool_15", " ", v_bool_bool_15, " ", "v_bool_bool_14", " ", v_bool_bool_14, " ", "v_bool_bool_13", " ", v_bool_bool_13, " ", "v_bool_bool_12", " ", v_bool_bool_12, " ", "v_bool_bool_11", " ", v_bool_bool_11, " ", "v_bool_bool_10", " ", v_bool_bool_10, " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 'l'), " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_bool_bool_19", " ", v_bool_bool_19, " ", "v_bool_bool_18", " ", v_bool_bool_18, " ", "v_bool_bool_16.0", " ", v_bool_bool_16.0, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_bool_bool_16.1", " ", v_bool_bool_16.1, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_bool_bool_18.0", " ", v_bool_bool_18.0, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_bool_bool_18.1", " ", v_bool_bool_18.1, " ", "v_DT_1_1_13", " ", v_DT_1_1_13, " ", "v_bool_bool_20.0", " ", v_bool_bool_20.0, " ", "v_bool_bool_20.1", " ", v_bool_bool_20.1, " ", "v_bool_bool_8.0", " ", v_bool_bool_8.0, " ", "v_bool_bool_6.1", " ", v_bool_bool_6.1, " ", "v_bool_bool_8.1", " ", v_bool_bool_8.1, " ", "v_map_3", " ", (v_map_3 == map[multiset{v_bool_bool_25, v_bool_bool_26, v_bool_bool_27} := 20]), " ", "v_map_2", " ", (v_map_2 == map[0 := multiset{v_bool_bool_28, v_bool_bool_29, v_bool_bool_30}, 18 := multiset{}, 22 := multiset{v_bool_bool_31, v_bool_bool_32, v_bool_bool_33, v_bool_bool_34}, 25 := multiset{v_bool_bool_35}, 12 := multiset{v_bool_bool_36, v_bool_bool_37, v_bool_bool_38}]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_bool_bool_2.0", " ", v_bool_bool_2.0, " ", "v_int_11", " ", v_int_11, " ", "v_bool_bool_4.0", " ", v_bool_bool_4.0, " ", "v_seq_4", " ", v_seq_4, " ", "v_bool_bool_2.1", " ", v_bool_bool_2.1, " ", "v_bool_bool_6.0", " ", v_bool_bool_6.0, " ", "v_bool_bool_4.1", " ", v_bool_bool_4.1, "\n";
	return ((if (true) then ({{v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3}, {v_DT_1_1_4, v_DT_1_1_5}, {v_DT_1_1_6, v_DT_1_1_7, v_DT_1_1_8, v_DT_1_1_9}}) else ({{}, {v_DT_1_1_10, v_DT_1_1_11, v_DT_1_1_12, v_DT_1_1_13}})) !! (map[{} := 23]).Keys);
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_3: seq<int> := [24, 18];
	var v_int_7: int := 2;
	var v_seq_11: seq<int> := v_seq_3;
	var v_int_22: int := v_int_7;
	var v_int_23: int := safe_index_seq(v_seq_11, v_int_22);
	v_int_7 := v_int_23;
	var v_int_8: int := 12;
	var v_int_9: int := 28;
	var v_int_10: int := safe_division(v_int_8, v_int_9);
	var v_array_1: array<bool> := new bool[4] [true, true, false, false];
	var v_array_bool_1: (array<bool>, bool) := (v_array_1, false);
	var v_array_2: array<bool> := new bool[4] [false, false, true, false];
	var v_array_bool_2: (array<bool>, bool) := (v_array_2, true);
	var v_array_3: array<bool> := new bool[4] [true, true, true, true];
	var v_array_bool_3: (array<bool>, bool) := (v_array_3, false);
	var v_map_1: map<(array<bool>, bool), int> := map[v_array_bool_1 := 10, v_array_bool_2 := 1, v_array_bool_3 := 10];
	var v_array_4: array<bool> := new bool[4] [true, false, false, false];
	var v_array_bool_4: (array<bool>, bool) := (v_array_4, true);
	var v_array_bool_5: (array<bool>, bool) := v_array_bool_4;
	var v_char_1: char := 'K';
	var v_seq_6: seq<bool> := m_method_2(v_char_1);
	var v_seq_9: seq<bool> := ((match 'K' {
		case 'J' => [true, true]
		case _ => [true]
	}) + v_seq_6);
	var v_map_4: map<seq<seq<bool>>, char> := map[[[true, true, false, false], [true]] := 'K', [[true, false, true], [false, true, false], [false, false]] := 's', [[false]] := 'c'][[[false, false, false], [true, false, true], [true, true, false, true]] := 'Q'];
	var v_seq_7: seq<seq<bool>> := [[false, false], [true]];
	var v_seq_10: seq<seq<bool>> := v_seq_7;
	var v_int_18: int := 28;
	var v_int_19: int := 16;
	var v_int_20: int, v_int_21: int := safe_subsequence(v_seq_10, v_int_18, v_int_19);
	var v_int_16: int, v_int_17: int := v_int_20, v_int_21;
	var v_seq_8: seq<seq<bool>> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_16..v_int_17]) else (v_seq_7));
	var v_char_2: char := (if ((v_seq_8 in v_map_4)) then (v_map_4[v_seq_8]) else ((if (true) then ('l') else ('u'))));
	var v_bool_2: bool := m_method_1(v_seq_9, v_char_2);
	v_seq_3, v_array_3[2] := ([(if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (4)), v_int_10] + [(if ((v_array_bool_5 in v_map_1)) then (v_map_1[v_array_bool_5]) else (23)), (match false {
		case false => 11
		case _ => 4
	}), v_int_10, (4 - 15)]), v_bool_2;
	var v_array_bool_6: (array<bool>, bool) := (v_array_3, false);
	var v_array_bool_7: (array<bool>, bool) := (v_array_2, true);
	var v_array_bool_8: (array<bool>, bool) := (v_array_4, true);
	var v_array_bool_9: (array<bool>, bool) := (v_array_4, true);
	var v_array_bool_10: (array<bool>, bool) := (v_array_1, false);
	var v_array_bool_11: (array<bool>, bool) := (v_array_2, true);
	var v_array_bool_12: (array<bool>, bool) := (v_array_3, false);
	var v_array_bool_13: (array<bool>, bool) := (v_array_1, false);
	print "v_bool_2", " ", v_bool_2, " ", "v_array_bool_3.1", " ", v_array_bool_3.1, " ", "v_array_bool_4.0", " ", (v_array_bool_4.0 == v_array_4), " ", "v_array_bool_4.1", " ", v_array_bool_4.1, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_array_bool_1.0", " ", (v_array_bool_1.0 == v_array_1), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_bool_1.1", " ", v_array_bool_1.1, " ", "v_array_bool_2.0", " ", (v_array_bool_2.0 == v_array_2), " ", "v_int_9", " ", v_int_9, " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_bool_2.1", " ", v_array_bool_2.1, " ", "v_array_bool_3.0", " ", (v_array_bool_3.0 == v_array_3), " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_array_bool_3", " ", (v_array_bool_3 == v_array_bool_6), " ", "v_char_1", " ", (v_char_1 == 'K'), " ", "v_array_bool_2", " ", (v_array_bool_2 == v_array_bool_7), " ", "v_map_4", " ", (v_map_4 == map[[[false]] := 'c', [[true, true, false, false], [true]] := 'K', [[false, false, false], [true, false, true], [true, true, false, true]] := 'Q', [[true, false, true], [false, true, false], [false, false]] := 's']), " ", "v_array_bool_5", " ", (v_array_bool_5 == v_array_bool_8), " ", "v_array_bool_4", " ", (v_array_bool_4 == v_array_bool_9), " ", "v_char_2", " ", (v_char_2 == 'l'), " ", "v_array_bool_1", " ", (v_array_bool_1 == v_array_bool_10), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[v_array_bool_11 := 1, v_array_bool_12 := 10, v_array_bool_13 := 10]), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_10", " ", v_int_10, " ", "v_seq_3", " ", v_seq_3, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_4[2]", " ", v_array_4[2], "\n";
	return ;
}
