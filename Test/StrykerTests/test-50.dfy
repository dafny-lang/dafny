// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1 | DT_1_2(DT_1_2_1: T_1)
datatype DT_2<T_2, T_3> = DT_2_1 | DT_2_4(DT_2_4_1: T_2)
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

method m_method_4(p_m_method_4_1: (bool, bool, int)) returns (ret_1: char)
	requires (((p_m_method_4_1).0 == true) && ((p_m_method_4_1).1 == false) && ((p_m_method_4_1).2 == 1));
	ensures ((((p_m_method_4_1).0 == true) && ((p_m_method_4_1).1 == false) && ((p_m_method_4_1).2 == 1)) ==> ((ret_1 == 'Y')));
{
	print "p_m_method_4_1.1", " ", p_m_method_4_1.1, " ", "p_m_method_4_1.2", " ", p_m_method_4_1.2, " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "p_m_method_4_1.0", " ", p_m_method_4_1.0, "\n";
	return 'Y';
}

method m_method_3(p_m_method_3_1: char) returns (ret_1: char)
	requires ((p_m_method_3_1 == 'S'));
	ensures (((p_m_method_3_1 == 'S')) ==> ((ret_1 == 'Y')));
{
	var v_bool_bool_int_1: (bool, bool, int) := (true, false, 1);
	var v_bool_bool_int_2: (bool, bool, int) := v_bool_bool_int_1;
	var v_char_1: char := m_method_4(v_bool_bool_int_2);
	print "v_char_1", " ", (v_char_1 == 'Y'), " ", "v_bool_bool_int_1.1", " ", v_bool_bool_int_1.1, " ", "v_bool_bool_int_2", " ", v_bool_bool_int_2, " ", "v_bool_bool_int_1", " ", v_bool_bool_int_1, " ", "v_bool_bool_int_1.0", " ", v_bool_bool_int_1.0, " ", "v_bool_bool_int_1.2", " ", v_bool_bool_int_1.2, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'S'), "\n";
	return v_char_1;
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

method m_method_2(p_m_method_2_1: DT_1<(bool, real, bool)>, p_m_method_2_2: bool, p_m_method_2_3: int, p_m_method_2_4: DT_2<real, int>) returns (ret_1: int)
	requires ((p_m_method_2_2 == true) && (p_m_method_2_1.DT_1_2? && (((p_m_method_2_1.DT_1_2_1).0 == false) && (12.57 < (p_m_method_2_1.DT_1_2_1).1 < 12.77) && ((p_m_method_2_1.DT_1_2_1).2 == true))) && (p_m_method_2_4.DT_2_4? && ((-15.82 < p_m_method_2_4.DT_2_4_1 < -15.62))) && (p_m_method_2_3 == 1));
	ensures (((p_m_method_2_2 == true) && (p_m_method_2_1.DT_1_2? && (((p_m_method_2_1.DT_1_2_1).0 == false) && (12.57 < (p_m_method_2_1.DT_1_2_1).1 < 12.77) && ((p_m_method_2_1.DT_1_2_1).2 == true))) && (p_m_method_2_4.DT_2_4? && ((-15.82 < p_m_method_2_4.DT_2_4_1 < -15.62))) && (p_m_method_2_3 == 1)) ==> ((ret_1 == 20)));
{
	var v_bool_real_bool_9: (bool, real, bool) := (false, 12.67, true);
	var v_DT_1_2_10: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_9);
	var v_bool_real_bool_10: (bool, real, bool) := (false, 12.67, true);
	var v_DT_2_4_3: DT_2<real, int> := DT_2_4(-15.72);
	print "p_m_method_2_1", " ", (p_m_method_2_1 == v_DT_1_2_10), " ", "p_m_method_2_1.DT_1_2_1", " ", (p_m_method_2_1.DT_1_2_1 == v_bool_real_bool_10), " ", "p_m_method_2_4.DT_2_4_1", " ", (p_m_method_2_4.DT_2_4_1 == -15.72), " ", "p_m_method_2_1.DT_1_2_1.2", " ", p_m_method_2_1.DT_1_2_1.2, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, " ", "p_m_method_2_1.DT_1_2_1.0", " ", p_m_method_2_1.DT_1_2_1.0, " ", "p_m_method_2_1.DT_1_2_1.1", " ", (p_m_method_2_1.DT_1_2_1.1 == 12.67), " ", "p_m_method_2_4", " ", (p_m_method_2_4 == v_DT_2_4_3), "\n";
	return 20;
}

method m_method_1(p_m_method_1_1: real) returns (ret_1: seq<char>)
	requires ((3.69 < p_m_method_1_1 < 3.89));
	ensures (((3.69 < p_m_method_1_1 < 3.89)) ==> (|ret_1| == 4 && (ret_1[0] == 'k') && (ret_1[1] == 'c') && (ret_1[2] == 'q') && (ret_1[3] == 'Q')));
{
	print "p_m_method_1_1", " ", (p_m_method_1_1 == 3.79), "\n";
	return ['k', 'c', 'q', 'Q'];
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_1: map<multiset<char>, multiset<bool>> := map[multiset({'q', 'k', 'Z'}) := multiset{true, true, true}, multiset({'V', 'b', 'C', 'w'}) := multiset{}, multiset{'I', 'u', 'f'} := multiset{false, false}, multiset{'S'} := multiset{}, multiset({'e', 'J'}) := multiset{true, false, true}];
	var v_multiset_1: multiset<char> := multiset{'O'};
	var v_seq_3: seq<char> := ['l', 'A', 'w'];
	var v_seq_8: seq<char> := v_seq_3;
	var v_int_15: int := 4;
	var v_int_16: int := 0;
	var v_int_17: int, v_int_18: int := safe_subsequence(v_seq_8, v_int_15, v_int_16);
	var v_int_13: int, v_int_14: int := v_int_17, v_int_18;
	var v_real_1: real := 3.79;
	var v_seq_4: seq<char> := m_method_1(v_real_1);
	var v_seq_7: seq<char> := ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_13..v_int_14]) else (v_seq_3)) + v_seq_4);
	var v_bool_real_bool_1: (bool, real, bool) := (true, 26.92, true);
	var v_DT_1_2_1: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_1);
	var v_bool_real_bool_2: (bool, real, bool) := (false, -9.46, false);
	var v_DT_1_2_2: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_2);
	var v_bool_real_bool_3: (bool, real, bool) := (false, 4.07, false);
	var v_DT_1_2_3: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_3);
	var v_bool_real_bool_4: (bool, real, bool) := (true, -23.38, true);
	var v_DT_1_2_4: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_4);
	var v_bool_real_bool_5: (bool, real, bool) := (true, -25.80, true);
	var v_DT_1_2_5: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_5);
	var v_seq_5: seq<seq<DT_1<(bool, real, bool)>>> := [[v_DT_1_2_1, v_DT_1_2_2, v_DT_1_2_3], [v_DT_1_2_4, v_DT_1_2_5], []];
	var v_int_7: int := 9;
	var v_seq_9: seq<seq<DT_1<(bool, real, bool)>>> := v_seq_5;
	var v_int_19: int := v_int_7;
	var v_int_20: int := safe_index_seq(v_seq_9, v_int_19);
	v_int_7 := v_int_20;
	var v_bool_real_bool_6: (bool, real, bool) := (false, 0.41, true);
	var v_DT_1_2_6: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_6);
	var v_bool_real_bool_7: (bool, real, bool) := (true, -1.96, false);
	var v_DT_1_2_7: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_7);
	var v_seq_6: seq<DT_1<(bool, real, bool)>> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_7]) else ([v_DT_1_2_6, v_DT_1_2_7]));
	var v_bool_real_bool_8: (bool, real, bool) := (false, 12.67, true);
	var v_DT_1_2_8: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_8);
	var v_DT_1_2_9: DT_1<(bool, real, bool)> := v_DT_1_2_8;
	var v_bool_1: bool := true;
	var v_int_8: int := 1;
	var v_DT_2_4_1: DT_2<real, int> := DT_2_4(-15.72);
	var v_DT_2_4_2: DT_2<real, int> := v_DT_2_4_1;
	var v_int_9: int := m_method_2(v_DT_1_2_9, v_bool_1, v_int_8, v_DT_2_4_2);
	var v_int_10: int := v_int_9;
	var v_int_11: int := safe_index_seq(v_seq_6, v_int_10);
	var v_int_12: int := v_int_11;
	var v_char_2: char := (if (false) then ('W') else ('S'));
	var v_char_3: char := m_method_3(v_char_2);
	var v_multiset_2: multiset<bool>, v_char_4: char := ((match false {
		case true => (if (true) then (multiset({true, true})) else (multiset{false, false, false}))
		case _ => (multiset({false, false, true}) * multiset{})
	}) + ((if ((v_multiset_1 in v_map_1)) then (v_map_1[v_multiset_1]) else (multiset({true, true, false}))) + (if (false) then (multiset{false, false, true, true}) else (multiset{})))), (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_12]) else (v_char_3));
	var v_bool_real_bool_11: (bool, real, bool) := (false, 0.41, true);
	var v_DT_1_2_11: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_11);
	var v_bool_real_bool_12: (bool, real, bool) := (true, -25.80, true);
	var v_DT_1_2_12: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_12);
	var v_bool_real_bool_13: (bool, real, bool) := (false, 12.67, true);
	var v_DT_1_2_13: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_13);
	var v_bool_real_bool_14: (bool, real, bool) := (true, -1.96, false);
	var v_DT_1_2_14: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_14);
	var v_bool_real_bool_15: (bool, real, bool) := (false, -9.46, false);
	var v_DT_1_2_15: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_15);
	var v_bool_real_bool_16: (bool, real, bool) := (true, 26.92, true);
	var v_DT_1_2_16: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_16);
	var v_bool_real_bool_17: (bool, real, bool) := (true, -23.38, true);
	var v_DT_1_2_17: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_17);
	var v_bool_real_bool_18: (bool, real, bool) := (false, 4.07, false);
	var v_DT_1_2_18: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_18);
	var v_bool_real_bool_19: (bool, real, bool) := (false, 12.67, true);
	var v_DT_1_2_19: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_19);
	var v_bool_real_bool_20: (bool, real, bool) := (true, -25.80, true);
	var v_bool_real_bool_21: (bool, real, bool) := (false, -9.46, false);
	var v_bool_real_bool_22: (bool, real, bool) := (true, -1.96, false);
	var v_bool_real_bool_23: (bool, real, bool) := (true, -23.38, true);
	var v_DT_2_4_4: DT_2<real, int> := DT_2_4(-15.72);
	var v_bool_real_bool_24: (bool, real, bool) := (false, 12.67, true);
	var v_DT_2_4_5: DT_2<real, int> := DT_2_4(-15.72);
	var v_bool_real_bool_25: (bool, real, bool) := (false, 4.07, false);
	var v_bool_real_bool_26: (bool, real, bool) := (false, 12.67, true);
	var v_bool_real_bool_27: (bool, real, bool) := (true, 26.92, true);
	var v_bool_real_bool_28: (bool, real, bool) := (false, -9.46, false);
	var v_bool_real_bool_29: (bool, real, bool) := (false, 4.07, false);
	var v_bool_real_bool_30: (bool, real, bool) := (true, -23.38, true);
	var v_bool_real_bool_31: (bool, real, bool) := (true, 26.92, true);
	var v_bool_real_bool_32: (bool, real, bool) := (true, -25.80, true);
	var v_bool_real_bool_33: (bool, real, bool) := (false, 0.41, true);
	var v_bool_real_bool_34: (bool, real, bool) := (true, -1.96, false);
	var v_bool_real_bool_35: (bool, real, bool) := (true, 26.92, true);
	var v_DT_1_2_20: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_35);
	var v_bool_real_bool_36: (bool, real, bool) := (false, -9.46, false);
	var v_DT_1_2_21: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_36);
	var v_bool_real_bool_37: (bool, real, bool) := (false, 4.07, false);
	var v_DT_1_2_22: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_37);
	var v_bool_real_bool_38: (bool, real, bool) := (true, 26.92, true);
	var v_DT_1_2_23: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_38);
	var v_bool_real_bool_39: (bool, real, bool) := (false, -9.46, false);
	var v_DT_1_2_24: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_39);
	var v_bool_real_bool_40: (bool, real, bool) := (false, 4.07, false);
	var v_DT_1_2_25: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_40);
	var v_bool_real_bool_41: (bool, real, bool) := (true, -23.38, true);
	var v_DT_1_2_26: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_41);
	var v_bool_real_bool_42: (bool, real, bool) := (true, -25.80, true);
	var v_DT_1_2_27: DT_1<(bool, real, bool)> := DT_1_2(v_bool_real_bool_42);
	var v_bool_real_bool_43: (bool, real, bool) := (false, 0.41, true);
	print "v_bool_real_bool_4.1", " ", (v_bool_real_bool_4.1 == -23.38), " ", "v_DT_1_2_6", " ", (v_DT_1_2_6 == v_DT_1_2_11), " ", "v_bool_real_bool_2.2", " ", v_bool_real_bool_2.2, " ", "v_bool_real_bool_4.0", " ", v_bool_real_bool_4.0, " ", "v_DT_1_2_5", " ", (v_DT_1_2_5 == v_DT_1_2_12), " ", "v_bool_real_bool_2.1", " ", (v_bool_real_bool_2.1 == -9.46), " ", "v_DT_1_2_8", " ", (v_DT_1_2_8 == v_DT_1_2_13), " ", "v_bool_real_bool_2.0", " ", v_bool_real_bool_2.0, " ", "v_DT_1_2_7", " ", (v_DT_1_2_7 == v_DT_1_2_14), " ", "v_DT_1_2_2", " ", (v_DT_1_2_2 == v_DT_1_2_15), " ", "v_DT_1_2_1", " ", (v_DT_1_2_1 == v_DT_1_2_16), " ", "v_DT_1_2_4", " ", (v_DT_1_2_4 == v_DT_1_2_17), " ", "v_DT_1_2_3", " ", (v_DT_1_2_3 == v_DT_1_2_18), " ", "v_bool_real_bool_8.2", " ", v_bool_real_bool_8.2, " ", "v_bool_real_bool_8.1", " ", (v_bool_real_bool_8.1 == 12.67), " ", "v_bool_real_bool_6.2", " ", v_bool_real_bool_6.2, " ", "v_bool_real_bool_8.0", " ", v_bool_real_bool_8.0, " ", "v_DT_1_2_9", " ", (v_DT_1_2_9 == v_DT_1_2_19), " ", "v_bool_real_bool_6.1", " ", (v_bool_real_bool_6.1 == 0.41), " ", "v_bool_real_bool_4.2", " ", v_bool_real_bool_4.2, " ", "v_DT_1_2_5.DT_1_2_1", " ", (v_DT_1_2_5.DT_1_2_1 == v_bool_real_bool_20), " ", "v_bool_real_bool_6.0", " ", v_bool_real_bool_6.0, " ", "v_DT_1_2_2.DT_1_2_1", " ", (v_DT_1_2_2.DT_1_2_1 == v_bool_real_bool_21), " ", "v_DT_1_2_7.DT_1_2_1", " ", (v_DT_1_2_7.DT_1_2_1 == v_bool_real_bool_22), " ", "v_DT_1_2_4.DT_1_2_1", " ", (v_DT_1_2_4.DT_1_2_1 == v_bool_real_bool_23), " ", "v_multiset_2", " ", (v_multiset_2 == multiset{false, true}), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{'O'}), " ", "v_DT_2_4_1", " ", (v_DT_2_4_1 == v_DT_2_4_4), " ", "v_DT_1_2_8.DT_1_2_1", " ", (v_DT_1_2_8.DT_1_2_1 == v_bool_real_bool_24), " ", "v_DT_2_4_2", " ", (v_DT_2_4_2 == v_DT_2_4_5), " ", "v_DT_1_2_3.DT_1_2_1", " ", (v_DT_1_2_3.DT_1_2_1 == v_bool_real_bool_25), " ", "v_real_1", " ", (v_real_1 == 3.79), " ", "v_bool_real_bool_3.2", " ", v_bool_real_bool_3.2, " ", "v_bool_real_bool_5.0", " ", v_bool_real_bool_5.0, " ", "v_bool_1", " ", v_bool_1, " ", "v_bool_real_bool_3.1", " ", (v_bool_real_bool_3.1 == 4.07), " ", "v_bool_real_bool_1.2", " ", v_bool_real_bool_1.2, " ", "v_bool_real_bool_3.0", " ", v_bool_real_bool_3.0, " ", "v_bool_real_bool_1.1", " ", (v_bool_real_bool_1.1 == 26.92), " ", "v_bool_real_bool_1.0", " ", v_bool_real_bool_1.0, " ", "v_bool_real_bool_7.2", " ", v_bool_real_bool_7.2, " ", "v_bool_real_bool_7.1", " ", (v_bool_real_bool_7.1 == -1.96), " ", "v_bool_real_bool_5.2", " ", v_bool_real_bool_5.2, " ", "v_bool_real_bool_7.0", " ", v_bool_real_bool_7.0, " ", "v_bool_real_bool_5.1", " ", (v_bool_real_bool_5.1 == -25.80), " ", "v_DT_2_4_1.DT_2_4_1", " ", (v_DT_2_4_1.DT_2_4_1 == -15.72), " ", "v_int_9", " ", v_int_9, " ", "v_bool_real_bool_8", " ", (v_bool_real_bool_8 == v_bool_real_bool_26), " ", "v_char_3", " ", (v_char_3 == 'Y'), " ", "v_char_2", " ", (v_char_2 == 'S'), " ", "v_char_4", " ", (v_char_4 == 'k'), " ", "v_int_8", " ", v_int_8, " ", "v_bool_real_bool_1", " ", (v_bool_real_bool_1 == v_bool_real_bool_27), " ", "v_int_7", " ", v_int_7, " ", "v_bool_real_bool_2", " ", (v_bool_real_bool_2 == v_bool_real_bool_28), " ", "v_bool_real_bool_3", " ", (v_bool_real_bool_3 == v_bool_real_bool_29), " ", "v_map_1", " ", (v_map_1 == map[multiset{'b', 'C', 'V', 'w'} := multiset{}, multiset{'S'} := multiset{}, multiset{'u', 'f', 'I'} := multiset{false, false}, multiset{'q', 'Z', 'k'} := multiset{true, true, true}, multiset{'e', 'J'} := multiset{false, true, true}]), " ", "v_bool_real_bool_4", " ", (v_bool_real_bool_4 == v_bool_real_bool_30), " ", "v_DT_1_2_1.DT_1_2_1", " ", (v_DT_1_2_1.DT_1_2_1 == v_bool_real_bool_31), " ", "v_bool_real_bool_5", " ", (v_bool_real_bool_5 == v_bool_real_bool_32), " ", "v_bool_real_bool_6", " ", (v_bool_real_bool_6 == v_bool_real_bool_33), " ", "v_bool_real_bool_7", " ", (v_bool_real_bool_7 == v_bool_real_bool_34), " ", "v_seq_7", " ", (v_seq_7 == ['k', 'c', 'q', 'Q']), " ", "v_int_12", " ", v_int_12, " ", "v_seq_6", " ", (v_seq_6 == [v_DT_1_2_20, v_DT_1_2_21, v_DT_1_2_22]), " ", "v_int_11", " ", v_int_11, " ", "v_seq_5", " ", (v_seq_5 == [[v_DT_1_2_23, v_DT_1_2_24, v_DT_1_2_25], [v_DT_1_2_26, v_DT_1_2_27], []]), " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", (v_seq_4 == ['k', 'c', 'q', 'Q']), " ", "v_seq_3", " ", (v_seq_3 == ['l', 'A', 'w']), " ", "v_DT_1_2_6.DT_1_2_1", " ", (v_DT_1_2_6.DT_1_2_1 == v_bool_real_bool_43), "\n";
}
