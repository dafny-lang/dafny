// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2 | DT_1_3(DT_1_3_1: T_2, DT_1_3_2: T_2, DT_1_3_3: T_2, DT_1_3_4: T_2)
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: char, p_m_method_8_2: char, p_m_method_8_3: char, p_m_method_8_4: char) returns (ret_1: DT_1<real, int>)
	requires ((p_m_method_8_2 == 'X') && (p_m_method_8_1 == 'K') && (p_m_method_8_4 == 'n') && (p_m_method_8_3 == 'j'));
	ensures (((p_m_method_8_2 == 'X') && (p_m_method_8_1 == 'K') && (p_m_method_8_4 == 'n') && (p_m_method_8_3 == 'j')) ==> ((ret_1.DT_1_3? && ((ret_1.DT_1_3_1 == 24) && (ret_1.DT_1_3_2 == 12) && (ret_1.DT_1_3_3 == 10) && (ret_1.DT_1_3_4 == 9)))));
{
	var v_seq_21: seq<char> := ['j', 'o'];
	var v_int_30: int := 1;
	var v_seq_22: seq<char> := ['m', 'C', 'v', 'k'];
	var v_int_31: int := 5;
	var v_seq_33: seq<char> := v_seq_22;
	var v_int_45: int := v_int_31;
	var v_int_46: int := safe_index_seq(v_seq_33, v_int_45);
	v_int_31 := v_int_46;
	var v_char_27: char, v_char_28: char, v_char_29: char := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_30]) else ('k')), p_m_method_8_2, (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_31]) else ('i'));
	var v_seq_23: seq<DT_1<real, int>> := [];
	var v_int_32: int := -7;
	var v_DT_1_3_4: DT_1<real, int> := DT_1_3(24, 12, 10, 9);
	print "v_char_29", " ", (v_char_29 == 'm'), " ", "v_char_28", " ", (v_char_28 == 'X'), " ", "v_DT_1_3_4", " ", v_DT_1_3_4, " ", "v_char_27", " ", (v_char_27 == 'o'), " ", "p_m_method_8_4", " ", (p_m_method_8_4 == 'n'), " ", "v_DT_1_3_4.DT_1_3_3", " ", v_DT_1_3_4.DT_1_3_3, " ", "v_int_32", " ", v_int_32, " ", "v_DT_1_3_4.DT_1_3_4", " ", v_DT_1_3_4.DT_1_3_4, " ", "v_seq_21", " ", (v_seq_21 == ['j', 'o']), " ", "v_DT_1_3_4.DT_1_3_1", " ", v_DT_1_3_4.DT_1_3_1, " ", "v_seq_22", " ", (v_seq_22 == ['m', 'C', 'v', 'k']), " ", "v_DT_1_3_4.DT_1_3_2", " ", v_DT_1_3_4.DT_1_3_2, " ", "v_seq_23", " ", v_seq_23, " ", "p_m_method_8_1", " ", (p_m_method_8_1 == 'K'), " ", "p_m_method_8_3", " ", (p_m_method_8_3 == 'j'), " ", "p_m_method_8_2", " ", (p_m_method_8_2 == 'X'), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, "\n";
	return (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_32]) else (v_DT_1_3_4));
}

method m_method_7(p_m_method_7_1: char) returns (ret_1: seq<DT_1<real, int>>)
	requires ((p_m_method_7_1 == 'I'));
	ensures (((p_m_method_7_1 == 'I')) ==> (|ret_1| == 1 && (ret_1[0].DT_1_3? && ((ret_1[0].DT_1_3_1 == 9) && (ret_1[0].DT_1_3_2 == 19) && (ret_1[0].DT_1_3_3 == 29) && (ret_1[0].DT_1_3_4 == 21)))));
{
	var v_int_27: int, v_int_28: int := 18, -18;
	for v_int_26 := v_int_27 downto v_int_28 
		invariant (v_int_26 - v_int_28 >= 0)
	{
		if false {
			continue;
		}
		var v_DT_1_3_1: DT_1<real, int> := DT_1_3(9, 19, 29, 21);
		print "v_DT_1_3_1.DT_1_3_4", " ", v_DT_1_3_1.DT_1_3_4, " ", "v_DT_1_3_1", " ", v_DT_1_3_1, " ", "v_int_26", " ", v_int_26, " ", "v_DT_1_3_1.DT_1_3_2", " ", v_DT_1_3_1.DT_1_3_2, " ", "v_DT_1_3_1.DT_1_3_3", " ", v_DT_1_3_1.DT_1_3_3, " ", "v_DT_1_3_1.DT_1_3_1", " ", v_DT_1_3_1.DT_1_3_1, " ", "p_m_method_7_1", " ", (p_m_method_7_1 == 'I'), "\n";
		return [v_DT_1_3_1];
	}
	var v_char_23: char, v_char_24: char, v_char_25: char := 'K', 'Q', 'R';
	return [];
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: char, p_m_method_6_2: char, p_m_method_6_3: char) returns (ret_1: seq<seq<real>>)
	requires ((p_m_method_6_3 == 'j') && (p_m_method_6_2 == 'j') && (p_m_method_6_1 == 'j'));
	ensures (((p_m_method_6_3 == 'j') && (p_m_method_6_2 == 'j') && (p_m_method_6_1 == 'j')) ==> (|ret_1| == 4 && |ret_1[0]| == 2 && (-2.48 < ret_1[0][0] < -2.28) && (-13.89 < ret_1[0][1] < -13.69) && |ret_1[1]| == 1 && (5.74 < ret_1[1][0] < 5.94) && |ret_1[2]| == 1 && (-3.70 < ret_1[2][0] < -3.50) && |ret_1[3]| == 0));
{
	print "p_m_method_6_3", " ", (p_m_method_6_3 == 'j'), " ", "p_m_method_6_2", " ", (p_m_method_6_2 == 'j'), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == 'j'), "\n";
	return ([[-2.38, -13.79], [5.84], [-3.60]] + [[]]);
}

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: char) returns (ret_1: char)
	requires ((p_m_method_5_1 == 'm') && (p_m_method_5_2 == 'O'));
	ensures (((p_m_method_5_1 == 'm') && (p_m_method_5_2 == 'O')) ==> ((ret_1 == 'g')));
{
	assert ((p_m_method_5_1 == 'm') && (p_m_method_5_2 == 'O'));
	expect ((p_m_method_5_1 == 'm') && (p_m_method_5_2 == 'O'));
	print "p_m_method_5_2", " ", (p_m_method_5_2 == 'O'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'm'), "\n";
	return 'g';
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char, p_m_method_4_3: char, p_m_method_4_4: char) returns (ret_1: map<bool, bool>)
	requires ((p_m_method_4_2 == 'j') && (p_m_method_4_1 == 'j') && (p_m_method_4_4 == 'g') && (p_m_method_4_3 == 'j'));
	ensures (((p_m_method_4_2 == 'j') && (p_m_method_4_1 == 'j') && (p_m_method_4_4 == 'g') && (p_m_method_4_3 == 'j')) ==> ((ret_1 == map[false := false, true := true])));
{
	print "p_m_method_4_4", " ", (p_m_method_4_4 == 'g'), " ", "p_m_method_4_1", " ", (p_m_method_4_1 == 'j'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'j'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'j'), "\n";
	return (map[true := true, false := false] - {});
}

method m_method_3(p_m_method_3_1: map<bool, bool>, p_m_method_3_2: int, p_m_method_3_3: char) returns (ret_1: DT_1<real, bool>)
	requires ((p_m_method_3_1 == map[false := false, true := true]) && (p_m_method_3_3 == 'j') && (p_m_method_3_2 == 21));
	ensures (((p_m_method_3_1 == map[false := false, true := true]) && (p_m_method_3_3 == 'j') && (p_m_method_3_2 == 21)) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_seq_6: seq<char> := ['f', 'r', 'd'];
	var v_seq_7: seq<char> := v_seq_6;
	var v_int_13: int := 23;
	var v_int_14: int := safe_index_seq(v_seq_7, v_int_13);
	var v_int_15: int := v_int_14;
	var v_seq_8: seq<char> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_15 := 'W']) else (v_seq_6));
	var v_map_3: map<char, int> := map['u' := 3, 'm' := 11];
	var v_char_4: char := 'h';
	var v_int_16: int := (if ((v_char_4 in v_map_3)) then (v_map_3[v_char_4]) else (9));
	var v_seq_37: seq<char> := v_seq_8;
	var v_int_53: int := v_int_16;
	var v_int_54: int := safe_index_seq(v_seq_37, v_int_53);
	v_int_16 := v_int_54;
	var v_bool_int_3: (bool, int) := (false, 20);
	var v_bool_int_4: (bool, int) := v_bool_int_3;
	var v_DT_1_2_3: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_4: DT_1<bool, bool> := v_DT_1_2_3;
	var v_char_5: char := m_method_2(v_bool_int_4, v_DT_1_2_4);
	var v_map_4: map<char, char> := (map['e' := 'S', 'j' := 'z'] + map['J' := 'C', 'z' := 'X']);
	var v_bool_int_5: (bool, int) := (true, 27);
	var v_bool_int_6: (bool, int) := v_bool_int_5;
	var v_DT_1_2_5: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_6: DT_1<bool, bool> := v_DT_1_2_5;
	var v_char_6: char := m_method_2(v_bool_int_6, v_DT_1_2_6);
	var v_char_7: char := v_char_6;
	var v_seq_9: seq<char> := ['v', 'a', 'l', 'v'];
	var v_int_17: int := 12;
	v_char_5, v_char_7, v_char_6, v_char_4 := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_16]) else (v_char_5)), p_m_method_3_3, v_char_4, (if ((v_char_7 in v_map_4)) then (v_map_4[v_char_7]) else ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_17]) else ('M'))));
	var v_DT_1_1_1: DT_1<real, bool> := DT_1_1;
	var v_DT_1_1_2: DT_1<real, bool> := DT_1_1;
	var v_DT_1_1_3: DT_1<real, bool> := DT_1_1;
	var v_DT_1_1_4: DT_1<real, bool> := DT_1_1;
	var v_seq_10: seq<DT_1<real, bool>> := ([v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3, v_DT_1_1_4] + []);
	var v_int_18: int := (if (true) then (9) else (15));
	var v_seq_38: seq<DT_1<real, bool>> := v_seq_10;
	var v_int_55: int := v_int_18;
	var v_int_56: int := safe_index_seq(v_seq_38, v_int_55);
	v_int_18 := v_int_56;
	print "v_DT_1_2_6", " ", v_DT_1_2_6, " ", "v_bool_int_5.1", " ", v_bool_int_5.1, " ", "v_DT_1_2_5", " ", v_DT_1_2_5, " ", "v_bool_int_3.0", " ", v_bool_int_3.0, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_2_4", " ", v_DT_1_2_4, " ", "v_bool_int_5.0", " ", v_bool_int_5.0, " ", "v_bool_int_3.1", " ", v_bool_int_3.1, " ", "v_DT_1_2_3", " ", v_DT_1_2_3, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_18", " ", v_int_18, " ", "v_bool_int_3", " ", v_bool_int_3, " ", "v_seq_10", " ", v_seq_10, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "v_bool_int_5", " ", v_bool_int_5, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == map[false := false, true := true]), " ", "v_bool_int_4", " ", v_bool_int_4, " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'j'), " ", "v_bool_int_6", " ", v_bool_int_6, " ", "v_map_4", " ", (v_map_4 == map['e' := 'S', 'j' := 'z', 'J' := 'C', 'z' := 'X']), " ", "v_char_5", " ", (v_char_5 == 'W'), " ", "v_char_4", " ", (v_char_4 == 'z'), " ", "v_char_7", " ", (v_char_7 == 'j'), " ", "v_char_6", " ", (v_char_6 == 'h'), " ", "v_map_3", " ", (v_map_3 == map['u' := 3, 'm' := 11]), " ", "v_seq_9", " ", (v_seq_9 == ['v', 'a', 'l', 'v']), " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", (v_seq_8 == ['W', 'r', 'd']), " ", "v_seq_7", " ", (v_seq_7 == ['f', 'r', 'd']), " ", "v_seq_6", " ", (v_seq_6 == ['f', 'r', 'd']), " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, "\n";
	return (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_18]) else (v_DT_1_1_1));
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

method m_method_2(p_m_method_2_1: (bool, int), p_m_method_2_2: DT_1<bool, bool>) returns (ret_1: char)
	requires ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == -2)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 27)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 13)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 24)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == 5)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == 20)) || ((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 12));
	ensures (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 13)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 12)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == 20)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 27)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == -2)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == false) && ((p_m_method_2_1).1 == 5)) ==> ((ret_1 == 'j'))) && (((p_m_method_2_2.DT_1_2? && ((p_m_method_2_2 == DT_1_2))) && ((p_m_method_2_1).0 == true) && ((p_m_method_2_1).1 == 24)) ==> ((ret_1 == 'j')));
{
	match 26 {
		case 0 => {
			var v_int_9: int := 22;
			var v_int_10: int := 13;
			var v_int_11: int := 7;
			while (v_int_10 < v_int_11) 
				decreases v_int_11 - v_int_10;
				invariant (v_int_10 <= v_int_11);
			{
				v_int_10 := (v_int_10 + 1);
				return 'm';
			}
		}
			case _ => {
			print "p_m_method_2_1.0", " ", p_m_method_2_1.0, " ", "p_m_method_2_1.1", " ", p_m_method_2_1.1, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
			return 'j';
		}
		
	}
	
	return 'H';
}

method m_method_1(p_m_method_1_1: DT_1<real, int>) returns (ret_1: DT_1<real, bool>, ret_2: seq<real>, ret_3: char, ret_4: int, ret_5: char)
	requires ((p_m_method_1_1.DT_1_3? && ((p_m_method_1_1.DT_1_3_1 == 5) && (p_m_method_1_1.DT_1_3_2 == 3) && (p_m_method_1_1.DT_1_3_3 == 21) && (p_m_method_1_1.DT_1_3_4 == 15))));
	ensures (((p_m_method_1_1.DT_1_3? && ((p_m_method_1_1.DT_1_3_1 == 5) && (p_m_method_1_1.DT_1_3_2 == 3) && (p_m_method_1_1.DT_1_3_3 == 21) && (p_m_method_1_1.DT_1_3_4 == 15)))) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1))) && |ret_2| == 2 && (-2.48 < ret_2[0] < -2.28) && (-13.89 < ret_2[1] < -13.69) && (ret_3 == 'g') && (ret_4 == 27) && (ret_5 == 'O')));
{
	var v_seq_3: seq<set<bool>> := [{true, true}, {false, true, true}, {false, true, false}];
	var v_int_7: int := 10;
	var v_seq_35: seq<set<bool>> := v_seq_3;
	var v_int_49: int := v_int_7;
	var v_int_50: int := safe_index_seq(v_seq_35, v_int_49);
	v_int_7 := v_int_50;
	var v_map_1: map<int, set<bool>> := map[-12 := {false}, 22 := {true}, 23 := {true, false, false, true}, 28 := {true, true, false}];
	var v_int_8: int := 8;
	var v_real_real_bool_1: (real, real, bool) := (1.50, 23.93, true);
	var v_real_real_bool_2: (real, real, bool) := (12.02, -22.91, false);
	var v_real_real_bool_3: (real, real, bool) := (0.84, 28.97, true);
	var v_map_2: map<char, set<bool>> := map['O' := {false, false}, 'T' := {false, true, false, false}, 'P' := {false, false, true}, 'V' := {true, true, false, true}]['o' := {false, false}];
	var v_bool_int_1: (bool, int) := (true, 24);
	var v_bool_int_2: (bool, int) := v_bool_int_1;
	var v_DT_1_2_1: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_2: DT_1<bool, bool> := v_DT_1_2_1;
	var v_char_1: char := m_method_2(v_bool_int_2, v_DT_1_2_2);
	var v_char_2: char := v_char_1;
	var v_seq_4: seq<set<bool>> := [{false}, {true, true}, {true, false, true, true}, {}];
	var v_int_12: int := 27;
	var v_seq_36: seq<set<bool>> := v_seq_4;
	var v_int_51: int := v_int_12;
	var v_int_52: int := safe_index_seq(v_seq_36, v_int_51);
	v_int_12 := v_int_52;
	var v_seq_5: seq<set<bool>>, v_char_3: char := [((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else ({})) + (if ((v_int_8 in v_map_1)) then (v_map_1[v_int_8]) else ({}))), ({true} - (map[true := multiset{v_real_real_bool_1, v_real_real_bool_2}, false := multiset{v_real_real_bool_3}]).Keys), (if ((v_char_2 in v_map_2)) then (v_map_2[v_char_2]) else ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_12]) else ({false, true}))))], v_char_1;
	var v_char_12: char := v_char_3;
	var v_bool_int_7: (bool, int) := (false, -2);
	var v_bool_int_8: (bool, int) := v_bool_int_7;
	var v_DT_1_2_7: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_8: DT_1<bool, bool> := v_DT_1_2_7;
	var v_char_8: char := m_method_2(v_bool_int_8, v_DT_1_2_8);
	var v_char_13: char := v_char_8;
	var v_char_14: char := v_char_2;
	var v_char_9: char := 'm';
	var v_char_10: char := 'O';
	var v_char_11: char := m_method_5(v_char_9, v_char_10);
	var v_char_15: char := v_char_11;
	var v_map_5: map<bool, bool> := m_method_4(v_char_12, v_char_13, v_char_14, v_char_15);
	var v_map_6: map<bool, bool> := v_map_5;
	var v_array_1: array<char> := new char[3];
	v_array_1[0] := 'm';
	v_array_1[1] := 'p';
	v_array_1[2] := 'E';
	var v_seq_11: seq<int> := [];
	var v_int_19: int := 21;
	var v_int_20: int := (v_array_1.Length * (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_19]) else (7)));
	var v_char_16: char := (match 'D' {
		case 't' => v_char_14
		case _ => v_char_12
	});
	var v_DT_1_1_5: DT_1<real, bool> := m_method_3(v_map_6, v_int_20, v_char_16);
	var v_char_19: char := v_char_14;
	var v_bool_int_9: (bool, int) := (false, 5);
	var v_bool_int_10: (bool, int) := v_bool_int_9;
	var v_DT_1_2_9: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_10: DT_1<bool, bool> := v_DT_1_2_9;
	var v_char_17: char := m_method_2(v_bool_int_10, v_DT_1_2_10);
	var v_char_20: char := v_char_17;
	var v_bool_int_11: (bool, int) := (true, 12);
	var v_bool_int_12: (bool, int) := v_bool_int_11;
	var v_DT_1_2_11: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_12: DT_1<bool, bool> := v_DT_1_2_11;
	var v_char_18: char := m_method_2(v_bool_int_12, v_DT_1_2_12);
	var v_char_21: char := v_char_18;
	var v_seq_12: seq<seq<real>> := m_method_6(v_char_19, v_char_20, v_char_21);
	var v_seq_13: seq<seq<real>> := v_seq_12;
	var v_int_21: int := v_int_7;
	var v_seq_15: seq<real> := ([-21.58] + []);
	var v_seq_14: seq<int> := [26, 7];
	var v_int_22: int := 26;
	var v_map_7: map<char, seq<int>> := map['d' := [5, 26, 0, -9]];
	var v_char_22: char := 'I';
	var v_seq_16: seq<seq<int>> := [[10, 8, 13, 13], [5, 13], [28, 17, 4, 4], [1]];
	var v_int_23: int := 17;
	var v_seq_17: seq<int> := (if ((if (true) then (true) else (false))) then ((if ((v_char_22 in v_map_7)) then (v_map_7[v_char_22]) else ([27, 26]))) else ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_23]) else ([]))));
	var v_int_24: int := v_int_12;
	var v_seq_18: seq<real> := [14.89, 27.20, 29.69];
	var v_int_25: int := 12;
	var v_real_real_bool_4: (real, real, bool) := (0.84, 28.97, true);
	var v_real_real_bool_5: (real, real, bool) := (12.02, -22.91, false);
	var v_real_real_bool_6: (real, real, bool) := (1.50, 23.93, true);
	print "v_DT_1_2_8", " ", v_DT_1_2_8, " ", "v_DT_1_2_7", " ", v_DT_1_2_7, " ", "v_DT_1_2_2", " ", v_DT_1_2_2, " ", "v_DT_1_2_1", " ", v_DT_1_2_1, " ", "v_DT_1_2_9", " ", v_DT_1_2_9, " ", "v_real_real_bool_1.1", " ", (v_real_real_bool_1.1 == 23.93), " ", "v_real_real_bool_1.2", " ", v_real_real_bool_1.2, " ", "v_real_real_bool_3.0", " ", (v_real_real_bool_3.0 == 0.84), " ", "v_real_real_bool_3.1", " ", (v_real_real_bool_3.1 == 28.97), " ", "v_real_real_bool_3.2", " ", v_real_real_bool_3.2, " ", "v_array_1[2]", " ", (v_array_1[2] == 'E'), " ", "p_m_method_1_1.DT_1_3_1", " ", p_m_method_1_1.DT_1_3_1, " ", "p_m_method_1_1.DT_1_3_2", " ", p_m_method_1_1.DT_1_3_2, " ", "p_m_method_1_1.DT_1_3_3", " ", p_m_method_1_1.DT_1_3_3, " ", "p_m_method_1_1.DT_1_3_4", " ", p_m_method_1_1.DT_1_3_4, " ", "v_real_real_bool_1.0", " ", (v_real_real_bool_1.0 == 1.50), " ", "v_real_real_bool_3", " ", (v_real_real_bool_3 == v_real_real_bool_4), " ", "v_real_real_bool_2", " ", (v_real_real_bool_2 == v_real_real_bool_5), " ", "v_real_real_bool_1", " ", (v_real_real_bool_1 == v_real_real_bool_6), " ", "v_char_22", " ", (v_char_22 == 'I'), " ", "v_DT_1_2_12", " ", v_DT_1_2_12, " ", "v_DT_1_2_11", " ", v_DT_1_2_11, " ", "v_DT_1_2_10", " ", v_DT_1_2_10, " ", "v_bool_int_9.1", " ", v_bool_int_9.1, " ", "v_bool_int_7.0", " ", v_bool_int_7.0, " ", "v_char_18", " ", (v_char_18 == 'j'), " ", "v_char_17", " ", (v_char_17 == 'j'), " ", "v_char_16", " ", (v_char_16 == 'j'), " ", "v_bool_int_9.0", " ", v_bool_int_9.0, " ", "v_bool_int_7.1", " ", v_bool_int_7.1, " ", "v_char_15", " ", (v_char_15 == 'g'), " ", "v_char_14", " ", (v_char_14 == 'j'), " ", "v_bool_int_1.1", " ", v_bool_int_1.1, " ", "v_char_13", " ", (v_char_13 == 'j'), " ", "v_char_12", " ", (v_char_12 == 'j'), " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_char_11", " ", (v_char_11 == 'g'), " ", "v_bool_int_1.0", " ", v_bool_int_1.0, " ", "v_int_19", " ", v_int_19, " ", "v_seq_18", " ", (v_seq_18 == [14.89, 27.20, 29.69]), " ", "v_char_19", " ", (v_char_19 == 'j'), " ", "v_real_real_bool_2.0", " ", (v_real_real_bool_2.0 == 12.02), " ", "v_bool_int_1", " ", v_bool_int_1, " ", "v_seq_14", " ", v_seq_14, " ", "v_int_24", " ", v_int_24, " ", "v_real_real_bool_2.1", " ", (v_real_real_bool_2.1 == -22.91), " ", "v_seq_15", " ", (v_seq_15 == [-21.58]), " ", "v_int_23", " ", v_int_23, " ", "v_real_real_bool_2.2", " ", v_real_real_bool_2.2, " ", "v_int_22", " ", v_int_22, " ", "v_seq_16", " ", v_seq_16, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_bool_int_2", " ", v_bool_int_2, " ", "v_int_21", " ", v_int_21, " ", "v_seq_17", " ", v_seq_17, " ", "v_seq_11", " ", v_seq_11, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_seq_12", " ", (v_seq_12 == [[-2.38, -13.79], [5.84], [-3.60], []]), " ", "v_seq_13", " ", (v_seq_13 == [[-2.38, -13.79], [5.84], [-3.60], []]), " ", "v_int_25", " ", v_int_25, " ", "v_bool_int_9", " ", v_bool_int_9, " ", "v_char_21", " ", (v_char_21 == 'j'), " ", "v_bool_int_8", " ", v_bool_int_8, " ", "v_char_20", " ", (v_char_20 == 'j'), " ", "v_bool_int_10", " ", v_bool_int_10, " ", "v_array_1[0]", " ", (v_array_1[0] == 'm'), " ", "v_int_20", " ", v_int_20, " ", "v_bool_int_12", " ", v_bool_int_12, " ", "v_bool_int_11", " ", v_bool_int_11, " ", "v_bool_int_7", " ", v_bool_int_7, " ", "v_char_1", " ", (v_char_1 == 'j'), " ", "v_map_5", " ", (v_map_5 == map[false := false, true := true]), " ", "v_char_3", " ", (v_char_3 == 'j'), " ", "v_map_7", " ", (v_map_7 == map['d' := [5, 26, 0, -9]]), " ", "v_char_2", " ", (v_char_2 == 'j'), " ", "v_map_6", " ", (v_map_6 == map[false := false, true := true]), " ", "v_int_8", " ", v_int_8, " ", "v_char_9", " ", (v_char_9 == 'm'), " ", "v_bool_int_11.1", " ", v_bool_int_11.1, " ", "v_int_7", " ", v_int_7, " ", "v_char_8", " ", (v_char_8 == 'j'), " ", "v_bool_int_11.0", " ", v_bool_int_11.0, " ", "v_map_1", " ", (v_map_1 == map[22 := {true}, 23 := {false, true}, -12 := {false}, 28 := {false, true}]), " ", "v_map_2", " ", (v_map_2 == map['P' := {false, true}, 'T' := {false, true}, 'V' := {false, true}, 'O' := {false}, 'o' := {false}]), " ", "v_int_12", " ", v_int_12, " ", "v_seq_5", " ", (v_seq_5 == [{true}, {}, {false}]), " ", "v_seq_4", " ", (v_seq_4 == [{false}, {true}, {false, true}, {}]), " ", "v_seq_3", " ", (v_seq_3 == [{true}, {false, true}, {false, true}]), " ", "v_char_10", " ", (v_char_10 == 'O'), " ", "v_array_1[1]", " ", (v_array_1[1] == 'p'), "\n";
	return v_DT_1_1_5, (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_21]) else ((if ((|v_seq_15| > 0)) then (v_seq_15[(if ((|v_seq_14| > 0)) then (v_seq_14[v_int_22]) else (22))..(if (true) then (28) else (1))]) else (v_seq_15)))), v_char_11, (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_24]) else (((if ((|v_seq_18| > 0)) then (v_seq_18[v_int_25]) else (-3.62))).Floor)), (if (v_real_real_bool_3.2) then (v_char_10) else (v_array_1[0]));
}

method Main() returns ()
{
	var v_char_26: char := 'I';
	var v_seq_19: seq<DT_1<real, int>> := m_method_7(v_char_26);
	var v_seq_20: seq<DT_1<real, int>> := v_seq_19;
	var v_array_2: array<char> := new char[5] ['C', 'Y', 'F', 'P', 'M'];
	var v_int_29: int := v_array_2.Length;
	var v_DT_1_3_2: DT_1<real, int> := DT_1_3(25, 24, 17, 19);
	var v_DT_1_3_3: DT_1<real, int> := DT_1_3(12, -16, -15, 2);
	var v_seq_24: seq<char> := ['K', 'm', 'd'];
	var v_int_33: int := 13;
	var v_seq_31: seq<char> := v_seq_24;
	var v_int_41: int := v_int_33;
	var v_int_42: int := safe_index_seq(v_seq_31, v_int_41);
	v_int_33 := v_int_42;
	var v_char_32: char := (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_33]) else ('V'));
	var v_seq_25: seq<char> := ['X', 'v', 'a', 'T'];
	var v_int_34: int := -5;
	var v_seq_32: seq<char> := v_seq_25;
	var v_int_43: int := v_int_34;
	var v_int_44: int := safe_index_seq(v_seq_32, v_int_43);
	v_int_34 := v_int_44;
	var v_char_33: char := (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_34]) else ('o'));
	var v_bool_int_13: (bool, int) := (true, 13);
	var v_bool_int_14: (bool, int) := v_bool_int_13;
	var v_DT_1_2_13: DT_1<bool, bool> := DT_1_2;
	var v_DT_1_2_14: DT_1<bool, bool> := v_DT_1_2_13;
	var v_char_30: char := m_method_2(v_bool_int_14, v_DT_1_2_14);
	var v_char_34: char := v_char_30;
	var v_map_8: map<char, char> := map['f' := 'X', 'g' := 'Q', 'i' := 'i', 't' := 'm', 'j' := 'u'];
	var v_char_31: char := 'e';
	var v_char_35: char := (if ((v_char_31 in v_map_8)) then (v_map_8[v_char_31]) else ('n'));
	var v_DT_1_3_5: DT_1<real, int> := m_method_8(v_char_32, v_char_33, v_char_34, v_char_35);
	var v_DT_1_3_6: DT_1<real, int> := DT_1_3(-10, 11, 24, 6);
	var v_DT_1_3_7: DT_1<real, int> := DT_1_3(17, 25, 0, 5);
	var v_DT_1_3_8: DT_1<real, int> := DT_1_3(18, 15, 14, 15);
	var v_seq_26: seq<DT_1<real, int>> := [v_DT_1_3_6, v_DT_1_3_7, v_DT_1_3_8];
	var v_seq_27: seq<DT_1<real, int>> := v_seq_26;
	var v_int_35: int := 10;
	var v_int_36: int := safe_index_seq(v_seq_27, v_int_35);
	var v_int_37: int := v_int_36;
	var v_DT_1_3_9: DT_1<real, int> := DT_1_3(5, 3, 21, 15);
	var v_seq_28: seq<DT_1<real, int>> := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_37 := v_DT_1_3_9]) else (v_seq_26));
	var v_int_38: int := (if (true) then (29) else (9));
	var v_seq_34: seq<DT_1<real, int>> := v_seq_28;
	var v_int_47: int := v_int_38;
	var v_int_48: int := safe_index_seq(v_seq_34, v_int_47);
	v_int_38 := v_int_48;
	var v_DT_1_3_10: DT_1<real, int> := DT_1_3(17, 25, -26, 16);
	var v_DT_1_3_11: DT_1<real, int> := DT_1_3(29, 29, 29, 3);
	var v_DT_1_3_12: DT_1<real, int> := DT_1_3(29, 17, 1, 21);
	var v_DT_1_3_13: DT_1<real, int> := DT_1_3(20, 17, 4, 12);
	var v_seq_29: seq<DT_1<real, int>> := [v_DT_1_3_10, v_DT_1_3_11, v_DT_1_3_12, v_DT_1_3_13];
	var v_int_39: int := 21;
	var v_DT_1_3_14: DT_1<real, int> := DT_1_3(8, 14, -17, 15);
	var v_DT_1_3_15: DT_1<real, int> := (match 'B' {
		case 'z' => (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_29]) else ((if (true) then (v_DT_1_3_2) else (v_DT_1_3_3))))
		case 'L' => v_DT_1_3_5
		case _ => (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_38]) else ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_39]) else (v_DT_1_3_14))))
	});
	var v_DT_1_1_6: DT_1<real, bool>, v_seq_30: seq<real>, v_char_36: char, v_int_40: int, v_char_37: char := m_method_1(v_DT_1_3_15);
	v_DT_1_1_6, v_seq_30, v_char_36, v_int_40, v_char_37 := v_DT_1_1_6, v_seq_30, v_char_36, v_int_40, v_char_37;
	print "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_char_37", " ", (v_char_37 == 'O'), " ", "v_char_36", " ", (v_char_36 == 'g'), " ", "v_DT_1_3_15", " ", v_DT_1_3_15, " ", "v_seq_30", " ", (v_seq_30 == [-2.38, -13.79]), " ", "v_int_40", " ", v_int_40, "\n";
}
