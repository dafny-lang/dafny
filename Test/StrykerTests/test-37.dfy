// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1
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

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: char, p_m_method_3_3: int, p_m_method_3_4: int) returns (ret_1: bool)
	requires ((p_m_method_3_1 == 29) && (p_m_method_3_3 == 21) && (p_m_method_3_2 == 'N') && (p_m_method_3_4 == 2));
	ensures (((p_m_method_3_1 == 29) && (p_m_method_3_3 == 21) && (p_m_method_3_2 == 'N') && (p_m_method_3_4 == 2)) ==> ((ret_1 == true)));
{
	var v_int_17: int, v_int_18: int := 28, 27;
	if true {
		print "v_int_17", " ", v_int_17, " ", "v_int_18", " ", v_int_18, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'N'), " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", p_m_method_3_4, " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
		return true;
	}
	return false;
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

method m_method_2(p_m_method_2_1: bool) returns (ret_1: char)
{
	var v_int_10: int, v_int_11: int := 3, 19;
	for v_int_9 := v_int_10 to v_int_11 
		invariant (v_int_11 - v_int_9 >= 0)
	{
		return 'x';
	}
	return 'b';
}

method m_method_1(p_m_method_1_1: array<bool>) returns (ret_1: array<(bool, (bool, real, real), int)>)
	requires (p_m_method_1_1.Length == 4 && (p_m_method_1_1[0] == false) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == false) && (p_m_method_1_1[3] == true));
	ensures ((p_m_method_1_1.Length == 4 && (p_m_method_1_1[0] == false) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == false) && (p_m_method_1_1[3] == true)) ==> (ret_1.Length == 4 && ((ret_1[0]).0 == true) && (((ret_1[0]).1).0 == true) && (-1.74 < ((ret_1[0]).1).1 < -1.54) && (2.54 < ((ret_1[0]).1).2 < 2.74) && ((ret_1[0]).2 == 26) && ((ret_1[1]).0 == false) && (((ret_1[1]).1).0 == true) && (19.75 < ((ret_1[1]).1).1 < 19.95) && (-1.17 < ((ret_1[1]).1).2 < -0.97) && ((ret_1[1]).2 == 27) && ((ret_1[2]).0 == true) && (((ret_1[2]).1).0 == false) && (7.47 < ((ret_1[2]).1).1 < 7.67) && (-13.94 < ((ret_1[2]).1).2 < -13.74) && ((ret_1[2]).2 == 0) && ((ret_1[3]).0 == false) && (((ret_1[3]).1).0 == false) && (-16.13 < ((ret_1[3]).1).1 < -15.93) && (-29.03 < ((ret_1[3]).1).2 < -28.83) && ((ret_1[3]).2 == 16)));
	modifies p_m_method_1_1;
{
	var v_int_7: int := (if (true) then (20) else (27));
	var v_int_8: int := (-1 / 6);
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8) && ((((v_int_7 == 20)) ==> ((((p_m_method_1_1[0] == false))))));
	{
		v_int_7 := (v_int_7 + 1);
		var v_bool_1: bool := true;
		var v_char_1: char := m_method_2(v_bool_1);
		var v_seq_3: seq<int> := [9];
		var v_int_12: int := 15;
		var v_DT_1_1_1: DT_1 := DT_1_1;
		p_m_method_1_1[0], v_char_1, v_int_12, v_DT_1_1_1, v_bool_1 := p_m_method_1_1[0], v_char_1, (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_12]) else (12)), v_DT_1_1_1, v_bool_1;
		break;
	}
	var v_array_1: array<(bool, (bool, real, real), int)> := new (bool, (bool, real, real), int)[5];
	var v_bool_real_real_1: (bool, real, real) := (true, -17.39, 13.06);
	var v_bool_bool_real_real_int_1: (bool, (bool, real, real), int) := (true, v_bool_real_real_1, 2);
	v_array_1[0] := v_bool_bool_real_real_int_1;
	var v_bool_real_real_2: (bool, real, real) := (false, -29.07, -9.33);
	var v_bool_bool_real_real_int_2: (bool, (bool, real, real), int) := (false, v_bool_real_real_2, 6);
	v_array_1[1] := v_bool_bool_real_real_int_2;
	var v_bool_real_real_3: (bool, real, real) := (true, 18.99, 18.95);
	var v_bool_bool_real_real_int_3: (bool, (bool, real, real), int) := (true, v_bool_real_real_3, 2);
	v_array_1[2] := v_bool_bool_real_real_int_3;
	var v_bool_real_real_4: (bool, real, real) := (false, 18.06, 6.87);
	var v_bool_bool_real_real_int_4: (bool, (bool, real, real), int) := (false, v_bool_real_real_4, -28);
	v_array_1[3] := v_bool_bool_real_real_int_4;
	var v_bool_real_real_5: (bool, real, real) := (true, -23.29, 29.38);
	var v_bool_bool_real_real_int_5: (bool, (bool, real, real), int) := (false, v_bool_real_real_5, 22);
	v_array_1[4] := v_bool_bool_real_real_int_5;
	var v_map_1: map<bool, array<(bool, (bool, real, real), int)>> := map[false := v_array_1];
	var v_bool_2: bool := true;
	var v_bool_real_real_6: (bool, real, real) := (true, -1.64, 2.64);
	var v_bool_bool_real_real_int_6: (bool, (bool, real, real), int) := (true, v_bool_real_real_6, 26);
	var v_bool_real_real_7: (bool, real, real) := (true, 19.85, -1.07);
	var v_bool_bool_real_real_int_7: (bool, (bool, real, real), int) := (false, v_bool_real_real_7, 27);
	var v_bool_real_real_8: (bool, real, real) := (false, 7.57, -13.84);
	var v_bool_bool_real_real_int_8: (bool, (bool, real, real), int) := (true, v_bool_real_real_8, 0);
	var v_bool_real_real_9: (bool, real, real) := (false, -16.03, -28.93);
	var v_bool_bool_real_real_int_9: (bool, (bool, real, real), int) := (false, v_bool_real_real_9, 16);
	var v_array_2: array<(bool, (bool, real, real), int)> := new (bool, (bool, real, real), int)[4] [v_bool_bool_real_real_int_6, v_bool_bool_real_real_int_7, v_bool_bool_real_real_int_8, v_bool_bool_real_real_int_9];
	var v_bool_real_real_10: (bool, real, real) := (false, -16.03, -28.93);
	var v_bool_bool_real_real_int_10: (bool, (bool, real, real), int) := (false, v_bool_real_real_10, 16);
	var v_bool_real_real_11: (bool, real, real) := (true, -1.64, 2.64);
	var v_bool_real_real_12: (bool, real, real) := (false, 7.57, -13.84);
	var v_bool_real_real_13: (bool, real, real) := (true, 18.99, 18.95);
	var v_bool_bool_real_real_int_11: (bool, (bool, real, real), int) := (true, v_bool_real_real_13, 2);
	var v_bool_real_real_14: (bool, real, real) := (false, -16.03, -28.93);
	var v_bool_bool_real_real_int_12: (bool, (bool, real, real), int) := (false, v_bool_real_real_14, 16);
	var v_bool_real_real_15: (bool, real, real) := (true, -17.39, 13.06);
	var v_bool_bool_real_real_int_13: (bool, (bool, real, real), int) := (true, v_bool_real_real_15, 2);
	var v_bool_real_real_16: (bool, real, real) := (false, -29.07, -9.33);
	var v_bool_bool_real_real_int_14: (bool, (bool, real, real), int) := (false, v_bool_real_real_16, 6);
	var v_bool_real_real_17: (bool, real, real) := (false, -29.07, -9.33);
	var v_bool_real_real_18: (bool, real, real) := (true, 18.99, 18.95);
	var v_bool_bool_real_real_int_15: (bool, (bool, real, real), int) := (true, v_bool_real_real_18, 2);
	var v_bool_real_real_19: (bool, real, real) := (false, 18.06, 6.87);
	var v_bool_bool_real_real_int_16: (bool, (bool, real, real), int) := (false, v_bool_real_real_19, -28);
	var v_bool_real_real_20: (bool, real, real) := (false, 18.06, 6.87);
	var v_bool_real_real_21: (bool, real, real) := (true, -23.29, 29.38);
	var v_bool_bool_real_real_int_17: (bool, (bool, real, real), int) := (false, v_bool_real_real_21, 22);
	var v_bool_real_real_22: (bool, real, real) := (true, -1.64, 2.64);
	var v_bool_bool_real_real_int_18: (bool, (bool, real, real), int) := (true, v_bool_real_real_22, 26);
	var v_bool_real_real_23: (bool, real, real) := (true, 19.85, -1.07);
	var v_bool_bool_real_real_int_19: (bool, (bool, real, real), int) := (false, v_bool_real_real_23, 27);
	var v_bool_real_real_24: (bool, real, real) := (false, 7.57, -13.84);
	var v_bool_bool_real_real_int_20: (bool, (bool, real, real), int) := (true, v_bool_real_real_24, 0);
	var v_bool_real_real_25: (bool, real, real) := (true, -1.64, 2.64);
	var v_bool_bool_real_real_int_21: (bool, (bool, real, real), int) := (true, v_bool_real_real_25, 26);
	var v_bool_real_real_26: (bool, real, real) := (false, 18.06, 6.87);
	var v_bool_bool_real_real_int_22: (bool, (bool, real, real), int) := (false, v_bool_real_real_26, -28);
	var v_bool_real_real_27: (bool, real, real) := (true, 19.85, -1.07);
	var v_bool_real_real_28: (bool, real, real) := (false, -16.03, -28.93);
	var v_bool_real_real_29: (bool, real, real) := (true, 19.85, -1.07);
	var v_bool_bool_real_real_int_23: (bool, (bool, real, real), int) := (false, v_bool_real_real_29, 27);
	var v_bool_real_real_30: (bool, real, real) := (true, -17.39, 13.06);
	var v_bool_bool_real_real_int_24: (bool, (bool, real, real), int) := (true, v_bool_real_real_30, 2);
	var v_bool_real_real_31: (bool, real, real) := (true, -23.29, 29.38);
	var v_bool_bool_real_real_int_25: (bool, (bool, real, real), int) := (false, v_bool_real_real_31, 22);
	var v_bool_real_real_32: (bool, real, real) := (true, 18.99, 18.95);
	var v_bool_real_real_33: (bool, real, real) := (true, -23.29, 29.38);
	var v_bool_real_real_34: (bool, real, real) := (false, -29.07, -9.33);
	var v_bool_real_real_35: (bool, real, real) := (true, 18.99, 18.95);
	var v_bool_real_real_36: (bool, real, real) := (true, -17.39, 13.06);
	var v_bool_real_real_37: (bool, real, real) := (true, -17.39, 13.06);
	var v_bool_real_real_38: (bool, real, real) := (false, -29.07, -9.33);
	var v_bool_bool_real_real_int_26: (bool, (bool, real, real), int) := (false, v_bool_real_real_38, 6);
	var v_bool_real_real_39: (bool, real, real) := (true, -1.64, 2.64);
	var v_bool_real_real_40: (bool, real, real) := (true, 19.85, -1.07);
	var v_bool_real_real_41: (bool, real, real) := (false, 18.06, 6.87);
	var v_bool_real_real_42: (bool, real, real) := (true, -23.29, 29.38);
	var v_bool_real_real_43: (bool, real, real) := (false, 7.57, -13.84);
	var v_bool_real_real_44: (bool, real, real) := (false, 7.57, -13.84);
	var v_bool_bool_real_real_int_27: (bool, (bool, real, real), int) := (true, v_bool_real_real_44, 0);
	var v_bool_real_real_45: (bool, real, real) := (false, -16.03, -28.93);
	print "p_m_method_1_1[2]", " ", p_m_method_1_1[2], " ", "v_bool_real_real_8.1", " ", (v_bool_real_real_8.1 == 7.57), " ", "v_bool_bool_real_real_int_9", " ", (v_bool_bool_real_real_int_9 == v_bool_bool_real_real_int_10), " ", "v_bool_real_real_6.2", " ", (v_bool_real_real_6.2 == 2.64), " ", "v_bool_real_real_8.0", " ", v_bool_real_real_8.0, " ", "v_bool_real_real_6.1", " ", (v_bool_real_real_6.1 == -1.64), " ", "v_bool_real_real_4.2", " ", (v_bool_real_real_4.2 == 6.87), " ", "v_bool_real_real_6.0", " ", v_bool_real_real_6.0, " ", "v_bool_real_real_4.1", " ", (v_bool_real_real_4.1 == 18.06), " ", "v_bool_bool_real_real_int_6.2", " ", v_bool_bool_real_real_int_6.2, " ", "v_bool_bool_real_real_int_8.0", " ", v_bool_bool_real_real_int_8.0, " ", "v_bool_real_real_2.2", " ", (v_bool_real_real_2.2 == -9.33), " ", "v_bool_real_real_4.0", " ", v_bool_real_real_4.0, " ", "v_bool_bool_real_real_int_6.1", " ", (v_bool_bool_real_real_int_6.1 == v_bool_real_real_11), " ", "v_bool_real_real_2.1", " ", (v_bool_real_real_2.1 == -29.07), " ", "v_bool_bool_real_real_int_8.2", " ", v_bool_bool_real_real_int_8.2, " ", "v_bool_real_real_2.0", " ", v_bool_real_real_2.0, " ", "v_bool_bool_real_real_int_8.1", " ", (v_bool_bool_real_real_int_8.1 == v_bool_real_real_12), " ", "v_bool_real_real_8.2", " ", (v_bool_real_real_8.2 == -13.84), " ", "v_array_1[2]", " ", (v_array_1[2] == v_bool_bool_real_real_int_11), " ", "v_array_2[3]", " ", (v_array_2[3] == v_bool_bool_real_real_int_12), " ", "v_bool_bool_real_real_int_1", " ", (v_bool_bool_real_real_int_1 == v_bool_bool_real_real_int_13), " ", "v_bool_bool_real_real_int_2.2", " ", v_bool_bool_real_real_int_2.2, " ", "v_bool_bool_real_real_int_4.0", " ", v_bool_bool_real_real_int_4.0, " ", "v_bool_bool_real_real_int_2", " ", (v_bool_bool_real_real_int_2 == v_bool_bool_real_real_int_14), " ", "v_bool_bool_real_real_int_2.1", " ", (v_bool_bool_real_real_int_2.1 == v_bool_real_real_17), " ", "v_bool_bool_real_real_int_3", " ", (v_bool_bool_real_real_int_3 == v_bool_bool_real_real_int_15), " ", "v_bool_bool_real_real_int_4.2", " ", v_bool_bool_real_real_int_4.2, " ", "v_bool_bool_real_real_int_6.0", " ", v_bool_bool_real_real_int_6.0, " ", "v_bool_bool_real_real_int_4", " ", (v_bool_bool_real_real_int_4 == v_bool_bool_real_real_int_16), " ", "v_bool_bool_real_real_int_4.1", " ", (v_bool_bool_real_real_int_4.1 == v_bool_real_real_20), " ", "v_bool_bool_real_real_int_5", " ", (v_bool_bool_real_real_int_5 == v_bool_bool_real_real_int_17), " ", "v_bool_bool_real_real_int_6", " ", (v_bool_bool_real_real_int_6 == v_bool_bool_real_real_int_18), " ", "v_bool_bool_real_real_int_2.0", " ", v_bool_bool_real_real_int_2.0, " ", "v_bool_bool_real_real_int_7", " ", (v_bool_bool_real_real_int_7 == v_bool_bool_real_real_int_19), " ", "v_bool_bool_real_real_int_8", " ", (v_bool_bool_real_real_int_8 == v_bool_bool_real_real_int_20), " ", "v_array_2[0]", " ", (v_array_2[0] == v_bool_bool_real_real_int_21), " ", "v_array_1[3]", " ", (v_array_1[3] == v_bool_bool_real_real_int_22), " ", "v_bool_real_real_1.0", " ", v_bool_real_real_1.0, " ", "v_bool_2", " ", v_bool_2, " ", "p_m_method_1_1[0]", " ", p_m_method_1_1[0], " ", "v_bool_real_real_7.2", " ", (v_bool_real_real_7.2 == -1.07), " ", "v_bool_real_real_9.0", " ", v_bool_real_real_9.0, " ", "v_bool_real_real_7.1", " ", (v_bool_real_real_7.1 == 19.85), " ", "v_bool_bool_real_real_int_9.2", " ", v_bool_bool_real_real_int_9.2, " ", "v_bool_real_real_5.2", " ", (v_bool_real_real_5.2 == 29.38), " ", "v_bool_real_real_7.0", " ", v_bool_real_real_7.0, " ", "v_bool_real_real_5.1", " ", (v_bool_real_real_5.1 == -23.29), " ", "v_bool_real_real_3.2", " ", (v_bool_real_real_3.2 == 18.95), " ", "v_bool_real_real_5.0", " ", v_bool_real_real_5.0, " ", "v_bool_bool_real_real_int_7.1", " ", (v_bool_bool_real_real_int_7.1 == v_bool_real_real_27), " ", "v_bool_real_real_3.1", " ", (v_bool_real_real_3.1 == 18.99), " ", "v_bool_bool_real_real_int_5.2", " ", v_bool_bool_real_real_int_5.2, " ", "v_bool_bool_real_real_int_7.0", " ", v_bool_bool_real_real_int_7.0, " ", "v_bool_real_real_1.2", " ", (v_bool_real_real_1.2 == 13.06), " ", "v_bool_real_real_3.0", " ", v_bool_real_real_3.0, " ", "v_bool_bool_real_real_int_9.1", " ", (v_bool_bool_real_real_int_9.1 == v_bool_real_real_28), " ", "v_bool_real_real_1.1", " ", (v_bool_real_real_1.1 == -17.39), " ", "v_bool_bool_real_real_int_7.2", " ", v_bool_bool_real_real_int_7.2, " ", "v_bool_bool_real_real_int_9.0", " ", v_bool_bool_real_real_int_9.0, " ", "p_m_method_1_1", " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_bool_real_real_9.2", " ", (v_bool_real_real_9.2 == -28.93), " ", "v_bool_real_real_9.1", " ", (v_bool_real_real_9.1 == -16.03), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[1]", " ", (v_array_2[1] == v_bool_bool_real_real_int_23), " ", "v_array_1[0]", " ", (v_array_1[0] == v_bool_bool_real_real_int_24), " ", "v_array_1[4]", " ", (v_array_1[4] == v_bool_bool_real_real_int_25), " ", "p_m_method_1_1[1]", " ", p_m_method_1_1[1], " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[false := v_array_1]), " ", "v_bool_bool_real_real_int_3.1", " ", (v_bool_bool_real_real_int_3.1 == v_bool_real_real_32), " ", "v_bool_bool_real_real_int_1.2", " ", v_bool_bool_real_real_int_1.2, " ", "v_bool_bool_real_real_int_3.0", " ", v_bool_bool_real_real_int_3.0, " ", "v_bool_bool_real_real_int_5.1", " ", (v_bool_bool_real_real_int_5.1 == v_bool_real_real_33), " ", "v_bool_bool_real_real_int_3.2", " ", v_bool_bool_real_real_int_3.2, " ", "v_bool_bool_real_real_int_5.0", " ", v_bool_bool_real_real_int_5.0, " ", "v_bool_real_real_2", " ", (v_bool_real_real_2 == v_bool_real_real_34), " ", "v_bool_real_real_3", " ", (v_bool_real_real_3 == v_bool_real_real_35), " ", "v_bool_bool_real_real_int_1.1", " ", (v_bool_bool_real_real_int_1.1 == v_bool_real_real_36), " ", "v_bool_real_real_1", " ", (v_bool_real_real_1 == v_bool_real_real_37), " ", "v_bool_bool_real_real_int_1.0", " ", v_bool_bool_real_real_int_1.0, " ", "v_array_1[1]", " ", (v_array_1[1] == v_bool_bool_real_real_int_26), " ", "v_bool_real_real_6", " ", (v_bool_real_real_6 == v_bool_real_real_39), " ", "v_bool_real_real_7", " ", (v_bool_real_real_7 == v_bool_real_real_40), " ", "v_bool_real_real_4", " ", (v_bool_real_real_4 == v_bool_real_real_41), " ", "v_bool_real_real_5", " ", (v_bool_real_real_5 == v_bool_real_real_42), " ", "v_bool_real_real_8", " ", (v_bool_real_real_8 == v_bool_real_real_43), " ", "v_array_2[2]", " ", (v_array_2[2] == v_bool_bool_real_real_int_27), " ", "v_bool_real_real_9", " ", (v_bool_real_real_9 == v_bool_real_real_45), "\n";
	return (if ((v_bool_2 in v_map_1)) then (v_map_1[v_bool_2]) else (v_array_2));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_array_3: array<bool> := new bool[4] [false, false, false, true];
	var v_array_4: array<bool> := new bool[4] [true, true, false, false];
	var v_array_5: array<bool> := new bool[3];
	v_array_5[0] := false;
	v_array_5[1] := false;
	v_array_5[2] := false;
	var v_seq_4: seq<array<bool>> := [v_array_3, v_array_4, v_array_5];
	var v_int_13: int := 8;
	var v_seq_6: seq<array<bool>> := v_seq_4;
	var v_int_24: int := v_int_13;
	var v_int_25: int := safe_index_seq(v_seq_6, v_int_24);
	v_int_13 := v_int_25;
	var v_array_6: array<bool> := new bool[3] [false, true, true];
	var v_array_7: array<bool> := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_13]) else (v_array_6));
	var v_array_8: array<(bool, (bool, real, real), int)> := m_method_1(v_array_7);
	v_int_13 := v_array_8.Length;
	var v_map_2: map<set<map<int, real>>, int> := map[{map[22 := -13.75, 2 := 29.79, 20 := -18.64, -15 := -7.72, 13 := -6.50], map[12 := 0.68, -7 := -1.85, 29 := 22.74, 4 := -7.92, 16 := 2.51], map[3 := 27.96, 20 := 0.07, 12 := 18.43]} := 23, {} := 28, {map[15 := -24.30, 8 := -6.40], map[24 := 9.87, 0 := -23.51, 27 := 20.58, 3 := 10.17, 25 := 17.79], map[11 := 11.24, 22 := 15.35], map[27 := 13.00, 15 := -19.52, -6 := 19.08, 22 := 27.68, 24 := -3.85]} := 13, {map[22 := -2.40], map[28 := 19.58, 3 := -27.22, 23 := 18.45]} := -26];
	var v_set_1: set<map<int, real>> := {map[23 := 14.48, 24 := -0.92, 1 := 17.47], map[14 := -19.35, 28 := -24.39]};
	var v_int_15: int, v_int_16: int := v_int_13, (match false {
		case true => ((if (true) then (5) else (-17)) - (if ((v_set_1 in v_map_2)) then (v_map_2[v_set_1]) else (28)))
		case _ => v_int_13
	});
	for v_int_14 := v_int_15 downto v_int_16 
		invariant (v_int_14 - v_int_16 >= 0)
	{
		break;
	}
	var v_int_26: int := (v_int_15 / v_int_13);
	var v_int_19: int := 29;
	var v_char_2: char := 'N';
	var v_int_20: int := 21;
	var v_int_21: int := 2;
	var v_bool_3: bool := m_method_3(v_int_19, v_char_2, v_int_20, v_int_21);
	var v_seq_5: seq<int> := [6, 29, 12, 9];
	var v_int_22: int := 28;
	var v_int_23: int := safe_index_seq(v_seq_5, v_int_22);
	var v_int_27: int := (if (v_bool_3) then (v_int_23) else ((27 - 4)));
	var v_int_28: int := safe_modulus(v_int_26, v_int_27);
	v_int_13 := v_int_28;
	print "v_array_6[2]", " ", v_array_6[2], " ", "v_bool_3", " ", v_bool_3, " ", "v_int_19", " ", v_int_19, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_int_23", " ", v_int_23, " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_int_22", " ", v_int_22, " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_int_21", " ", v_int_21, " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_array_5[0]", " ", v_array_5[0], " ", "v_array_7", " ", (v_array_7 == v_array_3), " ", "v_int_20", " ", v_int_20, " ", "v_array_8", " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_array_5[2]", " ", v_array_5[2], " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_array_6[1]", " ", v_array_6[1], " ", "v_char_2", " ", (v_char_2 == 'N'), " ", "v_int_13", " ", v_int_13, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", (v_seq_4 == [v_array_3, v_array_4, v_array_5]), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_6[0]", " ", v_array_6[0], " ", "v_array_4[2]", " ", v_array_4[2], " ", "v_array_5[1]", " ", v_array_5[1], "\n";
}
