// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1 | DT_1_2(DT_1_2_1: bool, DT_1_2_2: real, DT_1_2_3: bool)
datatype DT_2<T_1> = DT_2_1 | DT_2_3
datatype DT_3<T_2, T_3> = DT_3_1 | DT_3_3(DT_3_3_1: map<int, real>, DT_3_3_2: T_3)
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

method m_method_5(p_m_method_5_1: seq<bool>, p_m_method_5_2: seq<int>) returns (ret_1: seq<(int, real)>)
	requires (|p_m_method_5_1| == 4 && (p_m_method_5_1[0] == true) && (p_m_method_5_1[1] == true) && (p_m_method_5_1[2] == true) && (p_m_method_5_1[3] == true) && |p_m_method_5_2| == 3 && (p_m_method_5_2[0] == 18) && (p_m_method_5_2[1] == 15) && (p_m_method_5_2[2] == 27));
	ensures ((|p_m_method_5_1| == 4 && (p_m_method_5_1[0] == true) && (p_m_method_5_1[1] == true) && (p_m_method_5_1[2] == true) && (p_m_method_5_1[3] == true) && |p_m_method_5_2| == 3 && (p_m_method_5_2[0] == 18) && (p_m_method_5_2[1] == 15) && (p_m_method_5_2[2] == 27)) ==> (|ret_1| == 2 && ((ret_1[0]).0 == 24) && (1.63 < (ret_1[0]).1 < 1.83) && ((ret_1[1]).0 == 8) && (11.13 < (ret_1[1]).1 < 11.33)));
{
	var v_DT_1_1_6: DT_1 := DT_1_1;
	var v_DT_1_1_7: DT_1 := DT_1_1;
	var v_map_3: map<int, DT_1> := map[3 := v_DT_1_1_6, 8 := v_DT_1_1_7];
	var v_int_33: int := 5;
	var v_DT_1_1_8: DT_1 := DT_1_1;
	var v_map_4: map<int, map<int, int>> := map[19 := map[18 := 24, 7 := -2], 10 := map[-25 := -7], 1 := map[25 := 18, 8 := 21, 13 := 8, 19 := 15], 8 := map[19 := -21, 29 := 24, 21 := 6, 28 := 7]];
	var v_int_34: int := -23;
	var v_DT_1_1_9: DT_1, v_map_5: map<int, int> := (if ((v_int_33 in v_map_3)) then (v_map_3[v_int_33]) else (v_DT_1_1_8)), (if ((v_int_34 in v_map_4)) then (v_map_4[v_int_34]) else (map[4 := -14, -28 := 27]));
	var v_int_43: int, v_int_44: int := (21 + 9), v_int_34;
	for v_int_35 := v_int_43 downto v_int_44 
		invariant (v_int_35 - v_int_44 >= 0) && ((((v_int_35 == 29)) ==> ((((v_int_34 == -23)) && ((v_int_33 == 5))))) && (((v_int_35 == -7)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -17)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -13)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 2)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 20)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -20)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 28)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 16)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -2)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 6)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 24)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 12)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -6)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -18)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -22)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -14)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 3)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -21)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 15)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -1)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 27)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 11)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 23)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 7)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -9)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 19)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -5)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -19)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -15)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -11)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -23)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 4)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -10)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 0)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 26)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 14)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 22)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 10)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 8)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -8)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 18)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -4)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -16)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -12)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 1)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 25)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 9)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 17)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == -3)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 21)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 5)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))) && (((v_int_35 == 13)) ==> ((((v_int_34 == 5)) && ((v_int_33 == 20))))))
	{
		var v_int_36: int := 10;
		var v_int_37: int := 11;
		var v_int_38: int := safe_division(v_int_36, v_int_37);
		var v_map_6: map<int, int> := map[17 := 28, 26 := 2, -20 := 3];
		var v_int_39: int := 24;
		v_int_37, v_int_34, v_int_38, v_int_36, v_int_33 := v_int_33, (if (false) then (26) else (5)), v_int_38, v_int_37, (if ((v_int_39 in v_map_6)) then (v_map_6[v_int_39]) else (20));
		var v_int_40: int := -13;
		var v_int_41: int := 26;
		var v_int_42: int := safe_modulus(v_int_40, v_int_41);
		v_int_38, v_int_41, v_int_42 := (0 * 28), v_int_33, v_int_42;
		var v_DT_1_1_10: DT_1 := DT_1_1;
		var v_DT_1_1_11: DT_1 := DT_1_1;
		print "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_map_6", " ", (v_map_6 == map[17 := 28, -20 := 3, 26 := 2]), " ", "v_int_39", " ", v_int_39, " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_map_5", " ", (v_map_5 == map[4 := -14, -28 := 27]), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_map_4", " ", (v_map_4 == map[1 := map[19 := 15, 8 := 21, 25 := 18, 13 := 8], 19 := map[18 := 24, 7 := -2], 8 := map[19 := -21, 21 := 6, 28 := 7, 29 := 24], 10 := map[-25 := -7]]), " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "v_map_3", " ", (v_map_3 == map[3 := v_DT_1_1_10, 8 := v_DT_1_1_11]), " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
	}
	if (match 29 {
		case 1 => false
		case _ => false
	}) {
		
	}
	var v_DT_2_3_8: DT_2<real> := DT_2_3;
	var v_DT_2_3_9: DT_2<real> := v_DT_2_3_8;
	var v_bool_6: bool := m_method_4(v_DT_2_3_9);
	if v_bool_6 {
		var v_DT_1_1_12: DT_1 := DT_1_1;
		assert ((v_DT_1_1_8 == v_DT_1_1_12) && (p_m_method_5_1 == [true, true, true, true]));
		expect ((v_DT_1_1_8 == v_DT_1_1_12) && (p_m_method_5_1 == [true, true, true, true]));
		var v_int_real_1: (int, real) := (24, 1.73);
		var v_int_real_2: (int, real) := (8, 11.23);
		var v_int_real_4: (int, real) := (24, 1.73);
		var v_int_real_5: (int, real) := (8, 11.23);
		var v_DT_1_1_13: DT_1 := DT_1_1;
		var v_DT_1_1_14: DT_1 := DT_1_1;
		print "v_int_real_2.1", " ", (v_int_real_2.1 == 11.23), " ", "v_int_real_1.1", " ", (v_int_real_1.1 == 1.73), " ", "v_int_real_2.0", " ", v_int_real_2.0, " ", "v_int_real_1", " ", (v_int_real_1 == v_int_real_4), " ", "v_int_real_1.0", " ", v_int_real_1.0, " ", "v_int_real_2", " ", (v_int_real_2 == v_int_real_5), " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_map_5", " ", (v_map_5 == map[4 := -14, -28 := 27]), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_map_4", " ", (v_map_4 == map[1 := map[19 := 15, 8 := 21, 25 := 18, 13 := 8], 19 := map[18 := 24, 7 := -2], 8 := map[19 := -21, 21 := 6, 28 := 7, 29 := 24], 10 := map[-25 := -7]]), " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_map_3", " ", (v_map_3 == map[3 := v_DT_1_1_13, 8 := v_DT_1_1_14]), " ", "v_bool_6", " ", v_bool_6, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_DT_2_3_9", " ", v_DT_2_3_9, " ", "v_DT_2_3_8", " ", v_DT_2_3_8, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
		return ([v_int_real_1, v_int_real_2] + []);
	}
	var v_seq_10: seq<(int, real)> := [];
	var v_seq_11: seq<(int, real)> := v_seq_10;
	var v_int_45: int := -21;
	var v_int_46: int := safe_index_seq(v_seq_11, v_int_45);
	var v_int_47: int := v_int_46;
	var v_int_real_3: (int, real) := (-15, -1.06);
	return (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_47 := v_int_real_3]) else (v_seq_10));
}

method m_method_4(p_m_method_4_1: DT_2<real>) returns (ret_1: bool)
	requires ((p_m_method_4_1.DT_2_3? && ((p_m_method_4_1 == DT_2_3))));
	ensures (((p_m_method_4_1.DT_2_3? && ((p_m_method_4_1 == DT_2_3)))) ==> ((ret_1 == true)));
{
	print "p_m_method_4_1", " ", p_m_method_4_1, "\n";
	return true;
}

method m_method_3(p_m_method_3_1: seq<int>) returns (ret_1: array<real>)
	requires (|p_m_method_3_1| == 3 && (p_m_method_3_1[0] == 18) && (p_m_method_3_1[1] == 15) && (p_m_method_3_1[2] == 27));
	ensures ((|p_m_method_3_1| == 3 && (p_m_method_3_1[0] == 18) && (p_m_method_3_1[1] == 15) && (p_m_method_3_1[2] == 27)) ==> (ret_1.Length == 4 && (-1.32 < ret_1[0] < -1.12) && (-18.15 < ret_1[1] < -17.95) && (-21.58 < ret_1[2] < -21.38) && (-7.97 < ret_1[3] < -7.77)));
{
	var v_int_11: int, v_int_12: int := 20, 10;
	for v_int_10 := v_int_11 downto v_int_12 
		invariant (v_int_10 - v_int_12 >= 0)
	{
		var v_array_10: array<real> := new real[4] [-1.22, -18.05, -21.48, -7.87];
		print "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_int_10", " ", v_int_10, " ", "v_array_10[3]", " ", (v_array_10[3] == -7.87), " ", "v_array_10[2]", " ", (v_array_10[2] == -21.48), " ", "v_array_10[1]", " ", (v_array_10[1] == -18.05), " ", "v_array_10[0]", " ", (v_array_10[0] == -1.22), " ", "p_m_method_3_1", " ", p_m_method_3_1, "\n";
		return v_array_10;
	}
	var v_int_22: int, v_int_23: int := 11, 21;
	for v_int_13 := v_int_22 to v_int_23 
		invariant (v_int_23 - v_int_13 >= 0)
	{
		var v_int_15: int, v_int_16: int := 27, -3;
		for v_int_14 := v_int_15 to v_int_16 
			invariant (v_int_16 - v_int_14 >= 0)
		{
			var v_array_11: array<real> := new real[5] [1.21, -22.40, 9.90, -23.15, 14.79];
			return v_array_11;
		}
		var v_int_17: int := 29;
		var v_int_18: int := 13;
		while (v_int_17 < v_int_18) 
			decreases v_int_18 - v_int_17;
			invariant (v_int_17 <= v_int_18);
		{
			v_int_17 := (v_int_17 + 1);
			var v_array_12: array<real> := new real[3] [18.35, 13.11, 0.59];
			return v_array_12;
		}
		var v_int_20: int, v_int_21: int := 14, 29;
		for v_int_19 := v_int_20 to v_int_21 
			invariant (v_int_21 - v_int_19 >= 0)
		{
			var v_array_13: array<real> := new real[3] [-17.92, -16.79, -13.00];
			return v_array_13;
		}
	}
	var v_int_27: int, v_int_28: int := 1, 22;
	for v_int_24 := v_int_27 to v_int_28 
		invariant (v_int_28 - v_int_24 >= 0)
	{
		if true {
			
		} else {
			var v_array_14: array<real> := new real[4] [24.62, 9.46, 21.85, 2.77];
			return v_array_14;
		}
		var v_int_25: int := 11;
		var v_int_26: int := -26;
		while (v_int_25 < v_int_26) 
			decreases v_int_26 - v_int_25;
			invariant (v_int_25 <= v_int_26);
		{
			v_int_25 := (v_int_25 + 1);
			var v_array_15: array<real> := new real[3] [-23.07, 19.24, 25.48];
			return v_array_15;
		}
		if true {
			
		} else {
			var v_array_16: array<real> := new real[4] [19.12, 20.17, -26.32, 9.01];
			return v_array_16;
		}
		if true {
			var v_array_17: array<real> := new real[4] [12.19, 1.05, 7.06, -5.05];
			return v_array_17;
		} else {
			var v_array_18: array<real> := new real[4] [3.10, -16.69, -21.19, 28.62];
			return v_array_18;
		}
	}
	assert true;
	expect true;
	if false {
		var v_array_19: array<char> := new char[4];
		v_array_19[0] := 'P';
		v_array_19[1] := 'r';
		v_array_19[2] := 'c';
		v_array_19[3] := 'A';
		var v_int_29: int, v_array_20: array<char> := 26, v_array_19;
		var v_array_21: array<real> := new real[5];
		v_array_21[0] := -14.21;
		v_array_21[1] := -16.96;
		v_array_21[2] := 23.73;
		v_array_21[3] := 1.49;
		v_array_21[4] := 22.11;
		return v_array_21;
	} else {
		assert true;
		expect true;
	}
	var v_array_22: array<real> := new real[5] [25.05, 21.95, 14.24, 23.84, -0.84];
	return v_array_22;
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

method m_method_2(p_m_method_2_1: int) returns (ret_1: bool)
	requires ((p_m_method_2_1 == 13));
	ensures (((p_m_method_2_1 == 13)) ==> ((ret_1 == true)));
{
	var v_array_1: array<real> := new real[3] [-23.80, 10.20, 27.98];
	var v_array_2: array<real> := new real[5] [21.62, 12.36, -8.10, 15.54, 19.29];
	var v_array_3: array<real> := new real[5] [8.06, -24.27, -28.92, 29.81, -15.99];
	var v_seq_4: seq<array<real>> := [v_array_1, v_array_2, v_array_3];
	var v_int_8: int := -1;
	var v_seq_45: seq<array<real>> := v_seq_4;
	var v_int_95: int := v_int_8;
	var v_int_96: int := safe_index_seq(v_seq_45, v_int_95);
	v_int_8 := v_int_96;
	var v_array_4: array<real> := new real[3];
	v_array_4[0] := 12.15;
	v_array_4[1] := 24.04;
	v_array_4[2] := -9.22;
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_array_5: array<real> := new real[4] [28.40, -11.68, 21.29, -25.15];
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_array_6: array<real> := new real[3] [-14.31, 22.68, 20.18];
	var v_DT_1_1_3: DT_1 := DT_1_1;
	var v_array_7: array<real> := new real[5] [-29.00, -14.04, -6.13, -14.25, 11.93];
	var v_map_2: map<DT_1, array<real>> := map[v_DT_1_1_1 := v_array_5];
	var v_DT_1_1_4: DT_1 := DT_1_1;
	var v_DT_1_1_5: DT_1 := v_DT_1_1_4;
	var v_array_8: array<real> := new real[4] [-28.63, -13.07, -20.90, 4.39];
	var v_seq_5: seq<array<real>> := [];
	var v_int_9: int := 13;
	var v_array_9: array<real> := new real[3] [-11.13, 3.60, -24.10];
	var v_seq_6: seq<int> := [18, 15, 27];
	var v_array_23: array<real> := m_method_3(v_seq_6);
	var v_array_24: array<real> := new real[3];
	v_array_24[0] := -12.30;
	v_array_24[1] := -1.80;
	v_array_24[2] := 29.94;
	var v_array_25: array<real> := new real[3] [26.01, -24.99, 19.82];
	var v_array_26: array<real> := new real[3] [-26.58, -23.02, 19.40];
	var v_seq_7: seq<array<real>> := [v_array_24, v_array_25, v_array_26];
	var v_int_30: int := -29;
	var v_seq_46: seq<array<real>> := v_seq_7;
	var v_int_97: int := v_int_30;
	var v_int_98: int := safe_index_seq(v_seq_46, v_int_97);
	v_int_30 := v_int_98;
	var v_array_27: array<real> := new real[3] [-20.54, 2.97, 21.74];
	var v_array_28: array<array<real>> := new array<real>[5] [(if ((|v_seq_4| > 0)) then (v_seq_4[v_int_8]) else (v_array_4)), (if ((v_DT_1_1_5 in v_map_2)) then (v_map_2[v_DT_1_1_5]) else (v_array_8)), (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_9]) else (v_array_9)), v_array_23, (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_30]) else (v_array_27))];
	var v_array_29: array<array<real>> := v_array_28;
	var v_DT_2_3_1: DT_2<real> := DT_2_3;
	var v_DT_2_3_2: DT_2<real> := v_DT_2_3_1;
	var v_bool_4: bool := m_method_4(v_DT_2_3_2);
	var v_seq_8: seq<seq<seq<bool>>> := [];
	var v_int_31: int := 29;
	var v_DT_2_3_3: DT_2<real> := DT_2_3;
	var v_DT_2_3_4: DT_2<real> := DT_2_3;
	var v_DT_2_3_5: DT_2<real> := DT_2_3;
	var v_seq_9: seq<DT_2<real>> := [v_DT_2_3_3, v_DT_2_3_4, v_DT_2_3_5];
	var v_int_32: int := 11;
	var v_seq_47: seq<DT_2<real>> := v_seq_9;
	var v_int_99: int := v_int_32;
	var v_int_100: int := safe_index_seq(v_seq_47, v_int_99);
	v_int_32 := v_int_100;
	var v_DT_2_3_6: DT_2<real> := DT_2_3;
	var v_DT_2_3_7: DT_2<real> := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_32]) else (v_DT_2_3_6));
	var v_bool_5: bool := m_method_4(v_DT_2_3_7);
	var v_map_7: map<int, seq<bool>> := map[18 := [true, false], 14 := [false, true], 19 := [true, false, false]];
	var v_int_48: int := 15;
	var v_seq_12: seq<bool> := (if ((v_int_48 in v_map_7)) then (v_map_7[v_int_48]) else ([true, true, true, true]));
	var v_seq_13: seq<int> := v_seq_6;
	var v_seq_14: seq<(int, real)> := m_method_5(v_seq_12, v_seq_13);
	var v_bool_real_real_1: (bool, real, real) := (true, 6.92, -27.25);
	var v_bool_map_bool_real_real_1: (bool, map<real, int>, (bool, real, real)) := (false, map[-8.06 := -29], v_bool_real_real_1);
	var v_bool_real_real_2: (bool, real, real) := (true, 18.75, 6.30);
	var v_bool_map_bool_real_real_2: (bool, map<real, int>, (bool, real, real)) := (false, map[-25.07 := 21, 7.73 := 12, 10.76 := -19], v_bool_real_real_2);
	var v_bool_real_real_3: (bool, real, real) := (true, 7.94, 27.51);
	var v_bool_map_bool_real_real_3: (bool, map<real, int>, (bool, real, real)) := (true, map[21.87 := 19, 3.77 := 24, -1.83 := 21, 6.48 := 23], v_bool_real_real_3);
	var v_bool_real_real_4: (bool, real, real) := (false, 14.36, 17.68);
	var v_bool_map_bool_real_real_4: (bool, map<real, int>, (bool, real, real)) := (true, map[-15.04 := 25, 29.37 := 28, -4.13 := -6, 22.38 := 21], v_bool_real_real_4);
	var v_bool_real_real_5: (bool, real, real) := (true, 20.90, -28.80);
	var v_bool_map_bool_real_real_5: (bool, map<real, int>, (bool, real, real)) := (true, map[-11.31 := 7, 6.43 := 12, 21.73 := -1, 25.92 := 18], v_bool_real_real_5);
	var v_bool_real_real_6: (bool, real, real) := (false, -4.19, -16.25);
	var v_bool_map_bool_real_real_6: (bool, map<real, int>, (bool, real, real)) := (true, map[-23.03 := 19, -11.16 := 21, 25.19 := 18, -12.69 := 1], v_bool_real_real_6);
	var v_seq_15: seq<(bool, map<real, int>, (bool, real, real))> := [v_bool_map_bool_real_real_4, v_bool_map_bool_real_real_5, v_bool_map_bool_real_real_6];
	var v_int_49: int := 11;
	var v_seq_48: seq<(bool, map<real, int>, (bool, real, real))> := v_seq_15;
	var v_int_101: int := v_int_49;
	var v_int_102: int := safe_index_seq(v_seq_48, v_int_101);
	v_int_49 := v_int_102;
	var v_bool_real_real_7: (bool, real, real) := (true, 2.71, 8.23);
	var v_bool_map_bool_real_real_7: (bool, map<real, int>, (bool, real, real)) := (true, map[3.35 := 15, -20.09 := 8, -16.81 := 26], v_bool_real_real_7);
	var v_seq_16: seq<char> := ['f', 'J', 'c', 'I'];
	var v_int_50: int := 10;
	var v_seq_17: seq<char> := ['k', 'F', 'q', 'F'];
	var v_int_51: int := 27;
	var v_bool_7: bool := true;
	var v_DT_1_2_3: DT_1 := DT_1_2(false, 11.21, true);
	var v_DT_1_2_4: DT_1 := v_DT_1_2_3;
	var v_bool_8: bool := false;
	var v_char_3: char := 'R';
	var v_char_4: char := m_method_1(v_bool_7, v_DT_1_2_4, v_bool_8, v_char_3);
	var v_seq_18: seq<seq<bool>>, v_bool_9: bool, v_seq_19: seq<(int, real)>, v_bool_map_bool_real_real_8: (bool, map<real, int>, (bool, real, real)), v_char_5: char := (if (v_bool_4) then ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_31]) else ([[], [true, true, true, false], [false, false, true, true]]))) else (([[false]] + [[false, false, true, true]]))), v_bool_5, v_seq_14, (match 14 {
		case 2 => (match 6 {
			case _ => v_bool_map_bool_real_real_3
		})
		case _ => (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_49]) else (v_bool_map_bool_real_real_7))
	}), (match 24 {
		case 16 => (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_50]) else ('K'))
		case 12 => (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_51]) else ('Z'))
		case _ => v_char_4
	});
	var v_seq_20: seq<bool> := [true, false, false];
	var v_seq_21: seq<bool> := v_seq_20;
	var v_int_52: int := 29;
	var v_int_53: int := safe_index_seq(v_seq_21, v_int_52);
	var v_int_54: int := v_int_53;
	var v_seq_22: seq<bool> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_54 := true]) else (v_seq_20));
	var v_int_55: int := (16.55).Floor;
	var v_seq_49: seq<bool> := v_seq_22;
	var v_int_103: int := v_int_55;
	var v_int_104: int := safe_index_seq(v_seq_49, v_int_103);
	v_int_55 := v_int_104;
	var v_bool_real_real_8: (bool, real, real) := (false, 14.36, 17.68);
	var v_bool_map_bool_real_real_9: (bool, map<real, int>, (bool, real, real)) := (true, map[29.37 := 28, -15.04 := 25, -4.13 := -6, 22.38 := 21], v_bool_real_real_8);
	var v_DT_1_1_15: DT_1 := DT_1_1;
	var v_int_real_6: (int, real) := (24, 1.73);
	var v_int_real_7: (int, real) := (8, 11.23);
	var v_int_real_8: (int, real) := (24, 1.73);
	var v_int_real_9: (int, real) := (8, 11.23);
	print "v_array_5[3]", " ", (v_array_5[3] == -25.15), " ", "v_bool_map_bool_real_real_8", " ", (v_bool_map_bool_real_real_8 == v_bool_map_bool_real_real_9), " ", "v_array_28[2]", " ", (v_array_28[2] == v_array_9), " ", "v_array_26[0]", " ", (v_array_26[0] == -26.58), " ", "v_int_48", " ", v_int_48, " ", "v_array_3[0]", " ", (v_array_3[0] == 8.06), " ", "v_array_8[3]", " ", (v_array_8[3] == 4.39), " ", "v_array_5[2]", " ", (v_array_5[2] == 21.29), " ", "v_array_9[0]", " ", (v_array_9[0] == -11.13), " ", "v_array_2[3]", " ", (v_array_2[3] == 15.54), " ", "v_array_28[3]", " ", "v_int_32", " ", v_int_32, " ", "v_seq_21", " ", v_seq_21, " ", "v_array_26[1]", " ", (v_array_26[1] == -23.02), " ", "v_seq_22", " ", v_seq_22, " ", "v_seq_20", " ", v_seq_20, " ", "v_array_2[4]", " ", (v_array_2[4] == 19.29), " ", "v_int_31", " ", v_int_31, " ", "v_array_8[2]", " ", (v_array_8[2] == -20.90), " ", "v_int_30", " ", v_int_30, " ", "v_array_3[1]", " ", (v_array_3[1] == -24.27), " ", "v_array_6[0]", " ", (v_array_6[0] == -14.31), " ", "v_array_7[3]", " ", (v_array_7[3] == -14.25), " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_array_28[0]", " ", (v_array_28[0] == v_array_1), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_array_25[1]", " ", (v_array_25[1] == -24.99), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[1]", " ", (v_array_2[1] == 12.36), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_array_5[0]", " ", (v_array_5[0] == 28.40), " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_8[1]", " ", (v_array_8[1] == -13.07), " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_map_7", " ", (v_map_7 == map[18 := [true, false], 19 := [true, false, false], 14 := [false, true]]), " ", "v_array_7[4]", " ", (v_array_7[4] == 11.93), " ", "v_char_5", " ", (v_char_5 == 'R'), " ", "v_map_2", " ", (v_map_2 == map[v_DT_1_1_15 := v_array_5]), " ", "v_array_28[1]", " ", (v_array_28[1] == v_array_5), " ", "v_DT_2_3_2", " ", v_DT_2_3_2, " ", "v_DT_2_3_1", " ", v_DT_2_3_1, " ", "v_int_55", " ", v_int_55, " ", "v_int_54", " ", v_int_54, " ", "v_DT_2_3_6", " ", v_DT_2_3_6, " ", "v_array_25[2]", " ", (v_array_25[2] == 19.82), " ", "v_DT_2_3_5", " ", v_DT_2_3_5, " ", "v_DT_2_3_4", " ", v_DT_2_3_4, " ", "v_DT_2_3_3", " ", v_DT_2_3_3, " ", "v_DT_2_3_7", " ", v_DT_2_3_7, " ", "v_int_53", " ", v_int_53, " ", "v_int_52", " ", v_int_52, " ", "v_array_2[2]", " ", (v_array_2[2] == -8.10), " ", "v_array_5[1]", " ", (v_array_5[1] == -11.68), " ", "v_array_8[0]", " ", (v_array_8[0] == -28.63), " ", "v_array_7[1]", " ", (v_array_7[1] == -14.04), " ", "v_array_27[1]", " ", (v_array_27[1] == 2.97), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_array_24[2]", " ", (v_array_24[2] == 29.94), " ", "v_array_1[2]", " ", (v_array_1[2] == 27.98), " ", "v_array_4[1]", " ", (v_array_4[1] == 24.04), " ", "v_array_3[4]", " ", (v_array_3[4] == -15.99), " ", "v_array_7[0]", " ", (v_array_7[0] == -29.00), " ", "v_array_7[2]", " ", (v_array_7[2] == -6.13), " ", "v_array_27[2]", " ", (v_array_27[2] == 21.74), " ", "v_array_25[0]", " ", (v_array_25[0] == 26.01), " ", "v_array_2[0]", " ", (v_array_2[0] == 21.62), " ", "v_array_29", " ", (v_array_29 == v_array_28), " ", "v_array_28", " ", (v_array_28 == v_array_28), " ", "v_array_27", " ", (v_array_27 == v_array_27), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_4[2]", " ", (v_array_4[2] == -9.22), " ", "v_array_23", " ", "v_array_6[2]", " ", (v_array_6[2] == 20.18), " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_5", " ", v_bool_5, " ", "v_seq_18", " ", v_seq_18, " ", "v_array_28[4]", " ", (v_array_28[4] == v_array_24), " ", "v_bool_4", " ", v_bool_4, " ", "v_seq_19", " ", (v_seq_19 == [v_int_real_6, v_int_real_7]), " ", "v_seq_14", " ", (v_seq_14 == [v_int_real_8, v_int_real_9]), " ", "v_array_26[2]", " ", (v_array_26[2] == 19.40), " ", "v_seq_12", " ", v_seq_12, " ", "v_int_9", " ", v_int_9, " ", "v_array_24[0]", " ", (v_array_24[0] == -12.30), " ", "v_seq_13", " ", v_seq_13, " ", "v_array_1[0]", " ", (v_array_1[0] == -23.80), " ", "v_array_9[2]", " ", (v_array_9[2] == -24.10), " ", "v_array_3[2]", " ", (v_array_3[2] == -28.92), " ", "v_array_6[1]", " ", (v_array_6[1] == 22.68), " ", "v_int_8", " ", v_int_8, " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", (v_seq_7 == [v_array_24, v_array_25, v_array_26]), " ", "v_seq_6", " ", v_seq_6, " ", "v_seq_5", " ", (v_seq_5 == []), " ", "v_seq_4", " ", (v_seq_4 == [v_array_1, v_array_2, v_array_3]), " ", "v_array_24[1]", " ", (v_array_24[1] == -1.80), " ", "v_array_27[0]", " ", (v_array_27[0] == -20.54), " ", "v_array_1[1]", " ", (v_array_1[1] == 10.20), " ", "v_array_3[3]", " ", (v_array_3[3] == 29.81), " ", "v_array_4[0]", " ", (v_array_4[0] == 12.15), " ", "v_array_9[1]", " ", (v_array_9[1] == 3.60), "\n";
	return (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_55]) else (v_bool_4));
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: DT_1, p_m_method_1_3: bool, p_m_method_1_4: char) returns (ret_1: char)
	requires ((p_m_method_1_1 == true) && (p_m_method_1_3 == false) && (p_m_method_1_2.DT_1_2? && ((p_m_method_1_2.DT_1_2_1 == false) && (-0.93 < p_m_method_1_2.DT_1_2_2 < -0.73) && (p_m_method_1_2.DT_1_2_3 == true))) && (p_m_method_1_4 == 'e')) || ((p_m_method_1_1 == true) && (p_m_method_1_3 == false) && (p_m_method_1_2.DT_1_2? && ((p_m_method_1_2.DT_1_2_1 == false) && (11.11 < p_m_method_1_2.DT_1_2_2 < 11.31) && (p_m_method_1_2.DT_1_2_3 == true))) && (p_m_method_1_4 == 'R'));
	ensures (((p_m_method_1_1 == true) && (p_m_method_1_3 == false) && (p_m_method_1_2.DT_1_2? && ((p_m_method_1_2.DT_1_2_1 == false) && (-0.93 < p_m_method_1_2.DT_1_2_2 < -0.73) && (p_m_method_1_2.DT_1_2_3 == true))) && (p_m_method_1_4 == 'e')) ==> ((ret_1 == 'e'))) && (((p_m_method_1_1 == true) && (p_m_method_1_3 == false) && (p_m_method_1_2.DT_1_2? && ((p_m_method_1_2.DT_1_2_1 == false) && (11.11 < p_m_method_1_2.DT_1_2_2 < 11.31) && (p_m_method_1_2.DT_1_2_3 == true))) && (p_m_method_1_4 == 'R')) ==> ((ret_1 == 'R')));
{
	var v_DT_1_2_39: DT_1 := DT_1_2(false, -0.83, true);
	print "p_m_method_1_2", " ", (p_m_method_1_2 == v_DT_1_2_39), " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "p_m_method_1_2.DT_1_2_3", " ", p_m_method_1_2.DT_1_2_3, " ", "p_m_method_1_2.DT_1_2_2", " ", (p_m_method_1_2.DT_1_2_2 == -0.83), " ", "p_m_method_1_2.DT_1_2_1", " ", p_m_method_1_2.DT_1_2_1, " ", "p_m_method_1_4", " ", (p_m_method_1_4 == 'e'), " ", "p_m_method_1_3", " ", p_m_method_1_3, "\n";
	return p_m_method_1_4;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_bool_2: bool := true;
	var v_DT_1_2_1: DT_1 := DT_1_2(false, -0.83, true);
	var v_DT_1_2_2: DT_1 := v_DT_1_2_1;
	var v_map_1: map<bool, bool> := map[false := false];
	var v_bool_1: bool := true;
	var v_bool_3: bool := (if ((v_bool_1 in v_map_1)) then (v_map_1[v_bool_1]) else (false));
	var v_seq_3: seq<char> := ['e'];
	var v_int_7: int := 1;
	var v_seq_44: seq<char> := v_seq_3;
	var v_int_93: int := v_int_7;
	var v_int_94: int := safe_index_seq(v_seq_44, v_int_93);
	v_int_7 := v_int_94;
	var v_char_1: char := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else ('P'));
	var v_char_2: char := m_method_1(v_bool_2, v_DT_1_2_2, v_bool_3, v_char_1);
	var v_int_56: int := 5;
	var v_int_57: int := 21;
	var v_int_58: int := safe_modulus(v_int_56, v_int_57);
	var v_int_59: int := (match 23 {
		case 1 => (5 % 19)
		case 7 => v_int_58
		case _ => (match true {
			case false => 4
			case true => 13
			case _ => 23
		})
	});
	var v_bool_10: bool := m_method_2(v_int_59);
	var v_bool_11: bool, v_char_6: char, v_bool_12: bool := false, (match -25.11 {
		case -21.79 => 'k'
		case -6.08 => 'n'
		case _ => v_char_2
	}), v_bool_10;
	v_bool_10 := v_bool_10;
	if v_bool_12 {
		assert ((v_int_59 == 13) && (v_bool_10 == true) && (v_char_6 == 'e') && (v_bool_11 == false) && (v_bool_12 == true));
		expect ((v_int_59 == 13) && (v_bool_10 == true) && (v_char_6 == 'e') && (v_bool_11 == false) && (v_bool_12 == true));
		print "v_int_59", " ", v_int_59, " ", "v_char_6", " ", (v_char_6 == 'e'), " ", "v_bool_11", " ", v_bool_11, " ", "v_bool_12", " ", v_bool_12, " ", "v_bool_10", " ", v_bool_10, "\n";
		return ;
	} else {
		if v_bool_10 {
			var v_map_8: map<bool, map<seq<bool>, bool>> := map[false := map[[true, true] := true, [true, true, false] := false, [false] := true], false := map[[true, false] := true, [] := false, [false, true, false, false] := false, [true, true, false, false] := true, [false, false] := true], false := map[[false, true, true, true] := true, [false, true, true] := true, [false, true, true, true] := false, [true, false, false] := true], true := map[[true] := true], true := map[[false, false, true, false] := true, [false, false] := true, [] := false]];
			var v_bool_13: bool := true;
			var v_map_10: map<seq<bool>, bool> := (if (!(false)) then ((if ((v_bool_13 in v_map_8)) then (v_map_8[v_bool_13]) else (map[[true, false, true, true] := true, [] := false, [false, false, true, true] := false, [false] := false, [true, false, false] := true]))) else ((if (false) then (map[[true] := true, [false, true, false, true] := false]) else (map[[false] := true]))));
			var v_seq_23: seq<bool> := [];
			var v_seq_24: seq<bool> := (if ((|v_seq_23| > 0)) then (v_seq_23[12..9]) else (v_seq_23));
			var v_seq_25: seq<bool> := v_seq_24;
			var v_int_60: int := v_int_59;
			var v_int_61: int := safe_index_seq(v_seq_25, v_int_60);
			var v_int_62: int := v_int_61;
			var v_seq_26: seq<bool> := (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_62 := (false != true)]) else (v_seq_24));
			var v_map_9: map<bool, multiset<bool>> := map[false := multiset{true}, true := multiset{true, false, true, true}, true := multiset{}];
			var v_bool_14: bool := false;
			var v_seq_27: seq<bool> := [false, false, false, true];
			var v_seq_28: seq<bool> := v_seq_27;
			var v_int_63: int := 28;
			var v_int_64: int := safe_index_seq(v_seq_28, v_int_63);
			var v_int_65: int := v_int_64;
			var v_seq_29: seq<bool> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_65 := true]) else (v_seq_27));
			var v_int_66: int := (14 + 21);
			var v_map_11: map<bool, char> := map[true := 'T', false := 'e', false := 'E', false := 'k', false := 'T'][true := 'M'];
			var v_bool_15: bool := ('g' >= 'H');
			var v_seq_31: seq<bool> := v_seq_25;
			var v_seq_30: seq<int> := (match false {
				case _ => [28, 10]
			});
			var v_int_67: int := (match false {
				case _ => 6
			});
			var v_map_12: map<bool, int> := map[true := 20];
			var v_bool_16: bool := true;
			var v_int_68: int := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_67]) else ((if ((v_bool_16 in v_map_12)) then (v_map_12[v_bool_16]) else (7))));
			v_bool_13, v_bool_10, v_bool_14, v_bool_15 := (if ((v_seq_26 in v_map_10)) then (v_map_10[v_seq_26]) else (((multiset{true, false, true, true} - multiset({true, false})) <= (if ((v_bool_14 in v_map_9)) then (v_map_9[v_bool_14]) else (multiset({true, false, true})))))), (if ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_66]) else (v_bool_10))) then (v_bool_14) else ((match true {
				case _ => v_bool_12
			}))), ((if ((v_bool_15 in v_map_11)) then (v_map_11[v_bool_15]) else (v_char_6)) <= v_char_6), (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_68]) else (((false && false) && v_bool_13)));
		} else {
			var v_map_14: map<bool, int> := (map[true := 21, false := 20, true := 0, true := 22, false := 19] + map[false := 13, false := 10, false := 26, false := 3]);
			var v_bool_18: bool := !(true);
			var v_map_13: map<bool, int> := map[true := 27, true := -9];
			var v_bool_17: bool := true;
			var v_seq_32: seq<int> := (if (false) then ([15, 22]) else ([-19, 8, 13, 17]));
			var v_int_70: int := (8 * 19);
			var v_int_71: int, v_int_72: int := (match true {
				case _ => (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_70]) else (v_int_59))
			}), ((v_int_59 + v_int_59) / (match 6 {
				case _ => v_int_59
			}));
			for v_int_69 := v_int_71 to v_int_72 
				invariant (v_int_72 - v_int_69 >= 0)
			{
				break;
			}
			var v_seq_33: seq<int> := [];
			if ((if ((if (true) then (true) else (false))) then ((if ((|v_seq_33| > 0)) then (v_seq_33[25..3]) else (v_seq_33))) else (v_seq_33)) == (([29, 28] + [-18, 10, -28]) + (if (false) then ([]) else ([25, 3, 28])))) {
				assert true;
				expect true;
				return ;
			} else {
				return ;
			}
		}
		var v_seq_34: seq<int> := ([25, 27] + []);
		var v_int_74: int := (-22.68).Floor;
		var v_seq_35: seq<bool> := [true];
		var v_int_75: int := 0;
		var v_map_15: map<int, int> := map[23 := 11, 21 := 13, 19 := 13, 7 := 8, 28 := 7];
		var v_int_76: int := 29;
		var v_array_30: array<int> := new int[3] [10, 25, 13];
		var v_array_31: array<int> := new int[4] [7, -9, 15, 16];
		var v_array_32: array<int> := new int[4] [22, 0, -25, 1];
		var v_array_33: array<int> := new int[3] [15, 7, 6];
		var v_array_34: array<int> := new int[3] [20, 28, 22];
		var v_array_35: array<int> := new int[5] [15, 16, 25, 4, 29];
		var v_array_36: array<int> := new int[5] [11, 16, 0, 10, 28];
		var v_array_37: array<int> := new int[4] [20, -25, 16, 3];
		var v_map_16: map<int, map<int, array<int>>> := map[7 := map[18 := v_array_30, 20 := v_array_31, 21 := v_array_32, 6 := v_array_33], -16 := map[8 := v_array_34, 27 := v_array_35], 13 := map[23 := v_array_36], 25 := map[6 := v_array_37]];
		var v_int_77: int := 4;
		var v_array_38: array<int> := new int[4] [5, 11, 12, 6];
		var v_array_39: array<int> := new int[3] [-6, 6, 26];
		var v_array_40: array<int> := new int[4] [28, 5, 1, 6];
		var v_array_41: array<int> := new int[5];
		v_array_41[0] := 7;
		v_array_41[1] := 4;
		v_array_41[2] := 23;
		v_array_41[3] := 17;
		v_array_41[4] := -16;
		var v_map_18: map<int, array<int>> := (if ((v_int_77 in v_map_16)) then (v_map_16[v_int_77]) else (map[8 := v_array_38, 22 := v_array_39, 14 := v_array_40, -18 := v_array_41]));
		var v_map_17: map<int, int> := map[-17 := 7, 9 := 27];
		var v_int_78: int := 13;
		var v_int_79: int := (if ((v_int_78 in v_map_17)) then (v_map_17[v_int_78]) else (4));
		var v_array_42: array<int> := new int[4] [17, 20, 20, 23];
		var v_array_43: array<int> := new int[4] [6, 22, 10, 27];
		var v_int_80: int, v_int_81: int := ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_74]) else (v_int_59)) * (if ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_75]) else (false))) then ((if (false) then (21) else (20))) else ((if ((v_int_76 in v_map_15)) then (v_map_15[v_int_76]) else (13))))), (if ((v_int_79 in v_map_18)) then (v_map_18[v_int_79]) else ((match 3 {
			case _ => v_array_43
		}))).Length;
		for v_int_73 := v_int_80 to v_int_81 
			invariant (v_int_81 - v_int_73 >= 0)
		{
			return ;
		}
		assert true;
		expect true;
		assert true;
		expect true;
		var v_DT_1_2_5: DT_1 := DT_1_2(true, -18.87, true);
		var v_DT_1_2_6: DT_1 := DT_1_2(false, 6.48, true);
		var v_DT_1_2_7: DT_1 := DT_1_2(false, 11.41, false);
		var v_DT_1_2_8: DT_1 := DT_1_2(true, 4.68, true);
		var v_DT_1_2_9: DT_1 := DT_1_2(true, -3.05, false);
		var v_DT_1_2_10: DT_1 := DT_1_2(false, -22.25, true);
		var v_DT_1_2_11: DT_1 := DT_1_2(true, 22.60, false);
		var v_DT_1_2_12: DT_1 := DT_1_2(true, -5.65, true);
		var v_DT_1_2_13: DT_1 := DT_1_2(true, 20.69, true);
		var v_DT_1_2_14: DT_1 := DT_1_2(true, -26.01, false);
		var v_DT_1_2_15: DT_1 := DT_1_2(false, 3.77, false);
		var v_DT_1_2_16: DT_1 := DT_1_2(true, 14.77, true);
		var v_DT_1_2_17: DT_1 := DT_1_2(true, 5.49, true);
		var v_DT_1_2_18: DT_1 := DT_1_2(true, -20.97, true);
		var v_DT_1_2_19: DT_1 := DT_1_2(false, 29.67, true);
		var v_DT_1_2_20: DT_1 := DT_1_2(true, 27.07, true);
		var v_map_19: map<bool, map<DT_1, int>> := map[true := map[v_DT_1_2_13 := 22, v_DT_1_2_14 := 28, v_DT_1_2_15 := -1], false := map[v_DT_1_2_16 := 11, v_DT_1_2_17 := 21, v_DT_1_2_18 := 29, v_DT_1_2_19 := 0, v_DT_1_2_20 := 12]];
		var v_bool_19: bool := true;
		var v_DT_1_2_21: DT_1 := DT_1_2(false, 13.69, true);
		var v_DT_1_2_22: DT_1 := DT_1_2(true, -18.73, false);
		var v_DT_1_2_23: DT_1 := DT_1_2(true, -25.61, true);
		var v_DT_1_2_24: DT_1 := DT_1_2(true, 13.53, false);
		var v_seq_36: seq<map<DT_1, int>> := [];
		var v_int_82: int := 27;
		var v_DT_1_2_25: DT_1 := DT_1_2(true, 11.19, true);
		var v_DT_1_2_26: DT_1 := DT_1_2(false, 17.53, true);
		var v_DT_1_2_27: DT_1 := DT_1_2(false, 13.72, true);
		var v_DT_1_2_28: DT_1 := DT_1_2(false, 11.01, true);
		var v_DT_1_2_29: DT_1 := DT_1_2(false, 15.92, false);
		var v_DT_1_2_30: DT_1 := DT_1_2(false, 8.86, true);
		var v_seq_37: seq<int> := [2, 6];
		var v_int_83: int := 26;
		var v_map_21: map<DT_1, int> := (if ((|v_seq_36| > 0)) then (v_seq_36[v_int_82]) else (map[v_DT_1_2_25 := -27, v_DT_1_2_26 := 4, v_DT_1_2_27 := 3, v_DT_1_2_28 := 28]))[(if (true) then (v_DT_1_2_29) else (v_DT_1_2_30)) := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_83]) else (-16))];
		var v_DT_1_2_31: DT_1 := DT_1_2(false, -11.00, false);
		var v_DT_1_2_32: DT_1 := DT_1_2(true, -21.53, false);
		var v_DT_1_2_33: DT_1 := DT_1_2(true, 21.95, false);
		var v_seq_38: seq<DT_1> := [];
		var v_int_84: int := 23;
		var v_DT_1_2_34: DT_1 := DT_1_2(false, 20.57, true);
		var v_DT_1_2_35: DT_1 := (if (v_bool_11) then ((match true {
			case _ => v_DT_1_2_33
		})) else ((if ((|v_seq_38| > 0)) then (v_seq_38[v_int_84]) else (v_DT_1_2_34))));
		var v_map_20: map<char, seq<int>> := map['X' := [10], 'B' := [14, 16, 9, 14], 'K' := [17, 11]];
		var v_char_7: char := 'b';
		var v_seq_40: seq<int> := (if ((v_char_7 in v_map_20)) then (v_map_20[v_char_7]) else ([0, 10, -9, 20]));
		var v_seq_39: seq<int> := [8];
		var v_int_85: int := 15;
		var v_int_86: int := (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_85]) else (5));
		var v_DT_1_2_36: DT_1 := DT_1_2(false, 10.98, false);
		var v_map_22: map<DT_1, bool> := map[v_DT_1_2_36 := true];
		var v_DT_1_2_37: DT_1 := DT_1_2(true, -2.09, true);
		var v_DT_1_2_38: DT_1 := v_DT_1_2_37;
		var v_seq_41: seq<map<int, int>> := [];
		var v_seq_42: seq<map<int, int>> := v_seq_41;
		var v_int_87: int := 6;
		var v_int_88: int := safe_index_seq(v_seq_42, v_int_87);
		var v_int_89: int := v_int_88;
		var v_seq_43: seq<map<int, int>> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_89 := map[6 := 19, 13 := 5, 19 := 15, -19 := 0, 5 := 26]]) else (v_seq_41));
		var v_int_90: int := (if (true) then (7) else (18));
		var v_map_23: map<DT_1, int>, v_int_91: int, v_int_92: int, v_map_24: map<int, int> := ((if ((if (false) then (false) else (false))) then ((map[v_DT_1_2_5 := 19] - {v_DT_1_2_6, v_DT_1_2_7, v_DT_1_2_8, v_DT_1_2_9})) else (map[v_DT_1_2_10 := 6, v_DT_1_2_11 := 13][v_DT_1_2_12 := 12])) + (if ((v_bool_19 in v_map_19)) then (v_map_19[v_bool_19]) else (map[v_DT_1_2_21 := 9, v_DT_1_2_22 := -29, v_DT_1_2_23 := 1, v_DT_1_2_24 := 19]))[v_DT_1_2_18 := (match 'h' {
			case _ => 20
		})]), ((if ((if (true) then (false) else (false))) then (v_array_40[3]) else (v_array_36[1])) + v_array_33[1]), (if ((v_DT_1_2_35 in v_map_21)) then (v_map_21[v_DT_1_2_35]) else ((if ((|v_seq_40| > 0)) then (v_seq_40[v_int_86]) else ((if (true) then (10) else (4)))))), ((if ((if ((v_DT_1_2_38 in v_map_22)) then (v_map_22[v_DT_1_2_38]) else (true))) then ((if (false) then (map[28 := 19, 19 := 1]) else (map[1 := 7, 8 := 29]))) else (map[1 := 27][8 := 29])) + (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_90]) else ((if (true) then (map[7 := 25, 22 := 26]) else (map[25 := 7, 15 := 6, 24 := 11, 6 := -26])))));
		return ;
	}
}
