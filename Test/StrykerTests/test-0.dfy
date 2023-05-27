// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: char) returns (ret_1: char)
	requires ((p_m_method_7_1 == 'r'));
	ensures (((p_m_method_7_1 == 'r')) ==> ((ret_1 == 'v')));
{
	print "p_m_method_7_1", " ", (p_m_method_7_1 == 'r'), "\n";
	return 'v';
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: bool, p_m_method_6_2: bool, p_m_method_6_3: bool, p_m_method_6_4: bool) returns (ret_1: bool, ret_2: bool)
{
	return true, false;
}

method m_method_5(p_m_method_5_1: bool, p_m_method_5_2: bool) returns (ret_1: real)
{
	var v_bool_10: bool := true;
	var v_bool_11: bool := false;
	var v_bool_12: bool := false;
	var v_bool_13: bool := false;
	var v_bool_14: bool, v_bool_15: bool := m_method_6(v_bool_10, v_bool_11, v_bool_12, v_bool_13);
	v_bool_15, v_bool_13 := v_bool_14, v_bool_15;
	return 18.31;
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool, p_m_method_4_3: bool) returns (ret_1: bool)
{
	return true;
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: (real, bool, real)) returns (ret_1: int)
	requires ((p_m_method_3_1 == 'g') && (-9.39 < (p_m_method_3_2).0 < -9.19) && ((p_m_method_3_2).1 == false) && (-26.64 < (p_m_method_3_2).2 < -26.44));
	ensures (((p_m_method_3_1 == 'g') && (-9.39 < (p_m_method_3_2).0 < -9.19) && ((p_m_method_3_2).1 == false) && (-26.64 < (p_m_method_3_2).2 < -26.44)) ==> ((ret_1 == 32)));
{
	var v_array_7: array<bool> := new bool[4] [false, true, false, true];
	var v_array_8: array<bool> := new bool[5] [true, true, true, false, false];
	var v_array_9: array<bool> := new bool[3] [true, false, true];
	var v_array_10: array<bool> := new bool[3] [true, true, true];
	var v_seq_4: seq<array<bool>> := [v_array_9, v_array_10];
	var v_int_18: int := 11;
	var v_seq_15: seq<array<bool>> := v_seq_4;
	var v_int_40: int := v_int_18;
	var v_int_41: int := safe_index_seq(v_seq_15, v_int_40);
	v_int_18 := v_int_41;
	var v_array_11: array<bool> := new bool[3] [false, true, false];
	var v_seq_5: seq<bool> := [false, false];
	var v_int_19: int := 18;
	var v_seq_16: seq<bool> := v_seq_5;
	var v_int_42: int := v_int_19;
	var v_int_43: int := safe_index_seq(v_seq_16, v_int_42);
	v_int_19 := v_int_43;
	var v_DT_1_1_1: DT_1<bool> := DT_1_1;
	var v_DT_1_1_2: DT_1<bool> := DT_1_1;
	var v_DT_1_1_3: DT_1<bool> := DT_1_1;
	var v_DT_1_1_4: DT_1<bool> := DT_1_1;
	var v_DT_1_1_5: DT_1<bool> := DT_1_1;
	var v_DT_1_1_6: DT_1<bool> := DT_1_1;
	var v_DT_1_1_7: DT_1<bool> := DT_1_1;
	var v_DT_1_1_8: DT_1<bool> := DT_1_1;
	var v_DT_1_1_9: DT_1<bool> := DT_1_1;
	var v_array_12: array<real> := new real[3] [-2.86, 11.41, 2.26];
	var v_array_13: array<real> := new real[4] [-1.80, 20.37, 23.55, -21.99];
	var v_array_14: array<real> := new real[3] [-8.72, -2.64, -23.03];
	var v_array_15: array<real> := new real[4] [1.83, 11.38, -17.74, -12.51];
	var v_array_16: array<array<real>> := new array<real>[4] [v_array_12, v_array_13, v_array_14, v_array_15];
	var v_array_17: array<real> := new real[3];
	v_array_17[0] := -23.52;
	v_array_17[1] := -19.21;
	v_array_17[2] := 9.24;
	var v_array_18: array<real> := new real[4] [1.48, 25.26, 10.62, -12.37];
	var v_array_19: array<real> := new real[3] [9.82, -21.42, -8.83];
	var v_array_20: array<real> := new real[5] [-7.06, -16.69, -25.67, 18.41, 16.49];
	var v_array_21: array<array<real>> := new array<real>[4] [v_array_17, v_array_18, v_array_19, v_array_20];
	var v_map_4: map<array<array<real>>, int> := map[v_array_16 := 29, v_array_21 := -22];
	var v_array_22: array<real> := new real[3] [-23.84, 28.46, -3.74];
	var v_array_23: array<real> := new real[5] [-2.71, -24.77, -3.96, 16.39, 19.03];
	var v_array_24: array<real> := new real[3] [20.02, 10.27, -13.07];
	var v_array_25: array<real> := new real[4] [24.55, 23.95, 25.25, -13.39];
	var v_array_26: array<array<real>> := new array<real>[4] [v_array_22, v_array_23, v_array_24, v_array_25];
	var v_array_27: array<array<real>> := v_array_26;
	var v_int_20: int := (if ((v_array_27 in v_map_4)) then (v_map_4[v_array_27]) else (0));
	var v_int_21: int := v_int_18;
	var v_int_22: int := safe_division(v_int_20, v_int_21);
	var v_map_5: map<array<bool>, int>, v_set_1: set<DT_1<bool>>, v_int_23: int := (match 'e' {
		case 'l' => map[v_array_7 := -25]
		case _ => map[v_array_8 := 14]
	})[(if ((|v_seq_4| > 0)) then (v_seq_4[v_int_18]) else (v_array_11)) := v_int_18], (if ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_19]) else (true))) then ((if (false) then ({v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3, v_DT_1_1_4}) else ({v_DT_1_1_5, v_DT_1_1_6}))) else (({v_DT_1_1_7, v_DT_1_1_8, v_DT_1_1_9} * {}))), v_int_22;
	var v_seq_6: seq<map<bool, int>> := [map[true := 29, false := 9], map[true := 23, false := 27], map[false := 19, true := 0], map[false := 3, true := 6]];
	var v_int_26: int := 13;
	var v_seq_17: seq<map<bool, int>> := v_seq_6;
	var v_int_44: int := v_int_26;
	var v_int_45: int := safe_index_seq(v_seq_17, v_int_44);
	v_int_26 := v_int_45;
	var v_map_7: map<bool, int> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_26]) else (map[false := 7]));
	var v_bool_3: bool := p_m_method_3_2.1;
	var v_map_6: map<bool, int> := map[true := 19, false := 3];
	var v_bool_2: bool := false;
	var v_int_24: int := (if ((v_bool_3 in v_map_7)) then (v_map_7[v_bool_3]) else ((if ((v_bool_2 in v_map_6)) then (v_map_6[v_bool_2]) else (27))));
	var v_seq_7: seq<int> := [7, 4, 6, 18];
	var v_seq_18: seq<int> := v_seq_7;
	var v_int_48: int := 18;
	var v_int_49: int := 0;
	var v_int_50: int, v_int_51: int := safe_subsequence(v_seq_18, v_int_48, v_int_49);
	var v_int_46: int, v_int_47: int := v_int_50, v_int_51;
	var v_seq_8: seq<int> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_46..v_int_47]) else (v_seq_7));
	var v_int_27: int := (-14 * 4);
	var v_int_25: int := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_27]) else (v_int_27));
	while (v_int_24 < v_int_25) 
		decreases v_int_25 - v_int_24;
		invariant (v_int_24 <= v_int_25);
	{
		v_int_24 := (v_int_24 + 1);
		var v_seq_9: seq<int> := [];
		var v_int_28: int := 18;
		var v_map_8: map<bool, seq<real>> := (if (true) then (map[true := [], true := [-20.41, -28.62, -11.80], false := [-21.98, -21.26, -19.25], true := [-11.96, 26.21, -26.25], true := []]) else (map[true := [2.78, 25.34], true := [], true := [13.09, -21.70, 3.75, -15.63], false := [-13.65, 14.30]]));
		var v_bool_4: bool := (false !in multiset{false});
		var v_map_9: map<bool, map<bool, real>> := map[false := map[false := -11.17]];
		var v_bool_5: bool := true;
		var v_map_10: map<bool, real> := (if ((v_bool_5 in v_map_9)) then (v_map_9[v_bool_5]) else (map[false := 9.70]));
		var v_bool_6: bool := false;
		var v_bool_7: bool := false;
		var v_bool_8: bool := true;
		var v_bool_9: bool := m_method_4(v_bool_6, v_bool_7, v_bool_8);
		var v_bool_18: bool := v_bool_9;
		var v_bool_16: bool := true;
		var v_bool_17: bool := true;
		var v_real_1: real := m_method_5(v_bool_16, v_bool_17);
		var v_map_11: map<bool, real> := v_map_10;
		var v_bool_19: bool := v_bool_16;
		var v_int_29: int, v_seq_10: seq<real>, v_real_2: real, v_real_3: real := ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_28]) else (11)) / v_int_24), (if ((v_bool_4 in v_map_8)) then (v_map_8[v_bool_4]) else (([22.44] + [-4.19]))), (if ((v_bool_18 in v_map_10)) then (v_map_10[v_bool_18]) else (v_real_1)), (if ((v_bool_19 in v_map_11)) then (v_map_11[v_bool_19]) else (v_array_13[0]));
	}
	var v_map_12: map<char, bool> := map['q' := true, 'I' := true, 'o' := true];
	var v_char_1: char := 'Z';
	v_array_11[0], v_bool_3, v_array_10[1] := (v_array_10[0] !in (match 'P' {
		case 'G' => {true, true, true, true}
		case _ => {false, true, false, true}
	})), (match 'o' {
		case 's' => (match 'U' {
			case _ => true
		})
		case _ => (if ((v_char_1 in v_map_12)) then (v_map_12[v_char_1]) else (false))
	}), (p_m_method_3_1 !in (if (true) then (map['O' := 'h', 'b' := 'P', 'X' := 'M', 'M' := 'j']) else (map['p' := 'S', 'k' := 'j', 'A' := 'z', 'b' := 'y'])));
	var v_real_bool_real_4: (real, bool, real) := (-9.29, false, -26.54);
	print "v_array_16[3]", " ", (v_array_16[3] == v_array_15), " ", "v_array_20[1]", " ", (v_array_20[1] == -16.69), " ", "v_array_11[2]", " ", v_array_11[2], " ", "v_array_14[1]", " ", (v_array_14[1] == -2.64), " ", "v_array_17[0]", " ", (v_array_17[0] == -23.52), " ", "v_array_25[3]", " ", (v_array_25[3] == -13.39), " ", "v_array_26[0]", " ", (v_array_26[0] == v_array_22), " ", "v_array_23[1]", " ", (v_array_23[1] == -24.77), " ", "v_array_19[2]", " ", (v_array_19[2] == -8.83), " ", "v_array_9[0]", " ", v_array_9[0], " ", "v_array_16[2]", " ", (v_array_16[2] == v_array_14), " ", "v_array_14[0]", " ", (v_array_14[0] == -8.72), " ", "v_array_20[0]", " ", (v_array_20[0] == -7.06), " ", "v_array_19[1]", " ", (v_array_19[1] == -21.42), " ", "v_array_13[3]", " ", (v_array_13[3] == -21.99), " ", "v_array_22[2]", " ", (v_array_22[2] == -3.74), " ", "v_array_11[1]", " ", v_array_11[1], " ", "p_m_method_3_2.1", " ", p_m_method_3_2.1, " ", "p_m_method_3_2.2", " ", (p_m_method_3_2.2 == -26.54), " ", "p_m_method_3_2.0", " ", (p_m_method_3_2.0 == -9.29), " ", "v_set_1", " ", (v_set_1 == {}), " ", "v_array_26[1]", " ", (v_array_26[1] == v_array_23), " ", "v_array_23[2]", " ", (v_array_23[2] == -3.96), " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_array_17[2]", " ", (v_array_17[2] == 9.24), " ", "v_array_21[0]", " ", (v_array_21[0] == v_array_17), " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_array_12[1]", " ", (v_array_12[1] == 11.41), " ", "v_array_15[0]", " ", (v_array_15[0] == 1.83), " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_array_20[3]", " ", (v_array_20[3] == 18.41), " ", "v_array_25[1]", " ", (v_array_25[1] == 23.95), " ", "v_array_19", " ", (v_array_19 == v_array_19), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "p_m_method_3_2", " ", (p_m_method_3_2 == v_real_bool_real_4), " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'g'), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_map_5", " ", "v_map_4", " ", (v_map_4 == map[v_array_16 := 29, v_array_21 := -22]), " ", "v_map_7", " ", (v_map_7 == map[false := 9, true := 29]), " ", "v_map_6", " ", (v_map_6 == map[false := 3, true := 19]), " ", "v_array_14[2]", " ", (v_array_14[2] == -23.03), " ", "v_array_17[1]", " ", (v_array_17[1] == -19.21), " ", "v_array_20[2]", " ", (v_array_20[2] == -25.67), " ", "v_array_12[0]", " ", (v_array_12[0] == -2.86), " ", "v_array_25[2]", " ", (v_array_25[2] == 25.25), " ", "v_array_23[0]", " ", (v_array_23[0] == -2.71), " ", "v_array_15[2]", " ", (v_array_15[2] == -17.74), " ", "v_array_13[0]", " ", (v_array_13[0] == -1.80), " ", "v_array_18[1]", " ", (v_array_18[1] == 25.26), " ", "v_array_21[2]", " ", (v_array_21[2] == v_array_19), " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_array_24[2]", " ", (v_array_24[2] == -13.07), " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_18[0]", " ", (v_array_18[0] == 1.48), " ", "v_array_21[1]", " ", (v_array_21[1] == v_array_18), " ", "v_array_12[2]", " ", (v_array_12[2] == 2.26), " ", "v_array_15[1]", " ", (v_array_15[1] == 11.38), " ", "v_array_20[4]", " ", (v_array_20[4] == 16.49), " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_array_25[0]", " ", (v_array_25[0] == 24.55), " ", "v_array_27", " ", (v_array_27 == v_array_26), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_array_16[1]", " ", (v_array_16[1] == v_array_13), " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_array_19[0]", " ", (v_array_19[0] == 9.82), " ", "v_array_13[2]", " ", (v_array_13[2] == 23.55), " ", "v_array_22[1]", " ", (v_array_22[1] == 28.46), " ", "v_array_11[0]", " ", v_array_11[0], " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_array_26[2]", " ", (v_array_26[2] == v_array_24), " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_array_23[3]", " ", (v_array_23[3] == 16.39), " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_array_24[0]", " ", (v_array_24[0] == 20.02), " ", "v_int_25", " ", v_int_25, " ", "v_array_18[3]", " ", (v_array_18[3] == -12.37), " ", "v_array_9[2]", " ", v_array_9[2], " ", "v_int_20", " ", v_int_20, " ", "v_array_15[3]", " ", (v_array_15[3] == -12.51), " ", "v_array_13[1]", " ", (v_array_13[1] == 20.37), " ", "v_array_18[2]", " ", (v_array_18[2] == 10.62), " ", "v_array_22[0]", " ", (v_array_22[0] == -23.84), " ", "v_array_16[0]", " ", (v_array_16[0] == v_array_12), " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_array_21[3]", " ", (v_array_21[3] == v_array_20), " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", (v_seq_6 == [map[false := 9, true := 29], map[false := 27, true := 23], map[false := 19, true := 0], map[false := 3, true := 6]]), " ", "v_seq_5", " ", v_seq_5, " ", "v_array_26[3]", " ", (v_array_26[3] == v_array_25), " ", "v_seq_4", " ", (v_seq_4 == [v_array_9, v_array_10]), " ", "v_array_23[4]", " ", (v_array_23[4] == 19.03), " ", "v_array_24[1]", " ", (v_array_24[1] == 10.27), " ", "v_array_9[1]", " ", v_array_9[1], "\n";
	return (if (v_array_9[0]) then ((16 + 16)) else ((16.45).Floor));
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: int, p_m_method_2_3: bool) returns (ret_1: map<int, bool>)
	requires ((p_m_method_2_2 == 5) && (p_m_method_2_1 == 15) && (p_m_method_2_3 == true));
	ensures (((p_m_method_2_2 == 5) && (p_m_method_2_1 == 15) && (p_m_method_2_3 == true)) ==> ((ret_1 == map[13 := true])));
{
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
	return map[13 := true];
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: int) returns (ret_1: map<int, bool>)
	requires ((p_m_method_1_1 == 4) && (p_m_method_1_2 == -5));
	ensures (((p_m_method_1_1 == 4) && (p_m_method_1_2 == -5)) ==> ((ret_1 == map[13 := true])));
{
	var v_int_7: int := 15;
	var v_int_8: int := 5;
	var v_bool_1: bool := true;
	var v_map_1: map<int, bool> := m_method_2(v_int_7, v_int_8, v_bool_1);
	print "v_bool_1", " ", v_bool_1, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[13 := true]), "\n";
	return v_map_1;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_int_9: int := (if (false) then (1) else (4));
	var v_int_10: int := (4 - 9);
	var v_map_2: map<int, bool> := m_method_1(v_int_9, v_int_10);
	var v_seq_3: seq<int> := [20, 23, 16];
	var v_int_11: int := 3;
	var v_seq_19: seq<int> := v_seq_3;
	var v_int_52: int := v_int_11;
	var v_int_53: int := safe_index_seq(v_seq_19, v_int_52);
	v_int_11 := v_int_53;
	var v_int_real_real_1: (int, real, real) := (12, -13.41, 3.93);
	var v_bool_real_int_1: (bool, real, int) := (true, -15.94, 3);
	var v_int_real_real_bool_real_int_set_1: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_1, v_bool_real_int_1, {13, 6, 18, 22});
	var v_int_real_real_2: (int, real, real) := (7, -1.07, -21.32);
	var v_bool_real_int_2: (bool, real, int) := (true, 13.67, 20);
	var v_int_real_real_bool_real_int_set_2: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_2, v_bool_real_int_2, {17, 19});
	var v_int_real_real_3: (int, real, real) := (24, -13.16, -26.23);
	var v_bool_real_int_3: (bool, real, int) := (true, 2.08, 22);
	var v_int_real_real_bool_real_int_set_3: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_3, v_bool_real_int_3, {18});
	var v_map_3: map<((int, real, real), (bool, real, int), set<int>), int> := map[v_int_real_real_bool_real_int_set_1 := 22, v_int_real_real_bool_real_int_set_2 := 21, v_int_real_real_bool_real_int_set_3 := 7];
	var v_int_real_real_4: (int, real, real) := (24, -4.02, -25.07);
	var v_bool_real_int_4: (bool, real, int) := (false, -11.15, 1);
	var v_int_real_real_bool_real_int_set_4: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_4, v_bool_real_int_4, {23, 20, 3, -21});
	var v_int_real_real_bool_real_int_set_5: ((int, real, real), (bool, real, int), set<int>) := v_int_real_real_bool_real_int_set_4;
	var v_int_12: int := (if (false) then (12) else (14));
	var v_array_1: array<char> := new char[3] ['V', 'H', 'C'];
	var v_array_2: array<char> := new char[5] ['S', 'u', 'i', 'm', 'L'];
	var v_array_3: array<char> := new char[5] ['h', 'Z', 'H', 'g', 'Y'];
	var v_array_4: array<char> := new char[4] ['s', 'b', 'P', 'U'];
	var v_array_5: array<char> := new char[4];
	v_array_5[0] := 'x';
	v_array_5[1] := 'g';
	v_array_5[2] := 'b';
	v_array_5[3] := 'I';
	var v_array_6: array<array<char>> := new array<char>[5] [v_array_1, v_array_2, v_array_3, v_array_4, v_array_5];
	var v_int_13: int := v_array_6.Length;
	var v_int_14: int := safe_modulus(v_int_12, v_int_13);
	var v_int_15: int := v_int_13;
	var v_bool_int_1: (bool, int) := (false, 22);
	var v_char_set_bool_int_1: (char, set<bool>, (bool, int)) := ('m', {false}, v_bool_int_1);
	var v_bool_int_2: (bool, int) := (true, 17);
	var v_char_set_bool_int_2: (char, set<bool>, (bool, int)) := ('y', {false}, v_bool_int_2);
	var v_bool_int_3: (bool, int) := (false, 9);
	var v_char_set_bool_int_3: (char, set<bool>, (bool, int)) := ('u', {false}, v_bool_int_3);
	var v_int_16: int := |multiset{v_char_set_bool_int_1, v_char_set_bool_int_2, v_char_set_bool_int_3}|;
	var v_int_17: int := safe_division(v_int_15, v_int_16);
	var v_char_2: char := 'r';
	var v_char_3: char := m_method_7(v_char_2);
	var v_char_4: char := (match 'e' {
		case 'w' => (match 'u' {
			case _ => 'u'
		})
		case 'h' => v_char_3
		case _ => v_array_5[1]
	});
	var v_real_bool_real_1: (real, bool, real) := (-9.29, false, -26.54);
	var v_real_bool_real_2: (real, bool, real) := (14.13, false, 24.74);
	var v_seq_12: seq<(real, bool, real)> := ([] + [v_real_bool_real_1, v_real_bool_real_2]);
	var v_seq_11: seq<int> := [22, -3, 21, -6];
	var v_int_30: int := 10;
	var v_seq_13: seq<int> := v_seq_11;
	var v_int_36: int := v_int_30;
	var v_int_37: int := safe_index_seq(v_seq_13, v_int_36);
	v_int_30 := v_int_37;
	var v_int_31: int := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_30]) else (24));
	var v_seq_14: seq<(real, bool, real)> := v_seq_12;
	var v_int_38: int := v_int_31;
	var v_int_39: int := safe_index_seq(v_seq_14, v_int_38);
	v_int_31 := v_int_39;
	var v_real_bool_real_3: (real, bool, real) := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_31]) else (v_real_bool_real_1));
	var v_int_32: int := m_method_3(v_char_4, v_real_bool_real_3);
	var v_map_13: map<int, bool>, v_set_2: set<int>, v_int_33: int, v_int_34: int, v_int_35: int := (if ((match 27 {
		case -17 => (match -18 {
			case _ => false
		})
		case 13 => (if (true) then (true) else (false))
		case _ => false
	})) then (v_map_2) else (v_map_2)), {((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_11]) else (4)) % (if ((v_int_real_real_bool_real_int_set_5 in v_map_3)) then (v_map_3[v_int_real_real_bool_real_int_set_5]) else (16))), v_bool_real_int_1.2, v_bool_real_int_3.2, v_int_14}, v_bool_real_int_4.2, (v_int_real_real_3.0 - v_int_17), v_int_32;
	var v_bool_int_4: (bool, int) := (false, 9);
	var v_bool_int_5: (bool, int) := (false, 22);
	assert ((v_bool_real_int_1.1 == -15.94) && (v_bool_int_3 == v_bool_int_4) && (v_char_set_bool_int_1.2 == v_bool_int_5) && (v_array_2[2] == 'i'));
	expect ((v_bool_real_int_1.1 == -15.94) && (v_bool_int_3 == v_bool_int_4) && (v_char_set_bool_int_1.2 == v_bool_int_5) && (v_array_2[2] == 'i'));
	assert ((v_int_real_real_2.2 == -21.32) && (v_int_real_real_3.2 == -26.23) && (v_bool_real_int_4.1 == -11.15));
	expect ((v_int_real_real_2.2 == -21.32) && (v_int_real_real_3.2 == -26.23) && (v_bool_real_int_4.1 == -11.15));
	var v_int_real_real_5: (int, real, real) := (24, -4.02, -25.07);
	var v_int_real_real_6: (int, real, real) := (24, -13.16, -26.23);
	var v_int_real_real_7: (int, real, real) := (7, -1.07, -21.32);
	var v_int_real_real_8: (int, real, real) := (12, -13.41, 3.93);
	var v_bool_real_int_5: (bool, real, int) := (false, -11.15, 1);
	var v_int_real_real_9: (int, real, real) := (24, -4.02, -25.07);
	var v_bool_real_int_6: (bool, real, int) := (true, 2.08, 22);
	var v_int_real_real_10: (int, real, real) := (24, -13.16, -26.23);
	var v_int_real_real_11: (int, real, real) := (24, -13.16, -26.23);
	var v_bool_real_int_7: (bool, real, int) := (true, 2.08, 22);
	var v_int_real_real_bool_real_int_set_6: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_11, v_bool_real_int_7, {18});
	var v_int_real_real_12: (int, real, real) := (12, -13.41, 3.93);
	var v_bool_real_int_8: (bool, real, int) := (true, -15.94, 3);
	var v_int_real_real_bool_real_int_set_7: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_12, v_bool_real_int_8, {18, 6, 22, 13});
	var v_int_real_real_13: (int, real, real) := (7, -1.07, -21.32);
	var v_bool_real_int_9: (bool, real, int) := (true, 13.67, 20);
	var v_int_real_real_bool_real_int_set_8: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_13, v_bool_real_int_9, {17, 19});
	var v_real_bool_real_5: (real, bool, real) := (14.13, false, 24.74);
	var v_real_bool_real_6: (real, bool, real) := (-9.29, false, -26.54);
	var v_real_bool_real_7: (real, bool, real) := (-9.29, false, -26.54);
	var v_bool_real_int_10: (bool, real, int) := (true, 13.67, 20);
	var v_int_real_real_14: (int, real, real) := (7, -1.07, -21.32);
	var v_bool_int_6: (bool, int) := (true, 17);
	var v_char_set_bool_int_4: (char, set<bool>, (bool, int)) := ('y', {false}, v_bool_int_6);
	var v_bool_int_7: (bool, int) := (false, 9);
	var v_char_set_bool_int_5: (char, set<bool>, (bool, int)) := ('u', {false}, v_bool_int_7);
	var v_bool_int_8: (bool, int) := (false, 22);
	var v_char_set_bool_int_6: (char, set<bool>, (bool, int)) := ('m', {false}, v_bool_int_8);
	var v_real_bool_real_8: (real, bool, real) := (-9.29, false, -26.54);
	var v_real_bool_real_9: (real, bool, real) := (14.13, false, 24.74);
	var v_bool_real_int_11: (bool, real, int) := (true, 13.67, 20);
	var v_int_real_real_15: (int, real, real) := (24, -4.02, -25.07);
	var v_bool_real_int_12: (bool, real, int) := (false, -11.15, 1);
	var v_int_real_real_bool_real_int_set_9: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_15, v_bool_real_int_12, {3, 20, -21, 23});
	var v_bool_real_int_13: (bool, real, int) := (true, -15.94, 3);
	var v_int_real_real_16: (int, real, real) := (24, -4.02, -25.07);
	var v_bool_real_int_14: (bool, real, int) := (false, -11.15, 1);
	var v_int_real_real_bool_real_int_set_10: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_16, v_bool_real_int_14, {3, 20, -21, 23});
	var v_int_real_real_17: (int, real, real) := (24, -13.16, -26.23);
	var v_bool_real_int_15: (bool, real, int) := (true, 2.08, 22);
	var v_int_real_real_bool_real_int_set_11: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_17, v_bool_real_int_15, {18});
	var v_bool_real_int_16: (bool, real, int) := (false, -11.15, 1);
	var v_int_real_real_18: (int, real, real) := (7, -1.07, -21.32);
	var v_bool_real_int_17: (bool, real, int) := (true, 13.67, 20);
	var v_int_real_real_bool_real_int_set_12: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_18, v_bool_real_int_17, {17, 19});
	var v_bool_real_int_18: (bool, real, int) := (true, 2.08, 22);
	var v_int_real_real_19: (int, real, real) := (12, -13.41, 3.93);
	var v_bool_real_int_19: (bool, real, int) := (true, -15.94, 3);
	var v_int_real_real_bool_real_int_set_13: ((int, real, real), (bool, real, int), set<int>) := (v_int_real_real_19, v_bool_real_int_19, {18, 6, 22, 13});
	var v_bool_real_int_20: (bool, real, int) := (true, -15.94, 3);
	var v_int_real_real_20: (int, real, real) := (12, -13.41, 3.93);
	print "v_array_5[3]", " ", (v_array_5[3] == 'I'), " ", "v_bool_int_2.1", " ", v_bool_int_2.1, " ", "v_bool_int_2.0", " ", v_bool_int_2.0, " ", "v_char_set_bool_int_2.2", " ", v_char_set_bool_int_2.2, " ", "v_char_set_bool_int_2.1", " ", (v_char_set_bool_int_2.1 == {false}), " ", "v_char_set_bool_int_2.0", " ", (v_char_set_bool_int_2.0 == 'y'), " ", "v_map_13", " ", (v_map_13 == map[13 := true]), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == -1.07), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == -21.32), " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_5), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_6), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_7), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_8), " ", "v_array_3[0]", " ", (v_array_3[0] == 'h'), " ", "v_array_5[2]", " ", (v_array_5[2] == 'b'), " ", "v_array_2[3]", " ", (v_array_2[3] == 'm'), " ", "v_bool_real_int_4.0", " ", v_bool_real_int_4.0, " ", "v_int_real_real_bool_real_int_set_4.2", " ", (v_int_real_real_bool_real_int_set_4.2 == {3, 20, -21, 23}), " ", "v_bool_real_int_4.1", " ", (v_bool_real_int_4.1 == -11.15), " ", "v_int_real_real_bool_real_int_set_4.1", " ", (v_int_real_real_bool_real_int_set_4.1 == v_bool_real_int_5), " ", "v_bool_real_int_4.2", " ", v_bool_real_int_4.2, " ", "v_int_real_real_bool_real_int_set_4.0", " ", (v_int_real_real_bool_real_int_set_4.0 == v_int_real_real_9), " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_set_2", " ", (v_set_2 == {3, 4, 22}), " ", "v_array_2[4]", " ", (v_array_2[4] == 'L'), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, " ", "v_array_3[1]", " ", (v_array_3[1] == 'Z'), " ", "v_array_6[0]", " ", (v_array_6[0] == v_array_1), " ", "v_bool_int_3.0", " ", v_bool_int_3.0, " ", "v_char_set_bool_int_3.2", " ", v_char_set_bool_int_3.2, " ", "v_char_set_bool_int_3.1", " ", (v_char_set_bool_int_3.1 == {false}), " ", "v_char_set_bool_int_3.0", " ", (v_char_set_bool_int_3.0 == 'u'), " ", "v_bool_int_3.1", " ", v_bool_int_3.1, " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == -26.23), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == -13.16), " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[1]", " ", (v_array_2[1] == 'u'), " ", "v_array_5[0]", " ", (v_array_5[0] == 'x'), " ", "v_array_4[3]", " ", (v_array_4[3] == 'U'), " ", "v_bool_real_int_3.0", " ", v_bool_real_int_3.0, " ", "v_bool_real_int_3.1", " ", (v_bool_real_int_3.1 == 2.08), " ", "v_bool_real_int_3.2", " ", v_bool_real_int_3.2, " ", "v_int_real_real_bool_real_int_set_3.2", " ", (v_int_real_real_bool_real_int_set_3.2 == {18}), " ", "v_int_real_real_bool_real_int_set_3.1", " ", (v_int_real_real_bool_real_int_set_3.1 == v_bool_real_int_6), " ", "v_int_real_real_bool_real_int_set_3.0", " ", (v_int_real_real_bool_real_int_set_3.0 == v_int_real_real_10), " ", "v_char_4", " ", (v_char_4 == 'g'), " ", "v_map_3", " ", (v_map_3 == map[v_int_real_real_bool_real_int_set_6 := 7, v_int_real_real_bool_real_int_set_7 := 22, v_int_real_real_bool_real_int_set_8 := 21]), " ", "v_map_2", " ", (v_map_2 == map[13 := true]), " ", "v_array_2[2]", " ", (v_array_2[2] == 'i'), " ", "v_array_5[1]", " ", (v_array_5[1] == 'g'), " ", "v_real_bool_real_2", " ", (v_real_bool_real_2 == v_real_bool_real_5), " ", "v_real_bool_real_3", " ", (v_real_bool_real_3 == v_real_bool_real_6), " ", "v_array_6[4]", " ", (v_array_6[4] == v_array_5), " ", "v_real_bool_real_1", " ", (v_real_bool_real_1 == v_real_bool_real_7), " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -4.02), " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == -25.07), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_array_1[2]", " ", (v_array_1[2] == 'C'), " ", "v_array_4[1]", " ", (v_array_4[1] == 'b'), " ", "v_array_3[4]", " ", (v_array_3[4] == 'Y'), " ", "v_bool_real_int_2.1", " ", (v_bool_real_int_2.1 == 13.67), " ", "v_bool_real_int_2.2", " ", v_bool_real_int_2.2, " ", "v_int_real_real_bool_real_int_set_2.2", " ", (v_int_real_real_bool_real_int_set_2.2 == {17, 19}), " ", "v_int_real_real_bool_real_int_set_2.1", " ", (v_int_real_real_bool_real_int_set_2.1 == v_bool_real_int_10), " ", "v_int_real_real_bool_real_int_set_2.0", " ", (v_int_real_real_bool_real_int_set_2.0 == v_int_real_real_14), " ", "v_real_bool_real_1.0", " ", (v_real_bool_real_1.0 == -9.29), " ", "v_array_2[0]", " ", (v_array_2[0] == 'S'), " ", "v_real_bool_real_1.1", " ", v_real_bool_real_1.1, " ", "v_real_bool_real_1.2", " ", (v_real_bool_real_1.2 == -26.54), " ", "v_bool_real_int_2.0", " ", v_bool_real_int_2.0, " ", "v_array_4[2]", " ", (v_array_4[2] == 'P'), " ", "v_array_6[2]", " ", (v_array_6[2] == v_array_3), " ", "v_char_set_bool_int_1.0", " ", (v_char_set_bool_int_1.0 == 'm'), " ", "v_char_set_bool_int_2", " ", (v_char_set_bool_int_2 == v_char_set_bool_int_4), " ", "v_char_set_bool_int_3", " ", (v_char_set_bool_int_3 == v_char_set_bool_int_5), " ", "v_char_set_bool_int_1", " ", (v_char_set_bool_int_1 == v_char_set_bool_int_6), " ", "v_bool_int_1.1", " ", v_bool_int_1.1, " ", "v_char_set_bool_int_1.2", " ", v_char_set_bool_int_1.2, " ", "v_char_set_bool_int_1.1", " ", (v_char_set_bool_int_1.1 == {false}), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == 3.93), " ", "v_bool_int_1.0", " ", v_bool_int_1.0, " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == -13.41), " ", "v_bool_int_1", " ", v_bool_int_1, " ", "v_bool_int_3", " ", v_bool_int_3, " ", "v_bool_int_2", " ", v_bool_int_2, " ", "v_seq_11", " ", v_seq_11, " ", "v_seq_12", " ", (v_seq_12 == [v_real_bool_real_8, v_real_bool_real_9]), " ", "v_int_9", " ", v_int_9, " ", "v_bool_real_int_2", " ", (v_bool_real_int_2 == v_bool_real_int_11), " ", "v_int_real_real_bool_real_int_set_5", " ", (v_int_real_real_bool_real_int_set_5 == v_int_real_real_bool_real_int_set_9), " ", "v_bool_real_int_1", " ", (v_bool_real_int_1 == v_bool_real_int_13), " ", "v_int_real_real_bool_real_int_set_4", " ", (v_int_real_real_bool_real_int_set_4 == v_int_real_real_bool_real_int_set_10), " ", "v_int_real_real_bool_real_int_set_3", " ", (v_int_real_real_bool_real_int_set_3 == v_int_real_real_bool_real_int_set_11), " ", "v_bool_real_int_4", " ", (v_bool_real_int_4 == v_bool_real_int_16), " ", "v_int_real_real_bool_real_int_set_2", " ", (v_int_real_real_bool_real_int_set_2 == v_int_real_real_bool_real_int_set_12), " ", "v_bool_real_int_3", " ", (v_bool_real_int_3 == v_bool_real_int_18), " ", "v_array_1[0]", " ", (v_array_1[0] == 'V'), " ", "v_array_3[2]", " ", (v_array_3[2] == 'H'), " ", "v_array_6[1]", " ", (v_array_6[1] == v_array_2), " ", "v_bool_real_int_1.2", " ", v_bool_real_int_1.2, " ", "v_array_6[3]", " ", (v_array_6[3] == v_array_4), " ", "v_int_real_real_bool_real_int_set_1", " ", (v_int_real_real_bool_real_int_set_1 == v_int_real_real_bool_real_int_set_13), " ", "v_int_real_real_bool_real_int_set_1.2", " ", (v_int_real_real_bool_real_int_set_1.2 == {18, 6, 22, 13}), " ", "v_int_real_real_bool_real_int_set_1.1", " ", (v_int_real_real_bool_real_int_set_1.1 == v_bool_real_int_20), " ", "v_int_real_real_bool_real_int_set_1.0", " ", (v_int_real_real_bool_real_int_set_1.0 == v_int_real_real_20), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_int_17", " ", v_int_17, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_1[1]", " ", (v_array_1[1] == 'H'), " ", "v_real_bool_real_2.2", " ", (v_real_bool_real_2.2 == 24.74), " ", "v_real_bool_real_2.0", " ", (v_real_bool_real_2.0 == 14.13), " ", "v_real_bool_real_2.1", " ", v_real_bool_real_2.1, " ", "v_array_3[3]", " ", (v_array_3[3] == 'g'), " ", "v_array_4[0]", " ", (v_array_4[0] == 's'), " ", "v_bool_real_int_1.0", " ", v_bool_real_int_1.0, " ", "v_bool_real_int_1.1", " ", (v_bool_real_int_1.1 == -15.94), "\n";
	return ;
}
