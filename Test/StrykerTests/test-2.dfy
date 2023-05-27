// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1
datatype DT_2<T_3> = DT_2_1 | DT_2_2(DT_2_2_1: T_3, DT_2_2_2: T_3, DT_2_2_3: T_3)
datatype DT_3 = DT_3_1 | DT_3_2 | DT_3_3(DT_3_3_1: multiset<int>)
datatype DT_4 = DT_4_1 | DT_4_2 | DT_4_3(DT_4_3_1: DT_2<bool>, DT_4_3_2: multiset<bool>) | DT_4_5
datatype DT_5<T_4> = DT_5_1
datatype DT_6<T_5, T_6> = DT_6_1 | DT_6_2(DT_6_2_1: T_6, DT_6_2_2: T_6, DT_6_2_3: T_5, DT_6_2_4: T_6) | DT_6_4(DT_6_4_1: T_5, DT_6_4_2: set<bool>, DT_6_4_3: T_5, DT_6_4_4: T_6) | DT_6_5(DT_6_5_1: T_5)
datatype DT_7 = DT_7_1
datatype DT_8 = DT_8_1
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

method m_method_8(p_m_method_8_1: seq<int>, p_m_method_8_2: (bool, int, bool), p_m_method_8_3: array<real>) returns (ret_1: array<array<bool>>)
	requires (((p_m_method_8_2).0 == false) && ((p_m_method_8_2).1 == 4) && ((p_m_method_8_2).2 == false) && |p_m_method_8_1| == 1 && (p_m_method_8_1[0] == 21) && p_m_method_8_3.Length == 4 && (-0.19 < p_m_method_8_3[0] < 0.01) && (-1.94 < p_m_method_8_3[1] < -1.74) && (14.18 < p_m_method_8_3[2] < 14.38) && (-8.95 < p_m_method_8_3[3] < -8.75)) || (((p_m_method_8_2).0 == false) && ((p_m_method_8_2).1 == 4) && ((p_m_method_8_2).2 == false) && |p_m_method_8_1| == 3 && (p_m_method_8_1[0] == 17) && (p_m_method_8_1[1] == 3) && (p_m_method_8_1[2] == 9) && p_m_method_8_3.Length == 4 && (20.34 < p_m_method_8_3[0] < 20.54) && (-2.14 < p_m_method_8_3[1] < -1.94) && (-1.91 < p_m_method_8_3[2] < -1.71) && (10.28 < p_m_method_8_3[3] < 10.48));
	ensures ((((p_m_method_8_2).0 == false) && ((p_m_method_8_2).1 == 4) && ((p_m_method_8_2).2 == false) && |p_m_method_8_1| == 1 && (p_m_method_8_1[0] == 21) && p_m_method_8_3.Length == 4 && (-0.19 < p_m_method_8_3[0] < 0.01) && (-1.94 < p_m_method_8_3[1] < -1.74) && (14.18 < p_m_method_8_3[2] < 14.38) && (-8.95 < p_m_method_8_3[3] < -8.75)) ==> (ret_1.Length == 3 && ret_1[0].Length == 3 && (ret_1[0][0] == true) && (ret_1[0][1] == true) && (ret_1[0][2] == true) && ret_1[1].Length == 5 && (ret_1[1][0] == false) && (ret_1[1][1] == false) && (ret_1[1][2] == false) && (ret_1[1][3] == true) && (ret_1[1][4] == false) && ret_1[2].Length == 4 && (ret_1[2][0] == true) && (ret_1[2][1] == true) && (ret_1[2][2] == true) && (ret_1[2][3] == true))) && ((((p_m_method_8_2).0 == false) && ((p_m_method_8_2).1 == 4) && ((p_m_method_8_2).2 == false) && |p_m_method_8_1| == 3 && (p_m_method_8_1[0] == 17) && (p_m_method_8_1[1] == 3) && (p_m_method_8_1[2] == 9) && p_m_method_8_3.Length == 4 && (20.34 < p_m_method_8_3[0] < 20.54) && (-2.14 < p_m_method_8_3[1] < -1.94) && (-1.91 < p_m_method_8_3[2] < -1.71) && (10.28 < p_m_method_8_3[3] < 10.48)) ==> (ret_1.Length == 3 && ret_1[0].Length == 3 && (ret_1[0][0] == true) && (ret_1[0][1] == true) && (ret_1[0][2] == true) && ret_1[1].Length == 5 && (ret_1[1][0] == false) && (ret_1[1][1] == false) && (ret_1[1][2] == false) && (ret_1[1][3] == true) && (ret_1[1][4] == false) && ret_1[2].Length == 4 && (ret_1[2][0] == true) && (ret_1[2][1] == true) && (ret_1[2][2] == true) && (ret_1[2][3] == true)));
{
	if true {
		var v_bool_seq_7: (bool, seq<int>) := (true, [16, -18]);
		var v_bool_bool_1: (bool, bool) := (false, false);
		var v_bool_bool_2: (bool, bool) := (false, false);
		var v_bool_bool_3: (bool, bool) := (true, false);
		var v_bool_bool_4: (bool, bool) := (false, true);
		var v_bool_bool_5: (bool, bool) := (false, false);
		var v_array_28: array<(bool, bool)> := new (bool, bool)[5] [v_bool_bool_1, v_bool_bool_2, v_bool_bool_3, v_bool_bool_4, v_bool_bool_5];
		var v_array_29: array<bool> := new bool[5] [false, false, true, false, true];
		var v_array_30: array<bool> := new bool[3] [true, false, true];
		var v_array_31: array<bool> := new bool[3] [true, false, true];
		var v_array_32: array<bool> := new bool[3] [true, false, false];
		var v_array_33: array<array<bool>> := new array<bool>[4] [v_array_29, v_array_30, v_array_31, v_array_32];
		var v_DT_1_1_15: DT_1<bool, bool> := DT_1_1;
		var v_bool_seq_8: (bool, seq<int>), v_array_34: array<(bool, bool)>, v_array_35: array<array<bool>>, v_seq_17: seq<bool>, v_DT_1_1_16: DT_1<bool, bool> := v_bool_seq_7, v_array_28, v_array_33, [true], v_DT_1_1_15;
		var v_array_36: array<bool> := new bool[3] [true, true, true];
		var v_array_37: array<bool> := new bool[5];
		v_array_37[0] := false;
		v_array_37[1] := false;
		v_array_37[2] := false;
		v_array_37[3] := true;
		v_array_37[4] := false;
		var v_array_38: array<bool> := new bool[4] [true, true, true, true];
		var v_array_39: array<array<bool>> := new array<bool>[3] [v_array_36, v_array_37, v_array_38];
		print "v_array_33", " ", (v_array_33 == v_array_33), " ", "v_array_32", " ", (v_array_32 == v_array_32), " ", "v_array_31", " ", (v_array_31 == v_array_31), " ", "v_array_38[2]", " ", v_array_38[2], " ", "v_array_30", " ", (v_array_30 == v_array_30), " ", "v_array_37[1]", " ", v_array_37[1], " ", "v_array_29[3]", " ", v_array_29[3], " ", "v_bool_bool_5", " ", v_bool_bool_5, " ", "v_array_28[2]", " ", v_array_28[2], " ", "v_bool_bool_1", " ", v_bool_bool_1, " ", "v_array_32[0]", " ", v_array_32[0], " ", "v_bool_bool_2", " ", v_bool_bool_2, " ", "v_bool_bool_3", " ", v_bool_bool_3, " ", "v_array_33[1]", " ", (v_array_33[1] == v_array_30), " ", "v_bool_bool_4", " ", v_bool_bool_4, " ", "v_array_30[2]", " ", v_array_30[2], " ", "v_array_36[0]", " ", v_array_36[0], " ", "v_array_39", " ", (v_array_39 == v_array_39), " ", "v_array_38", " ", (v_array_38 == v_array_38), " ", "v_array_37", " ", (v_array_37 == v_array_37), " ", "v_array_36", " ", (v_array_36 == v_array_36), " ", "v_array_35", " ", (v_array_35 == v_array_33), " ", "v_array_34", " ", (v_array_34 == v_array_28), " ", "v_array_38[3]", " ", v_array_38[3], " ", "v_array_39[0]", " ", (v_array_39[0] == v_array_36), " ", "v_array_37[2]", " ", v_array_37[2], " ", "v_array_29[4]", " ", v_array_29[4], " ", "v_array_29[0]", " ", v_array_29[0], " ", "v_bool_bool_1.1", " ", v_bool_bool_1.1, " ", "v_array_28[3]", " ", v_array_28[3], " ", "v_bool_bool_1.0", " ", v_bool_bool_1.0, " ", "v_bool_bool_3.1", " ", v_bool_bool_3.1, " ", "v_bool_bool_3.0", " ", v_bool_bool_3.0, " ", "v_bool_bool_5.1", " ", v_bool_bool_5.1, " ", "v_array_31[0]", " ", v_array_31[0], " ", "v_bool_bool_5.0", " ", v_bool_bool_5.0, " ", "v_array_32[1]", " ", v_array_32[1], " ", "v_array_29", " ", (v_array_29 == v_array_29), " ", "v_array_33[2]", " ", (v_array_33[2] == v_array_31), " ", "v_array_28", " ", (v_array_28 == v_array_28), " ", "v_array_36[1]", " ", v_array_36[1], " ", "v_bool_seq_8", " ", v_bool_seq_8, " ", "v_array_37[3]", " ", v_array_37[3], " ", "v_array_39[1]", " ", (v_array_39[1] == v_array_37), " ", "v_array_38[0]", " ", v_array_38[0], " ", "v_bool_seq_7", " ", v_bool_seq_7, " ", "v_array_28[4]", " ", v_array_28[4], " ", "v_array_28[0]", " ", v_array_28[0], " ", "v_array_30[0]", " ", v_array_30[0], " ", "v_array_29[1]", " ", v_array_29[1], " ", "v_seq_17", " ", v_seq_17, " ", "v_array_32[2]", " ", v_array_32[2], " ", "v_array_31[1]", " ", v_array_31[1], " ", "v_bool_seq_7.1", " ", v_bool_seq_7.1, " ", "v_array_33[3]", " ", (v_array_33[3] == v_array_32), " ", "v_bool_seq_7.0", " ", v_bool_seq_7.0, " ", "v_array_36[2]", " ", v_array_36[2], " ", "v_DT_1_1_16", " ", v_DT_1_1_16, " ", "v_DT_1_1_15", " ", v_DT_1_1_15, " ", "v_array_39[2]", " ", (v_array_39[2] == v_array_38), " ", "v_array_37[4]", " ", v_array_37[4], " ", "v_array_38[1]", " ", v_array_38[1], " ", "v_array_37[0]", " ", v_array_37[0], " ", "v_array_28[1]", " ", v_array_28[1], " ", "v_bool_bool_2.0", " ", v_bool_bool_2.0, " ", "v_array_29[2]", " ", v_array_29[2], " ", "v_bool_bool_4.0", " ", v_bool_bool_4.0, " ", "v_array_31[2]", " ", v_array_31[2], " ", "v_bool_bool_2.1", " ", v_bool_bool_2.1, " ", "v_array_30[1]", " ", v_array_30[1], " ", "v_bool_bool_4.1", " ", v_bool_bool_4.1, " ", "v_array_33[0]", " ", (v_array_33[0] == v_array_29), " ", "p_m_method_8_3[2]", " ", (p_m_method_8_3[2] == 14.28), " ", "p_m_method_8_1", " ", p_m_method_8_1, " ", "p_m_method_8_3", " ", "p_m_method_8_2", " ", p_m_method_8_2, " ", "p_m_method_8_2.1", " ", p_m_method_8_2.1, " ", "p_m_method_8_2.0", " ", p_m_method_8_2.0, " ", "p_m_method_8_3[0]", " ", (p_m_method_8_3[0] == -0.09), " ", "p_m_method_8_2.2", " ", p_m_method_8_2.2, " ", "p_m_method_8_3[1]", " ", (p_m_method_8_3[1] == -1.84), "\n";
		return v_array_39;
	} else {
		
	}
	var v_DT_3_2_1: DT_3 := DT_3_2;
	var v_array_40: array<map<bool, int>> := new map<bool, int>[4] [map[false := 20], map[false := -11], map[true := 24], map[true := 6, false := 25, true := 9, true := 25, false := 26]];
	var v_DT_4_2_1: DT_4 := DT_4_2;
	var v_DT_3_2_2: DT_3, v_real_2: real, v_array_41: array<map<bool, int>>, v_int_35: int, v_DT_4_2_2: DT_4 := v_DT_3_2_1, 11.62, v_array_40, 24, v_DT_4_2_1;
	var v_multiset_2: multiset<multiset<int>>, v_multiset_3: multiset<bool> := multiset{multiset{24}, multiset({29, 9, 12})}, multiset({true, true, true});
	var v_real_int_1: (real, int) := (29.68, 11);
	var v_multiset_multiset_real_int_1: (multiset<int>, multiset<int>, (real, int)) := (multiset{1, 15, -25}, multiset{18, 4}, v_real_int_1);
	var v_DT_3_3_1: DT_3 := DT_3_3(multiset{25, 1, 20, 8});
	var v_multiset_multiset_real_int_2: (multiset<int>, multiset<int>, (real, int)), v_DT_3_3_2: DT_3, v_multiset_4: multiset<multiset<real>> := v_multiset_multiset_real_int_1, v_DT_3_3_1, multiset({multiset{21.09, 12.75, -15.65}, multiset{21.74, 27.42, -26.95}});
	if true {
		if false {
			var v_array_42: array<bool> := new bool[3] [true, false, false];
			var v_array_43: array<bool> := new bool[3] [true, false, true];
			var v_array_44: array<bool> := new bool[4] [true, true, false, true];
			var v_array_45: array<array<bool>> := new array<bool>[3] [v_array_42, v_array_43, v_array_44];
			return v_array_45;
		} else {
			match false {
				case _ => {
					var v_array_55: array<bool> := new bool[4] [true, true, true, true];
					var v_array_56: array<bool> := new bool[3] [true, true, false];
					var v_array_57: array<bool> := new bool[5] [false, true, false, true, false];
					var v_array_58: array<array<bool>> := new array<bool>[3] [v_array_55, v_array_56, v_array_57];
					return v_array_58;
				}
				
			}
			
		}
	}
	assert true;
	expect true;
	var v_array_59: array<bool> := new bool[4] [true, false, false, true];
	var v_array_60: array<bool> := new bool[3];
	v_array_60[0] := false;
	v_array_60[1] := true;
	v_array_60[2] := true;
	var v_array_61: array<bool> := new bool[3] [true, false, true];
	var v_array_62: array<bool> := new bool[3] [true, true, false];
	var v_array_63: array<bool> := new bool[3] [true, false, true];
	var v_array_64: array<array<bool>> := new array<bool>[5] [v_array_59, v_array_60, v_array_61, v_array_62, v_array_63];
	return v_array_64;
}

method m_method_7(p_m_method_7_1: bool, p_m_method_7_2: seq<real>, p_m_method_7_3: char) returns (ret_1: int)
	requires ((p_m_method_7_3 == 'F') && |p_m_method_7_2| == 1 && (-2.91 < p_m_method_7_2[0] < -2.71) && (p_m_method_7_1 == true));
	ensures (((p_m_method_7_3 == 'F') && |p_m_method_7_2| == 1 && (-2.91 < p_m_method_7_2[0] < -2.71) && (p_m_method_7_1 == true)) ==> ((ret_1 == 6)));
{
	var v_int_24: int := 24;
	var v_int_25: int := 4;
	var v_int_26: int := safe_division(v_int_24, v_int_25);
	print "v_int_24", " ", v_int_24, " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "p_m_method_7_2", " ", (p_m_method_7_2 == [-2.81]), " ", "p_m_method_7_1", " ", p_m_method_7_1, " ", "p_m_method_7_3", " ", (p_m_method_7_3 == 'F'), "\n";
	return v_int_26;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: bool, p_m_method_6_2: char, p_m_method_6_3: DT_2<bool>, p_m_method_6_4: char) returns (ret_1: (real, bool))
	requires ((p_m_method_6_4 == 'o') && (p_m_method_6_3.DT_2_2? && ((p_m_method_6_3.DT_2_2_1 == true) && (p_m_method_6_3.DT_2_2_2 == false) && (p_m_method_6_3.DT_2_2_3 == false))) && (p_m_method_6_2 == 'S') && (p_m_method_6_1 == false));
	ensures (((p_m_method_6_4 == 'o') && (p_m_method_6_3.DT_2_2? && ((p_m_method_6_3.DT_2_2_1 == true) && (p_m_method_6_3.DT_2_2_2 == false) && (p_m_method_6_3.DT_2_2_3 == false))) && (p_m_method_6_2 == 'S') && (p_m_method_6_1 == false)) ==> ((1.85 < (ret_1).0 < 2.05) && ((ret_1).1 == true)));
{
	var v_DT_1_1_7: DT_1<bool, bool> := DT_1_1;
	var v_int_23: int, v_DT_1_1_8: DT_1<bool, bool> := 1, v_DT_1_1_7;
	var v_real_bool_1: (real, bool) := (1.95, true);
	var v_real_bool_4: (real, bool) := (1.95, true);
	print "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_real_bool_1.1", " ", v_real_bool_1.1, " ", "v_real_bool_1.0", " ", (v_real_bool_1.0 == 1.95), " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "p_m_method_6_3.DT_2_2_1", " ", p_m_method_6_3.DT_2_2_1, " ", "p_m_method_6_3.DT_2_2_3", " ", p_m_method_6_3.DT_2_2_3, " ", "p_m_method_6_3.DT_2_2_2", " ", p_m_method_6_3.DT_2_2_2, " ", "v_int_23", " ", v_int_23, " ", "p_m_method_6_3", " ", p_m_method_6_3, " ", "p_m_method_6_2", " ", (p_m_method_6_2 == 'S'), " ", "p_m_method_6_4", " ", (p_m_method_6_4 == 'o'), " ", "p_m_method_6_1", " ", p_m_method_6_1, " ", "v_real_bool_1", " ", (v_real_bool_1 == v_real_bool_4), "\n";
	return v_real_bool_1;
}

method m_method_5(p_m_method_5_1: (real, bool), p_m_method_5_2: DT_1<bool, bool>, p_m_method_5_3: bool, p_m_method_5_4: char) returns (ret_1: DT_1<bool, bool>)
	requires ((p_m_method_5_4 == 'R') && (1.85 < (p_m_method_5_1).0 < 2.05) && ((p_m_method_5_1).1 == true) && (p_m_method_5_3 == true) && (p_m_method_5_2.DT_1_1? && ((p_m_method_5_2 == DT_1_1))));
	ensures (((p_m_method_5_4 == 'R') && (1.85 < (p_m_method_5_1).0 < 2.05) && ((p_m_method_5_1).1 == true) && (p_m_method_5_3 == true) && (p_m_method_5_2.DT_1_1? && ((p_m_method_5_2 == DT_1_1)))) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_seq_13: seq<multiset<bool>> := [multiset({false, false, false, true}), multiset{false, true, true}, multiset{}, multiset{}];
	var v_int_20: int := 22;
	var v_seq_148: seq<multiset<bool>> := v_seq_13;
	var v_int_187: int := v_int_20;
	var v_int_188: int := safe_index_seq(v_seq_148, v_int_187);
	v_int_20 := v_int_188;
	var v_real_1: real, v_set_2: set<bool>, v_multiset_1: multiset<bool>, v_bool_4: bool := p_m_method_5_1.0, ({false, false, true} + {false, true, true, true}), (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_20]) else (multiset{false, true, false})), p_m_method_5_3;
	var v_DT_2_1_1: DT_2<(bool, real)> := DT_2_1;
	var v_map_5: map<int, DT_2<(bool, real)>> := map[20 := v_DT_2_1_1];
	var v_int_21: int := 24;
	var v_DT_2_1_2: DT_2<(bool, real)> := DT_2_1;
	var v_seq_14: seq<int> := [27];
	var v_char_5: char := 'Q';
	var v_int_22: int := -9;
	var v_char_6: char := m_method_2(v_seq_14, v_char_5, v_int_22);
	var v_real_bool_int_1: (real, bool, int) := (25.80, true, -14);
	var v_real_bool_int_2: (real, bool, int) := (13.88, false, 27);
	var v_real_bool_int_3: (real, bool, int) := (-27.97, true, 17);
	var v_DT_2_1_3: DT_2<(bool, real)>, v_char_7: char, v_set_3: set<(real, bool, int)> := (if ((v_int_21 in v_map_5)) then (v_map_5[v_int_21]) else (v_DT_2_1_2)), v_char_6, (if (false) then ({v_real_bool_int_1, v_real_bool_int_2, v_real_bool_int_3}) else ({}));
	var v_real_bool_5: (real, bool) := (1.95, true);
	var v_DT_2_1_10: DT_2<(bool, real)> := DT_2_1;
	var v_real_bool_int_4: (real, bool, int) := (13.88, false, 27);
	var v_real_bool_int_5: (real, bool, int) := (25.80, true, -14);
	var v_real_bool_int_6: (real, bool, int) := (-27.97, true, 17);
	print "v_bool_4", " ", v_bool_4, " ", "p_m_method_5_1.0", " ", (p_m_method_5_1.0 == 1.95), " ", "p_m_method_5_1.1", " ", p_m_method_5_1.1, " ", "v_seq_14", " ", v_seq_14, " ", "v_int_22", " ", v_int_22, " ", "v_real_bool_int_1.0", " ", (v_real_bool_int_1.0 == 25.80), " ", "v_int_21", " ", v_int_21, " ", "v_real_bool_int_1.1", " ", v_real_bool_int_1.1, " ", "v_real_bool_int_2.0", " ", (v_real_bool_int_2.0 == 13.88), " ", "v_seq_13", " ", (v_seq_13 == [multiset{false, true}, multiset{false, true, true}, multiset{}, multiset{}]), " ", "p_m_method_5_4", " ", (p_m_method_5_4 == 'R'), " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "v_int_20", " ", v_int_20, " ", "v_real_bool_int_1.2", " ", v_real_bool_int_1.2, " ", "v_real_bool_int_2.1", " ", v_real_bool_int_2.1, " ", "v_real_bool_int_3.0", " ", (v_real_bool_int_3.0 == -27.97), " ", "v_real_bool_int_2.2", " ", v_real_bool_int_2.2, " ", "v_real_bool_int_3.1", " ", v_real_bool_int_3.1, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "v_real_bool_int_3.2", " ", v_real_bool_int_3.2, " ", "p_m_method_5_1", " ", (p_m_method_5_1 == v_real_bool_5), " ", "v_map_5", " ", (v_map_5 == map[20 := v_DT_2_1_10]), " ", "v_char_5", " ", (v_char_5 == 'Q'), " ", "v_char_7", " ", (v_char_7 == 'Q'), " ", "v_char_6", " ", (v_char_6 == 'Q'), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{false, true}), " ", "v_DT_2_1_3", " ", v_DT_2_1_3, " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "v_set_3", " ", (v_set_3 == {}), " ", "v_set_2", " ", (v_set_2 == {false, true}), " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_real_bool_int_2", " ", (v_real_bool_int_2 == v_real_bool_int_4), " ", "v_real_1", " ", (v_real_1 == 1.95), " ", "v_real_bool_int_1", " ", (v_real_bool_int_1 == v_real_bool_int_5), " ", "v_real_bool_int_3", " ", (v_real_bool_int_3 == v_real_bool_int_6), "\n";
	return p_m_method_5_2;
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: int, p_m_method_4_3: bool) returns (ret_1: (int, bool))
	requires ((p_m_method_4_2 == 6) && (p_m_method_4_1 == 'V') && (p_m_method_4_3 == false));
	ensures (((p_m_method_4_2 == 6) && (p_m_method_4_1 == 'V') && (p_m_method_4_3 == false)) ==> (((ret_1).0 == 5) && ((ret_1).1 == true)));
{
	var v_int_bool_6: (int, bool) := (5, true);
	print "v_int_bool_6", " ", v_int_bool_6, " ", "v_int_bool_6.1", " ", v_int_bool_6.1, " ", "v_int_bool_6.0", " ", v_int_bool_6.0, " ", "p_m_method_4_1", " ", (p_m_method_4_1 == 'V'), " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return v_int_bool_6;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: seq<real>, p_m_method_3_3: DT_2<bool>, p_m_method_3_4: (int, real, bool)) returns (ret_1: (int, bool))
	requires ((p_m_method_3_1 == -26) && (p_m_method_3_3.DT_2_2? && ((p_m_method_3_3.DT_2_2_1 == true) && (p_m_method_3_3.DT_2_2_2 == true) && (p_m_method_3_3.DT_2_2_3 == false))) && |p_m_method_3_2| == 6 && (20.66 < p_m_method_3_2[0] < 20.86) && (29.21 < p_m_method_3_2[1] < 29.41) && (-17.59 < p_m_method_3_2[2] < -17.39) && (-12.52 < p_m_method_3_2[3] < -12.32) && (-28.40 < p_m_method_3_2[4] < -28.20) && (8.10 < p_m_method_3_2[5] < 8.30) && ((p_m_method_3_4).0 == 12) && (-29.15 < (p_m_method_3_4).1 < -28.95) && ((p_m_method_3_4).2 == true));
	ensures (((p_m_method_3_1 == -26) && (p_m_method_3_3.DT_2_2? && ((p_m_method_3_3.DT_2_2_1 == true) && (p_m_method_3_3.DT_2_2_2 == true) && (p_m_method_3_3.DT_2_2_3 == false))) && |p_m_method_3_2| == 6 && (20.66 < p_m_method_3_2[0] < 20.86) && (29.21 < p_m_method_3_2[1] < 29.41) && (-17.59 < p_m_method_3_2[2] < -17.39) && (-12.52 < p_m_method_3_2[3] < -12.32) && (-28.40 < p_m_method_3_2[4] < -28.20) && (8.10 < p_m_method_3_2[5] < 8.30) && ((p_m_method_3_4).0 == 12) && (-29.15 < (p_m_method_3_4).1 < -28.95) && ((p_m_method_3_4).2 == true)) ==> (((ret_1).0 == 23) && ((ret_1).1 == false)));
{
	var v_int_bool_1: (int, bool) := (23, false);
	var v_int_bool_2: (int, bool) := (4, false);
	var v_int_bool_3: (int, bool) := (5, true);
	var v_int_bool_4: (int, bool) := (20, false);
	var v_seq_7: seq<(int, bool)> := [v_int_bool_1, v_int_bool_2, v_int_bool_3, v_int_bool_4];
	var v_int_14: int := 24;
	var v_seq_154: seq<(int, bool)> := v_seq_7;
	var v_int_203: int := v_int_14;
	var v_int_204: int := safe_index_seq(v_seq_154, v_int_203);
	v_int_14 := v_int_204;
	var v_int_bool_5: (int, bool) := (18, false);
	var v_char_3: char := 'V';
	var v_int_15: int := 6;
	var v_bool_1: bool := false;
	var v_int_bool_7: (int, bool) := m_method_4(v_char_3, v_int_15, v_bool_1);
	var v_int_real_bool_7: (int, real, bool) := (12, -29.05, true);
	print "v_bool_1", " ", v_bool_1, " ", "v_int_bool_7", " ", v_int_bool_7, " ", "v_int_bool_5", " ", v_int_bool_5, " ", "v_int_bool_4", " ", v_int_bool_4, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == [20.76, 29.31, -17.49, -12.42, -28.30, 8.20]), " ", "p_m_method_3_3.DT_2_2_1", " ", p_m_method_3_3.DT_2_2_1, " ", "v_int_bool_3", " ", v_int_bool_3, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_3.DT_2_2_2", " ", p_m_method_3_3.DT_2_2_2, " ", "v_int_bool_2", " ", v_int_bool_2, " ", "p_m_method_3_3.DT_2_2_3", " ", p_m_method_3_3.DT_2_2_3, " ", "p_m_method_3_4", " ", (p_m_method_3_4 == v_int_real_bool_7), " ", "v_int_bool_1", " ", v_int_bool_1, " ", "p_m_method_3_3", " ", p_m_method_3_3, " ", "v_int_bool_1.0", " ", v_int_bool_1.0, " ", "v_char_3", " ", (v_char_3 == 'V'), " ", "p_m_method_3_4.1", " ", (p_m_method_3_4.1 == -29.05), " ", "p_m_method_3_4.2", " ", p_m_method_3_4.2, " ", "p_m_method_3_4.0", " ", p_m_method_3_4.0, " ", "v_int_bool_5.1", " ", v_int_bool_5.1, " ", "v_int_bool_4.1", " ", v_int_bool_4.1, " ", "v_int_bool_5.0", " ", v_int_bool_5.0, " ", "v_int_bool_3.1", " ", v_int_bool_3.1, " ", "v_int_bool_4.0", " ", v_int_bool_4.0, " ", "v_int_bool_2.1", " ", v_int_bool_2.1, " ", "v_int_bool_3.0", " ", v_int_bool_3.0, " ", "v_int_bool_1.1", " ", v_int_bool_1.1, " ", "v_int_bool_2.0", " ", v_int_bool_2.0, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, "\n";
	return (if (('m' >= 'd')) then ((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_14]) else (v_int_bool_5))) else (v_int_bool_7));
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

method m_method_2(p_m_method_2_1: seq<int>, p_m_method_2_2: char, p_m_method_2_3: int) returns (ret_1: char)
	requires ((p_m_method_2_2 == 'Y') && |p_m_method_2_1| == 9 && (p_m_method_2_1[0] == 17) && (p_m_method_2_1[1] == 0) && (p_m_method_2_1[2] == 17) && (p_m_method_2_1[3] == 4) && (p_m_method_2_1[4] == 7) && (p_m_method_2_1[5] == 9) && (p_m_method_2_1[6] == 27) && (p_m_method_2_1[7] == 23) && (p_m_method_2_1[8] == 9) && (p_m_method_2_3 == 6)) || ((p_m_method_2_2 == 'Q') && |p_m_method_2_1| == 1 && (p_m_method_2_1[0] == 27) && (p_m_method_2_3 == -9));
	ensures (((p_m_method_2_2 == 'Q') && |p_m_method_2_1| == 1 && (p_m_method_2_1[0] == 27) && (p_m_method_2_3 == -9)) ==> ((ret_1 == 'Q'))) && (((p_m_method_2_2 == 'Y') && |p_m_method_2_1| == 9 && (p_m_method_2_1[0] == 17) && (p_m_method_2_1[1] == 0) && (p_m_method_2_1[2] == 17) && (p_m_method_2_1[3] == 4) && (p_m_method_2_1[4] == 7) && (p_m_method_2_1[5] == 9) && (p_m_method_2_1[6] == 27) && (p_m_method_2_1[7] == 23) && (p_m_method_2_1[8] == 9) && (p_m_method_2_3 == 6)) ==> ((ret_1 == 'Y')));
{
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'Q'), "\n";
	return p_m_method_2_2;
}

method m_method_1(p_m_method_1_1: DT_1<bool, bool>) returns (ret_1: char, ret_2: (int, bool))
	requires ((p_m_method_1_1.DT_1_1? && ((p_m_method_1_1 == DT_1_1))));
	ensures (((p_m_method_1_1.DT_1_1? && ((p_m_method_1_1 == DT_1_1)))) ==> ((ret_1 == 'Y') && ((ret_2).0 == 23) && ((ret_2).1 == false)));
{
	var v_DT_1_1_1: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_2: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_3: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_4: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_5: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_6: DT_1<bool, bool> := DT_1_1;
	var v_map_1: map<set<DT_1<bool, bool>>, seq<int>> := map[{v_DT_1_1_1, v_DT_1_1_2} := [23, -27, -24, 11], {} := [27, 23, 9]];
	var v_set_1: set<DT_1<bool, bool>> := {};
	var v_seq_6: seq<int> := (([17, 0, 17, 4] + [7, 9]) + (if ((v_set_1 in v_map_1)) then (v_map_1[v_set_1]) else ([26])));
	var v_seq_3: seq<seq<char>> := [['Y']];
	var v_int_7: int := 4;
	var v_seq_149: seq<seq<char>> := v_seq_3;
	var v_int_189: int := v_int_7;
	var v_int_190: int := safe_index_seq(v_seq_149, v_int_189);
	v_int_7 := v_int_190;
	var v_seq_4: seq<char> := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (['W', 'Z']));
	var v_int_8: int := v_int_7;
	var v_seq_5: seq<char> := ['x', 'J'];
	var v_int_9: int := 6;
	var v_char_1: char := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_8]) else ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_9]) else ('f'))));
	var v_int_10: int := 3;
	var v_int_11: int := -26;
	var v_int_12: int := safe_modulus(v_int_10, v_int_11);
	var v_int_13: int := (v_int_12 * |map[false := -9, true := 2]|);
	var v_char_2: char := m_method_2(v_seq_6, v_char_1, v_int_13);
	var v_int_19: int := v_int_11;
	var v_seq_8: seq<real> := [-10.73, 2.08, -26.70, 6.20];
	var v_seq_150: seq<real> := v_seq_8;
	var v_int_193: int := 27;
	var v_int_194: int := 24;
	var v_int_195: int, v_int_196: int := safe_subsequence(v_seq_150, v_int_193, v_int_194);
	var v_int_191: int, v_int_192: int := v_int_195, v_int_196;
	var v_seq_12: seq<real> := ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_191..v_int_192]) else (v_seq_8)) + ([20.76, 29.31, -17.49] + [-12.42, -28.30, 8.20]));
	var v_DT_2_2_1: DT_2<bool> := DT_2_2(true, true, false);
	var v_DT_2_2_2: DT_2<bool> := DT_2_2(false, false, true);
	var v_DT_2_2_3: DT_2<bool> := DT_2_2(false, false, false);
	var v_DT_2_2_4: DT_2<bool> := DT_2_2(false, true, true);
	var v_seq_9: seq<seq<DT_2<bool>>> := [[v_DT_2_2_1, v_DT_2_2_2, v_DT_2_2_3, v_DT_2_2_4]];
	var v_int_16: int := 18;
	var v_seq_151: seq<seq<DT_2<bool>>> := v_seq_9;
	var v_int_197: int := v_int_16;
	var v_int_198: int := safe_index_seq(v_seq_151, v_int_197);
	v_int_16 := v_int_198;
	var v_DT_2_2_5: DT_2<bool> := DT_2_2(false, false, false);
	var v_seq_10: seq<DT_2<bool>> := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_16]) else ([v_DT_2_2_5]));
	var v_int_17: int := (if (true) then (28) else (21));
	var v_seq_152: seq<DT_2<bool>> := v_seq_10;
	var v_int_199: int := v_int_17;
	var v_int_200: int := safe_index_seq(v_seq_152, v_int_199);
	v_int_17 := v_int_200;
	var v_DT_2_2_6: DT_2<bool> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_17]) else (v_DT_2_2_2));
	var v_int_real_bool_1: (int, real, bool) := (3, -29.99, false);
	var v_int_real_bool_2: (int, real, bool) := (12, -3.66, false);
	var v_map_2: map<bool, (int, real, bool)> := (map[false := v_int_real_bool_1] - {false});
	var v_bool_2: bool := !(false);
	var v_int_real_bool_3: (int, real, bool) := (12, -29.05, true);
	var v_int_real_bool_4: (int, real, bool) := (8, -16.21, true);
	var v_seq_11: seq<(int, real, bool)> := [v_int_real_bool_3, v_int_real_bool_4];
	var v_int_18: int := -16;
	var v_seq_153: seq<(int, real, bool)> := v_seq_11;
	var v_int_201: int := v_int_18;
	var v_int_202: int := safe_index_seq(v_seq_153, v_int_201);
	v_int_18 := v_int_202;
	var v_int_real_bool_5: (int, real, bool) := (20, 19.45, false);
	var v_int_real_bool_6: (int, real, bool) := (if ((v_bool_2 in v_map_2)) then (v_map_2[v_bool_2]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_18]) else (v_int_real_bool_5))));
	var v_int_bool_8: (int, bool) := m_method_3(v_int_19, v_seq_12, v_DT_2_2_6, v_int_real_bool_6);
	var v_int_real_bool_8: (int, real, bool) := (12, -29.05, true);
	var v_int_real_bool_9: (int, real, bool) := (8, -16.21, true);
	var v_DT_1_1_21: DT_1<bool, bool> := DT_1_1;
	var v_int_real_bool_10: (int, real, bool) := (12, -29.05, true);
	var v_int_real_bool_11: (int, real, bool) := (20, 19.45, false);
	var v_int_real_bool_12: (int, real, bool) := (12, -3.66, false);
	var v_int_real_bool_13: (int, real, bool) := (3, -29.99, false);
	var v_int_real_bool_14: (int, real, bool) := (8, -16.21, true);
	var v_int_real_bool_15: (int, real, bool) := (12, -29.05, true);
	print "v_DT_2_2_3.DT_2_2_3", " ", v_DT_2_2_3.DT_2_2_3, " ", "v_int_real_bool_2.0", " ", v_int_real_bool_2.0, " ", "v_DT_2_2_3.DT_2_2_2", " ", v_DT_2_2_3.DT_2_2_2, " ", "v_DT_2_2_3.DT_2_2_1", " ", v_DT_2_2_3.DT_2_2_1, " ", "v_int_real_bool_2.2", " ", v_int_real_bool_2.2, " ", "v_int_real_bool_4.0", " ", v_int_real_bool_4.0, " ", "v_int_real_bool_2.1", " ", (v_int_real_bool_2.1 == -3.66), " ", "v_int_real_bool_4.2", " ", v_int_real_bool_4.2, " ", "v_int_real_bool_4.1", " ", (v_int_real_bool_4.1 == -16.21), " ", "v_int_bool_8", " ", v_int_bool_8, " ", "v_DT_2_2_3", " ", v_DT_2_2_3, " ", "v_DT_2_2_2", " ", v_DT_2_2_2, " ", "v_DT_2_2_1", " ", v_DT_2_2_1, " ", "v_DT_2_2_4.DT_2_2_1", " ", v_DT_2_2_4.DT_2_2_1, " ", "v_DT_2_2_4.DT_2_2_2", " ", v_DT_2_2_4.DT_2_2_2, " ", "v_set_1", " ", (v_set_1 == {}), " ", "v_DT_2_2_4.DT_2_2_3", " ", v_DT_2_2_4.DT_2_2_3, " ", "v_DT_2_2_6", " ", v_DT_2_2_6, " ", "v_DT_2_2_5", " ", v_DT_2_2_5, " ", "v_DT_2_2_4", " ", v_DT_2_2_4, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_int_real_bool_1.1", " ", (v_int_real_bool_1.1 == -29.99), " ", "v_int_real_bool_1.0", " ", v_int_real_bool_1.0, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_real_bool_5.2", " ", v_int_real_bool_5.2, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_int_real_bool_3.1", " ", (v_int_real_bool_3.1 == -29.05), " ", "v_int_real_bool_1.2", " ", v_int_real_bool_1.2, " ", "v_int_real_bool_3.0", " ", v_int_real_bool_3.0, " ", "v_int_real_bool_5.1", " ", (v_int_real_bool_5.1 == 19.45), " ", "v_int_real_bool_3.2", " ", v_int_real_bool_3.2, " ", "v_int_real_bool_5.0", " ", v_int_real_bool_5.0, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", (v_seq_11 == [v_int_real_bool_8, v_int_real_bool_9]), " ", "v_seq_12", " ", (v_seq_12 == [20.76, 29.31, -17.49, -12.42, -28.30, 8.20]), " ", "v_int_9", " ", v_int_9, " ", "v_DT_2_2_2.DT_2_2_2", " ", v_DT_2_2_2.DT_2_2_2, " ", "v_DT_2_2_5.DT_2_2_2", " ", v_DT_2_2_5.DT_2_2_2, " ", "v_DT_2_2_2.DT_2_2_1", " ", v_DT_2_2_2.DT_2_2_1, " ", "v_DT_2_2_5.DT_2_2_3", " ", v_DT_2_2_5.DT_2_2_3, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_2_2_2.DT_2_2_3", " ", v_DT_2_2_2.DT_2_2_3, " ", "v_DT_2_2_5.DT_2_2_1", " ", v_DT_2_2_5.DT_2_2_1, " ", "v_char_1", " ", (v_char_1 == 'Y'), " ", "v_char_2", " ", (v_char_2 == 'Y'), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[{} := [27, 23, 9], {v_DT_1_1_21} := [23, -27, -24, 11]]), " ", "v_seq_9", " ", v_seq_9, " ", "v_map_2", " ", (v_map_2 == map[]), " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", (v_seq_8 == [-10.73, 2.08, -26.70, 6.20]), " ", "v_int_12", " ", v_int_12, " ", "v_DT_2_2_1.DT_2_2_1", " ", v_DT_2_2_1.DT_2_2_1, " ", "v_int_11", " ", v_int_11, " ", "v_seq_6", " ", v_seq_6, " ", "v_DT_2_2_1.DT_2_2_2", " ", v_DT_2_2_1.DT_2_2_2, " ", "v_seq_5", " ", (v_seq_5 == ['x', 'J']), " ", "v_int_10", " ", v_int_10, " ", "v_DT_2_2_1.DT_2_2_3", " ", v_DT_2_2_1.DT_2_2_3, " ", "v_seq_4", " ", (v_seq_4 == ['Y']), " ", "v_int_17", " ", v_int_17, " ", "v_int_real_bool_6", " ", (v_int_real_bool_6 == v_int_real_bool_10), " ", "v_seq_3", " ", (v_seq_3 == [['Y']]), " ", "v_int_16", " ", v_int_16, " ", "v_int_real_bool_5", " ", (v_int_real_bool_5 == v_int_real_bool_11), " ", "v_int_real_bool_2", " ", (v_int_real_bool_2 == v_int_real_bool_12), " ", "v_int_real_bool_1", " ", (v_int_real_bool_1 == v_int_real_bool_13), " ", "v_int_real_bool_4", " ", (v_int_real_bool_4 == v_int_real_bool_14), " ", "v_int_real_bool_3", " ", (v_int_real_bool_3 == v_int_real_bool_15), "\n";
	return v_char_2, v_int_bool_8;
}

method Main() returns ()
{
	var v_map_4: map<char, bool> := (map['O' := true] + map['k' := true, 't' := false, 'T' := false]);
	var v_map_3: map<bool, char> := map[true := 'l'];
	var v_bool_3: bool := false;
	var v_char_4: char := (if ((v_bool_3 in v_map_3)) then (v_map_3[v_bool_3]) else ('R'));
	var v_bool_5: bool := false;
	var v_char_8: char := 'S';
	var v_DT_2_2_7: DT_2<bool> := DT_2_2(true, false, false);
	var v_DT_2_2_8: DT_2<bool> := v_DT_2_2_7;
	var v_char_9: char := 'o';
	var v_real_bool_2: (real, bool) := m_method_6(v_bool_5, v_char_8, v_DT_2_2_8, v_char_9);
	var v_real_bool_3: (real, bool) := v_real_bool_2;
	var v_DT_1_1_9: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_10: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_11: DT_1<bool, bool> := DT_1_1;
	var v_DT_1_1_12: DT_1<bool, bool> := (match 15 {
		case 0 => v_DT_1_1_9
		case 9 => v_DT_1_1_10
		case _ => v_DT_1_1_11
	});
	var v_bool_seq_1: (bool, seq<real>) := (true, [8.43, 23.09, -26.95, 17.33]);
	var v_bool_seq_2: (bool, seq<real>) := (true, [18.28, 2.71, 29.89, 24.67]);
	var v_bool_seq_3: (bool, seq<real>) := (true, [-3.49, -20.22, 25.78, -2.51]);
	var v_bool_seq_4: (bool, seq<real>) := (true, [0.39, -27.20, -17.12, -25.91]);
	var v_map_6: map<(bool, seq<real>), bool> := map[v_bool_seq_1 := true, v_bool_seq_2 := true, v_bool_seq_3 := false, v_bool_seq_4 := false];
	var v_bool_seq_5: (bool, seq<real>) := (true, [-2.81]);
	var v_bool_seq_6: (bool, seq<real>) := v_bool_seq_5;
	var v_bool_6: bool := (if ((v_bool_seq_6 in v_map_6)) then (v_map_6[v_bool_seq_6]) else (true));
	var v_char_10: char := v_char_4;
	var v_DT_1_1_13: DT_1<bool, bool> := m_method_5(v_real_bool_3, v_DT_1_1_12, v_bool_6, v_char_10);
	var v_DT_1_1_14: DT_1<bool, bool> := (if ((if ((v_char_4 in v_map_4)) then (v_map_4[v_char_4]) else ((if (false) then (true) else (false))))) then (v_DT_1_1_13) else (v_DT_1_1_12));
	var v_char_11: char, v_int_bool_9: (int, bool) := m_method_1(v_DT_1_1_14);
	v_char_8, v_int_bool_9 := v_char_11, v_int_bool_9;
	var v_bool_7: bool := (match 14 {
		case 14 => true
		case 3 => true
		case _ => true
	});
	var v_seq_16: seq<real> := v_bool_seq_5.1;
	var v_seq_15: seq<char> := ['F', 'V', 'B', 'L'];
	var v_int_27: int := -15;
	var v_seq_155: seq<char> := v_seq_15;
	var v_int_205: int := v_int_27;
	var v_int_206: int := safe_index_seq(v_seq_155, v_int_205);
	v_int_27 := v_int_206;
	var v_char_12: char := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_27]) else ('J'));
	var v_int_28: int := m_method_7(v_bool_7, v_seq_16, v_char_12);
	var v_int_32: int := v_int_28;
	var v_int_29: int := 10;
	var v_int_30: int := 21;
	var v_int_31: int := safe_modulus(v_int_29, v_int_30);
	var v_int_33: int := (v_int_31 % (match -12.70 {
		case -15.04 => 20
		case -16.53 => 13
		case _ => 5
	}));
	var v_int_34: int := safe_division(v_int_32, v_int_33);
	var v_array_1: array<bool> := new bool[4] [false, false, false, false];
	var v_array_2: array<bool> := new bool[3] [false, true, true];
	var v_array_3: array<bool> := new bool[4] [true, false, true, true];
	var v_array_4: array<bool> := new bool[3] [false, true, false];
	var v_array_5: array<array<bool>> := new array<bool>[4] [v_array_1, v_array_2, v_array_3, v_array_4];
	var v_array_6: array<bool> := new bool[3] [true, false, true];
	var v_array_7: array<bool> := new bool[3] [true, false, false];
	var v_array_8: array<bool> := new bool[3];
	v_array_8[0] := true;
	v_array_8[1] := true;
	v_array_8[2] := false;
	var v_array_9: array<array<bool>> := new array<bool>[3] [v_array_6, v_array_7, v_array_8];
	var v_array_10: array<bool> := new bool[5] [true, false, false, false, false];
	var v_array_11: array<bool> := new bool[4];
	v_array_11[0] := false;
	v_array_11[1] := true;
	v_array_11[2] := true;
	v_array_11[3] := false;
	var v_array_12: array<bool> := new bool[5] [true, false, true, false, true];
	var v_array_13: array<array<bool>> := new array<bool>[3] [v_array_10, v_array_11, v_array_12];
	var v_array_14: array<bool> := new bool[4] [true, true, false, true];
	var v_array_15: array<bool> := new bool[5] [true, true, true, false, false];
	var v_array_16: array<bool> := new bool[4] [true, false, true, true];
	var v_array_17: array<bool> := new bool[4] [false, true, true, false];
	var v_array_18: array<bool> := new bool[3] [true, false, false];
	var v_array_19: array<array<bool>> := new array<bool>[5] [v_array_14, v_array_15, v_array_16, v_array_17, v_array_18];
	var v_array_20: array<bool> := new bool[4] [true, true, true, true];
	var v_array_21: array<bool> := new bool[5] [false, false, true, false, false];
	var v_array_22: array<bool> := new bool[4] [false, true, false, true];
	var v_array_23: array<array<bool>> := new array<bool>[3] [v_array_20, v_array_21, v_array_22];
	var v_array_24: array<bool> := new bool[5] [true, false, true, false, true];
	var v_array_25: array<bool> := new bool[3] [false, true, true];
	var v_array_26: array<bool> := new bool[4] [true, false, true, false];
	var v_array_27: array<array<bool>> := new array<bool>[3] [v_array_24, v_array_25, v_array_26];
	var v_seq_18: seq<int> := [21];
	var v_bool_int_bool_1: (bool, int, bool) := (false, 4, false);
	var v_bool_int_bool_2: (bool, int, bool) := v_bool_int_bool_1;
	var v_array_65: array<real> := new real[4] [-0.09, -1.84, 14.28, -8.85];
	var v_array_66: array<real> := v_array_65;
	var v_array_67: array<array<bool>> := m_method_8(v_seq_18, v_bool_int_bool_2, v_array_66);
	var v_int_real_real_1: (int, real, real) := (22, -25.65, -14.92);
	var v_int_real_real_2: (int, real, real) := (26, 14.04, 19.98);
	var v_int_real_real_3: (int, real, real) := (26, 21.33, -14.01);
	var v_int_real_real_4: (int, real, real) := (18, -21.27, 9.54);
	var v_int_real_real_5: (int, real, real) := (11, 6.42, -14.93);
	var v_int_real_real_6: (int, real, real) := (22, 20.47, 25.29);
	var v_int_real_real_7: (int, real, real) := (-18, -3.08, -7.24);
	var v_int_real_real_8: (int, real, real) := (5, -1.91, -20.69);
	var v_int_real_real_9: (int, real, real) := (1, 15.40, 4.16);
	var v_int_real_real_10: (int, real, real) := (4, 7.57, 5.70);
	var v_map_7: map<multiset<(int, real, real)>, char> := map[multiset{v_int_real_real_1, v_int_real_real_2, v_int_real_real_3, v_int_real_real_4} := 'p', multiset{v_int_real_real_5} := 'I', multiset{v_int_real_real_6} := 'X', multiset{v_int_real_real_7, v_int_real_real_8, v_int_real_real_9, v_int_real_real_10} := 'x', multiset{} := 'e'];
	var v_int_real_real_11: (int, real, real) := (4, -13.00, -8.76);
	var v_int_real_real_12: (int, real, real) := (27, -18.48, 1.06);
	var v_int_real_real_13: (int, real, real) := (28, -0.22, 19.79);
	var v_multiset_5: multiset<(int, real, real)> := multiset{v_int_real_real_11, v_int_real_real_12, v_int_real_real_13};
	var v_map_9: map<array<array<bool>>, char> := (map[v_array_5 := 'V', v_array_9 := 'P'] + map[v_array_13 := 'V', v_array_19 := 'F', v_array_23 := 'r', v_array_27 := 's'])[v_array_67 := (if ((v_multiset_5 in v_map_7)) then (v_map_7[v_multiset_5]) else ('x'))];
	var v_seq_19: seq<int> := ([] + [17, 3, 9]);
	var v_bool_int_bool_3: (bool, int, bool) := v_bool_int_bool_2;
	var v_array_68: array<real> := new real[5] [13.40, -21.07, 16.14, -27.13, 18.04];
	var v_array_69: array<real> := new real[3] [-10.77, -24.57, -12.59];
	var v_array_70: array<real> := new real[4] [14.38, -9.31, -23.15, 4.91];
	var v_array_71: array<real> := new real[4] [20.44, -2.04, -1.81, 10.38];
	var v_map_8: map<multiset<seq<int>>, array<real>> := map[multiset{[7, 17, 24], [17, 25, 1]} := v_array_68, multiset{[2], [3, 9, 12, -25], []} := v_array_69, multiset{[10, 0, -3]} := v_array_70, multiset({}) := v_array_71];
	var v_multiset_6: multiset<seq<int>> := multiset{};
	var v_array_72: array<real> := new real[5] [-29.09, -8.10, 3.73, 19.42, 0.72];
	var v_array_73: array<real> := (if ((v_multiset_6 in v_map_8)) then (v_map_8[v_multiset_6]) else (v_array_72));
	var v_array_74: array<array<bool>> := m_method_8(v_seq_19, v_bool_int_bool_3, v_array_73);
	var v_array_75: array<array<bool>> := v_array_74;
	var v_seq_20: seq<DT_1<bool, bool>> := [];
	var v_seq_21: seq<DT_1<bool, bool>> := v_seq_20;
	var v_int_36: int := 9;
	var v_int_37: int := safe_index_seq(v_seq_21, v_int_36);
	var v_int_38: int := v_int_37;
	var v_DT_1_1_17: DT_1<bool, bool> := DT_1_1;
	var v_seq_22: seq<DT_1<bool, bool>> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_38 := v_DT_1_1_17]) else (v_seq_20));
	var v_seq_23: seq<DT_1<bool, bool>> := v_seq_22;
	var v_int_39: int := (match false {
		case false => 6
		case true => 15
		case _ => 14
	});
	var v_int_40: int := safe_index_seq(v_seq_23, v_int_39);
	var v_int_41: int := v_int_40;
	var v_seq_24: seq<DT_1<bool, bool>> := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_41 := v_DT_1_1_13]) else (v_seq_22));
	var v_int_42: int := (match true {
		case false => |{false, true, true, true}|
		case true => (if (true) then (24) else (14))
		case _ => v_int_41
	});
	var v_seq_25: seq<bool> := ([false, true, true] + [false, false]);
	var v_map_10: map<bool, int> := map[false := 1, true := -17];
	var v_bool_8: bool := true;
	var v_int_43: int := (if ((v_bool_8 in v_map_10)) then (v_map_10[v_bool_8]) else (17));
	var v_map_11: map<bool, bool> := map[true := true, false := false];
	var v_bool_9: bool := true;
	v_int_28, v_char_8, v_array_70[2], v_DT_1_1_17, v_array_26[1] := v_int_34, (if ((v_array_75 in v_map_9)) then (v_map_9[v_array_75]) else (v_char_12)), v_int_real_real_9.2, (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_42]) else (v_DT_1_1_12)), (match true {
		case false => (!(true) <==> (if (false) then (true) else (true)))
		case true => (if (v_array_1[3]) then (v_bool_int_bool_1.2) else ((false in [])))
		case _ => (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_43]) else ((if ((v_bool_9 in v_map_11)) then (v_map_11[v_bool_9]) else (true))))
	});
	var v_bool_seq_9: (bool, seq<real>) := (true, [-3.49, -20.22, 25.78, -2.51]);
	assert ((v_bool_seq_3 == v_bool_seq_9));
	expect ((v_bool_seq_3 == v_bool_seq_9));
	var v_map_12: map<bool, map<bool, seq<int>>> := map[true := map[false := [2, 29, 13, 13]], false := map[true := [6], false := [7, 10, 0, 0]]];
	var v_bool_10: bool := false;
	var v_map_13: map<bool, seq<int>> := (if ((v_bool_10 in v_map_12)) then (v_map_12[v_bool_10]) else (map[true := []]));
	var v_bool_11: bool := (true in map[false := true]);
	var v_seq_26: seq<int> := (if ((v_bool_11 in v_map_13)) then (v_map_13[v_bool_11]) else (([7, 14] + [6, 0, 24, 6])));
	var v_array_76: array<bool> := new bool[4] [true, true, true, true];
	var v_int_45: int := ((match false {
		case false => 9
		case _ => 11
	}) + v_array_76.Length);
	var v_seq_156: seq<int> := v_seq_26;
	var v_int_207: int := v_int_45;
	var v_int_208: int := safe_index_seq(v_seq_156, v_int_207);
	v_int_45 := v_int_208;
	var v_seq_27: seq<int> := [];
	var v_int_46: int := 10;
	var v_map_15: map<bool, multiset<bool>> := map[true := multiset{false, false, false}, false := multiset{false, true}][true := multiset{false, true, true, false}];
	var v_map_14: map<bool, bool> := map[false := false];
	var v_bool_12: bool := true;
	var v_bool_13: bool := (if ((v_bool_12 in v_map_14)) then (v_map_14[v_bool_12]) else (false));
	var v_seq_28: seq<multiset<bool>> := [multiset({false, false}), multiset{}, multiset{false, false, true}];
	var v_int_47: int := 19;
	var v_int_185: int, v_int_186: int := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_45]) else ((if ((match false {
		case _ => false
	})) then ((if ((|v_seq_27| > 0)) then (v_seq_27[v_int_46]) else (28))) else (v_int_real_real_9.0)))), |(if ((v_bool_13 in v_map_15)) then (v_map_15[v_bool_13]) else ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_47]) else (multiset({false, true})))))|;
	for v_int_44 := v_int_185 downto v_int_186 
		invariant (v_int_44 - v_int_186 >= 0) && ((((v_int_44 == 6)) ==> ((((v_array_15[3] == false)) && ((v_bool_3 == false)) && ((v_array_24[2] == true)) && ((v_array_21[0] == false)) && ((v_array_8[1] == true)) && ((v_array_21[3] == false)) && ((v_bool_12 == true)) && ((v_array_17[0] == false)) && ((v_array_18[2] == false)) && (v_array_19[4].Length == 3 && (v_array_19[4][0] == true) && (v_array_19[4][1] == false) && (v_array_19[4][2] == false))))))
	{
		var v_seq_29: seq<map<bool, int>> := [map[false := 21, true := 0]];
		var v_int_49: int := -11;
		var v_seq_157: seq<map<bool, int>> := v_seq_29;
		var v_int_209: int := v_int_49;
		var v_int_210: int := safe_index_seq(v_seq_157, v_int_209);
		v_int_49 := v_int_210;
		var v_map_17: map<bool, int> := (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_49]) else (map[false := 12, true := 13, true := 16, false := 24]));
		var v_map_16: map<bool, bool> := map[false := false, true := false];
		var v_bool_14: bool := true;
		var v_bool_15: bool := (if ((v_bool_14 in v_map_16)) then (v_map_16[v_bool_14]) else (true));
		var v_map_18: map<bool, map<bool, int>> := map[false := map[false := 10], true := map[false := 20, true := 24]];
		var v_bool_16: bool := false;
		var v_map_19: map<bool, int> := (if ((v_bool_16 in v_map_18)) then (v_map_18[v_bool_16]) else (map[false := 7, true := 22, false := 27, true := -12, true := 13]));
		var v_bool_17: bool := (if (false) then (true) else (false));
		var v_int_50: int, v_int_51: int := v_int_real_real_5.0, (match true {
			case false => (if ((v_bool_15 in v_map_17)) then (v_map_17[v_bool_15]) else (v_int_real_real_9.0))
			case true => v_int_36
			case _ => (if ((v_bool_17 in v_map_19)) then (v_map_19[v_bool_17]) else ((if (true) then (14) else (10))))
		});
		for v_int_48 := v_int_50 downto v_int_51 
			invariant (v_int_48 - v_int_51 >= 0)
		{
			var v_int_real_real_14: (int, real, real) := (5, -1.91, -20.69);
			var v_int_real_real_15: (int, real, real) := (-18, -3.08, -7.24);
			var v_int_real_real_16: (int, real, real) := (22, 20.47, 25.29);
			var v_int_real_real_17: (int, real, real) := (11, 6.42, -14.93);
			var v_int_real_real_18: (int, real, real) := (18, -21.27, 9.54);
			var v_int_real_real_19: (int, real, real) := (26, 21.33, -14.01);
			var v_int_real_real_20: (int, real, real) := (26, 14.04, 19.98);
			var v_int_real_real_21: (int, real, real) := (22, -25.65, -14.92);
			var v_int_real_real_22: (int, real, real) := (28, -0.22, 19.79);
			var v_int_real_real_23: (int, real, real) := (27, -18.48, 1.06);
			var v_int_real_real_24: (int, real, real) := (4, -13.00, -8.76);
			var v_int_real_real_25: (int, real, real) := (4, 7.57, 5.70);
			var v_bool_seq_10: (bool, seq<real>) := (true, [-2.81]);
			var v_bool_seq_11: (bool, seq<real>) := (true, [0.39, -27.20, -17.12, -25.91]);
			var v_bool_seq_12: (bool, seq<real>) := (true, [-2.81]);
			var v_bool_seq_13: (bool, seq<real>) := (true, [18.28, 2.71, 29.89, 24.67]);
			var v_bool_seq_14: (bool, seq<real>) := (true, [-3.49, -20.22, 25.78, -2.51]);
			var v_bool_seq_15: (bool, seq<real>) := (true, [8.43, 23.09, -26.95, 17.33]);
			var v_int_real_real_26: (int, real, real) := (1, 15.40, 4.16);
			var v_int_real_real_27: (int, real, real) := (27, -18.48, 1.06);
			var v_int_real_real_28: (int, real, real) := (4, -13.00, -8.76);
			var v_int_real_real_29: (int, real, real) := (28, -0.22, 19.79);
			var v_int_real_real_30: (int, real, real) := (22, 20.47, 25.29);
			var v_int_real_real_31: (int, real, real) := (-18, -3.08, -7.24);
			var v_int_real_real_32: (int, real, real) := (4, 7.57, 5.70);
			var v_int_real_real_33: (int, real, real) := (5, -1.91, -20.69);
			var v_int_real_real_34: (int, real, real) := (1, 15.40, 4.16);
			var v_int_real_real_35: (int, real, real) := (11, 6.42, -14.93);
			var v_int_real_real_36: (int, real, real) := (18, -21.27, 9.54);
			var v_int_real_real_37: (int, real, real) := (26, 14.04, 19.98);
			var v_int_real_real_38: (int, real, real) := (26, 21.33, -14.01);
			var v_int_real_real_39: (int, real, real) := (22, -25.65, -14.92);
			var v_bool_seq_16: (bool, seq<real>) := (true, [8.43, 23.09, -26.95, 17.33]);
			var v_bool_seq_17: (bool, seq<real>) := (true, [-3.49, -20.22, 25.78, -2.51]);
			var v_bool_seq_18: (bool, seq<real>) := (true, [18.28, 2.71, 29.89, 24.67]);
			var v_bool_seq_19: (bool, seq<real>) := (true, [0.39, -27.20, -17.12, -25.91]);
			var v_real_bool_6: (real, bool) := (1.95, true);
			var v_real_bool_7: (real, bool) := (1.95, true);
			print "v_int_48", " ", v_int_48, " ", "v_int_44", " ", v_int_44, " ", "v_array_76", " ", (v_array_76 == v_array_76), " ", "v_array_75", " ", "v_array_74", " ", "v_array_73", " ", (v_array_73 == v_array_71), " ", "v_array_20[1]", " ", v_array_20[1], " ", "v_array_72", " ", (v_array_72 == v_array_72), " ", "v_array_71", " ", (v_array_71 == v_array_71), " ", "v_array_14[1]", " ", v_array_14[1], " ", "v_array_70", " ", (v_array_70 == v_array_70), " ", "v_int_real_real_8", " ", (v_int_real_real_8 == v_int_real_real_14), " ", "v_int_real_real_7", " ", (v_int_real_real_7 == v_int_real_real_15), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 14.04), " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_16), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == 19.98), " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_17), " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_18), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_19), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_20), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_21), " ", "v_int_46", " ", v_int_46, " ", "v_int_45", " ", v_int_45, " ", "v_array_26[0]", " ", v_array_26[0], " ", "v_int_47", " ", v_int_47, " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_19[2]", " ", (v_array_19[2] == v_array_16), " ", "v_array_72[2]", " ", (v_array_72[2] == 3.73), " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_array_9[0]", " ", (v_array_9[0] == v_array_6), " ", "v_int_40", " ", v_int_40, " ", "v_array_66", " ", (v_array_66 == v_array_65), " ", "v_array_65", " ", (v_array_65 == v_array_65), " ", "v_array_14[0]", " ", v_array_14[0], " ", "v_array_20[0]", " ", v_array_20[0], " ", "v_array_19[1]", " ", (v_array_19[1] == v_array_15), " ", "v_int_29", " ", v_int_29, " ", "v_array_65[3]", " ", (v_array_65[3] == -8.85), " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_int_39", " ", v_int_39, " ", "v_array_26[1]", " ", v_array_26[1], " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_int_real_real_13", " ", (v_int_real_real_13 == v_int_real_real_22), " ", "v_int_real_real_12", " ", (v_int_real_real_12 == v_int_real_real_23), " ", "v_int_real_real_11", " ", (v_int_real_real_11 == v_int_real_real_24), " ", "v_int_real_real_10", " ", (v_int_real_real_10 == v_int_real_real_25), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, " ", "v_array_8[2]", " ", v_array_8[2], " ", "v_array_69", " ", (v_array_69 == v_array_69), " ", "v_array_72[3]", " ", (v_array_72[3] == 19.42), " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_68", " ", (v_array_68 == v_array_68), " ", "v_array_67", " ", "v_array_14[3]", " ", v_array_14[3], " ", "v_array_65[2]", " ", (v_array_65[2] == 14.28), " ", "v_array_21[0]", " ", v_array_21[0], " ", "v_array_15[0]", " ", v_array_15[0], " ", "v_array_20[3]", " ", v_array_20[3], " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == -14.01), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == 21.33), " ", "v_DT_2_2_7.DT_2_2_1", " ", v_DT_2_2_7.DT_2_2_1, " ", "v_array_24[4]", " ", v_array_24[4], " ", "v_array_25[1]", " ", v_array_25[1], " ", "v_array_19[4]", " ", (v_array_19[4] == v_array_18), " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_array_72[4]", " ", (v_array_72[4] == 0.72), " ", "v_array_8[1]", " ", v_array_8[1], " ", "v_array_65[1]", " ", (v_array_65[1] == -1.84), " ", "v_array_14[2]", " ", v_array_14[2], " ", "v_array_20[2]", " ", v_array_20[2], " ", "v_DT_2_2_7.DT_2_2_3", " ", v_DT_2_2_7.DT_2_2_3, " ", "v_DT_2_2_7.DT_2_2_2", " ", v_DT_2_2_7.DT_2_2_2, " ", "v_array_25[2]", " ", v_array_25[2], " ", "v_bool_int_bool_1.0", " ", v_bool_int_bool_1.0, " ", "v_bool_int_bool_1.1", " ", v_bool_int_bool_1.1, " ", "v_array_19[3]", " ", (v_array_19[3] == v_array_17), " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_bool_int_bool_1.2", " ", v_bool_int_bool_1.2, " ", "v_array_8[0]", " ", v_array_8[0], " ", "v_array_15[2]", " ", v_array_15[2], " ", "v_array_21[2]", " ", v_array_21[2], " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -21.27), " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == 9.54), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_array_76[2]", " ", v_array_76[2], " ", "v_array_27[1]", " ", (v_array_27[1] == v_array_25), " ", "v_int_bool_9", " ", v_int_bool_9, " ", "v_array_71[1]", " ", (v_array_71[1] == -2.04), " ", "v_bool_seq_4.0", " ", v_bool_seq_4.0, " ", "v_array_4[1]", " ", v_array_4[1], " ", "v_bool_seq_4.1", " ", (v_bool_seq_4.1 == [0.39, -27.20, -17.12, -25.91]), " ", "v_array_21[1]", " ", v_array_21[1], " ", "v_array_15[1]", " ", v_array_15[1], " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_int_real_real_10.2", " ", (v_int_real_real_10.2 == 5.70), " ", "v_int_real_real_10.0", " ", v_int_real_real_10.0, " ", "v_int_real_real_10.1", " ", (v_int_real_real_10.1 == 7.57), " ", "v_array_27[2]", " ", (v_array_27[2] == v_array_26), " ", "v_DT_2_2_7", " ", v_DT_2_2_7, " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == -14.93), " ", "v_array_71[2]", " ", (v_array_71[2] == -1.81), " ", "v_DT_2_2_8", " ", v_DT_2_2_8, " ", "v_array_4[2]", " ", v_array_4[2], " ", "v_array_76[3]", " ", v_array_76[3], " ", "v_array_16[1]", " ", v_array_16[1], " ", "v_bool_3", " ", v_bool_3, " ", "v_array_15[4]", " ", v_array_15[4], " ", "v_bool_seq_6", " ", (v_bool_seq_6 == v_bool_seq_10), " ", "v_bool_seq_4", " ", (v_bool_seq_4 == v_bool_seq_11), " ", "v_char_12", " ", (v_char_12 == 'F'), " ", "v_bool_seq_5", " ", (v_bool_seq_5 == v_bool_seq_12), " ", "v_char_11", " ", (v_char_11 == 'Y'), " ", "v_array_10[3]", " ", v_array_10[3], " ", "v_array_22[1]", " ", v_array_22[1], " ", "v_bool_seq_2", " ", (v_bool_seq_2 == v_bool_seq_13), " ", "v_array_11[0]", " ", v_array_11[0], " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_bool_seq_3", " ", (v_bool_seq_3 == v_bool_seq_14), " ", "v_array_21[4]", " ", v_array_21[4], " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == 6.42), " ", "v_bool_seq_1", " ", (v_bool_seq_1 == v_bool_seq_15), " ", "v_bool_5", " ", v_bool_5, " ", "v_seq_18", " ", v_seq_18, " ", "v_seq_19", " ", v_seq_19, " ", "v_bool_7", " ", v_bool_7, " ", "v_bool_6", " ", v_bool_6, " ", "v_seq_15", " ", (v_seq_15 == ['F', 'V', 'B', 'L']), " ", "v_seq_16", " ", (v_seq_16 == [-2.81]), " ", "v_array_26[2]", " ", v_array_26[2], " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_bool_int_bool_2", " ", v_bool_int_bool_2, " ", "v_array_72[0]", " ", (v_array_72[0] == -29.09), " ", "v_bool_int_bool_1", " ", v_bool_int_bool_1, " ", "v_array_71[3]", " ", (v_array_71[3] == 10.38), " ", "v_bool_seq_5.1", " ", (v_bool_seq_5.1 == [-2.81]), " ", "v_bool_int_bool_3", " ", v_bool_int_bool_3, " ", "v_array_9[2]", " ", (v_array_9[2] == v_array_8), " ", "v_bool_seq_5.0", " ", v_bool_seq_5.0, " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_array_15[3]", " ", v_array_15[3], " ", "v_array_22[0]", " ", v_array_22[0], " ", "v_array_16[0]", " ", v_array_16[0], " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_array_21[3]", " ", v_array_21[3], " ", "v_int_real_real_11.1", " ", (v_int_real_real_11.1 == -13.00), " ", "v_int_real_real_11.2", " ", (v_int_real_real_11.2 == -8.76), " ", "v_int_real_real_11.0", " ", v_int_real_real_11.0, " ", "v_array_26[3]", " ", v_array_26[3], " ", "v_array_27[0]", " ", (v_array_27[0] == v_array_24), " ", "v_int_real_real_6.1", " ", (v_int_real_real_6.1 == 20.47), " ", "v_int_real_real_6.2", " ", (v_int_real_real_6.2 == 25.29), " ", "v_int_real_real_9", " ", (v_int_real_real_9 == v_int_real_real_26), " ", "v_char_10", " ", (v_char_10 == 'R'), " ", "v_array_72[1]", " ", (v_array_72[1] == -8.10), " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_9[1]", " ", (v_array_9[1] == v_array_7), " ", "v_array_5[3]", " ", (v_array_5[3] == v_array_4), " ", "v_array_16[3]", " ", v_array_16[3], " ", "v_array_11[2]", " ", v_array_11[2], " ", "v_array_17[0]", " ", v_array_17[0], " ", "v_map_13", " ", (v_map_13 == map[false := [7, 10, 0, 0], true := [6]]), " ", "v_array_22[3]", " ", v_array_22[3], " ", "v_int_real_real_6.0", " ", v_int_real_real_6.0, " ", "v_map_14", " ", (v_map_14 == map[false := false]), " ", "v_map_12", " ", (v_map_12 == map[false := map[false := [7, 10, 0, 0], true := [6]], true := map[false := [2, 29, 13, 13]]]), " ", "v_array_69[0]", " ", (v_array_69[0] == -10.77), " ", "v_array_68[3]", " ", (v_array_68[3] == -27.13), " ", "v_map_15", " ", (v_map_15 == map[false := multiset{false, true}, true := multiset{false, false, true, true}]), " ", "v_array_23[1]", " ", (v_array_23[1] == v_array_21), " ", "v_bool_seq_2.0", " ", v_bool_seq_2.0, " ", "v_array_5[2]", " ", (v_array_5[2] == v_array_3), " ", "v_bool_seq_2.1", " ", (v_bool_seq_2.1 == [18.28, 2.71, 29.89, 24.67]), " ", "v_array_16[2]", " ", v_array_16[2], " ", "v_array_70[0]", " ", (v_array_70[0] == 14.38), " ", "v_array_10[4]", " ", v_array_10[4], " ", "v_multiset_6", " ", (v_multiset_6 == multiset{}), " ", "v_multiset_5", " ", (v_multiset_5 == multiset{v_int_real_real_27, v_int_real_real_28, v_int_real_real_29}), " ", "v_array_22[2]", " ", v_array_22[2], " ", "v_int_real_real_12.2", " ", (v_int_real_real_12.2 == 1.06), " ", "v_array_11[1]", " ", v_array_11[1], " ", "v_int_real_real_12.0", " ", v_int_real_real_12.0, " ", "v_int_real_real_12.1", " ", (v_int_real_real_12.1 == -18.48), " ", "v_array_68[2]", " ", (v_array_68[2] == 16.14), " ", "v_seq_26", " ", v_seq_26, " ", "v_seq_27", " ", v_seq_27, " ", "v_seq_28", " ", (v_seq_28 == [multiset{false}, multiset{}, multiset{false, false, true}]), " ", "v_int_real_real_7.2", " ", (v_int_real_real_7.2 == -7.24), " ", "v_seq_21", " ", v_seq_21, " ", "v_seq_22", " ", v_seq_22, " ", "v_array_23[2]", " ", (v_array_23[2] == v_array_22), " ", "v_int_real_real_7.0", " ", v_int_real_real_7.0, " ", "v_seq_23", " ", v_seq_23, " ", "v_int_real_real_7.1", " ", (v_int_real_real_7.1 == -3.08), " ", "v_seq_24", " ", v_seq_24, " ", "v_bool_13", " ", v_bool_13, " ", "v_array_70[1]", " ", (v_array_70[1] == -9.31), " ", "v_bool_11", " ", v_bool_11, " ", "v_seq_20", " ", v_seq_20, " ", "v_bool_12", " ", v_bool_12, " ", "v_bool_10", " ", v_bool_10, " ", "v_array_6[0]", " ", v_array_6[0], " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_array_17[2]", " ", v_array_17[2], " ", "v_array_12[1]", " ", v_array_12[1], " ", "v_array_68[1]", " ", (v_array_68[1] == -21.07), " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_array_76[0]", " ", v_array_76[0], " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_DT_1_1_17", " ", v_DT_1_1_17, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_array_19", " ", (v_array_19 == v_array_19), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_array_70[2]", " ", (v_array_70[2] == 4.16), " ", "v_bool_seq_3.1", " ", (v_bool_seq_3.1 == [-3.49, -20.22, 25.78, -2.51]), " ", "v_array_5[0]", " ", (v_array_5[0] == v_array_1), " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_DT_1_1_14", " ", v_DT_1_1_14, " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_bool_seq_3.0", " ", v_bool_seq_3.0, " ", "v_DT_1_1_13", " ", v_DT_1_1_13, " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_map_4", " ", (v_map_4 == map['t' := false, 'T' := false, 'k' := true, 'O' := true]), " ", "v_map_7", " ", (v_map_7 == map[multiset{} := 'e', multiset{v_int_real_real_30} := 'X', multiset{v_int_real_real_31, v_int_real_real_32, v_int_real_real_33, v_int_real_real_34} := 'x', multiset{v_int_real_real_35} := 'I', multiset{v_int_real_real_36, v_int_real_real_37, v_int_real_real_38, v_int_real_real_39} := 'p']), " ", "v_map_6", " ", (v_map_6 == map[v_bool_seq_16 := true, v_bool_seq_17 := false, v_bool_seq_18 := true, v_bool_seq_19 := false]), " ", "v_map_9", " ", "v_char_4", " ", (v_char_4 == 'R'), " ", "v_map_8", " ", (v_map_8 == map[multiset{} := v_array_71, multiset{[17, 25, 1], [7, 17, 24]} := v_array_68, multiset{[10, 0, -3]} := v_array_70, multiset{[2], [], [3, 9, 12, -25]} := v_array_69]), " ", "v_array_17[1]", " ", v_array_17[1], " ", "v_array_11[3]", " ", v_array_11[3], " ", "v_char_9", " ", (v_char_9 == 'o'), " ", "v_int_real_real_13.1", " ", (v_int_real_real_13.1 == -0.22), " ", "v_char_8", " ", (v_char_8 == 'F'), " ", "v_array_12[0]", " ", v_array_12[0], " ", "v_int_real_real_13.2", " ", (v_int_real_real_13.2 == 19.79), " ", "v_int_real_real_13.0", " ", v_int_real_real_13.0, " ", "v_array_68[0]", " ", (v_array_68[0] == 13.40), " ", "v_map_3", " ", (v_map_3 == map[true := 'l']), " ", "v_array_76[1]", " ", v_array_76[1], " ", "v_int_real_real_8.1", " ", (v_int_real_real_8.1 == -1.91), " ", "v_int_real_real_8.2", " ", (v_int_real_real_8.2 == -20.69), " ", "v_int_real_real_8.0", " ", v_int_real_real_8.0, " ", "v_array_23[0]", " ", (v_array_23[0] == v_array_20), " ", "v_array_70[3]", " ", (v_array_70[3] == 4.91), " ", "v_array_71[0]", " ", (v_array_71[0] == 20.44), " ", "v_array_5[1]", " ", (v_array_5[1] == v_array_2), " ", "v_array_7[1]", " ", v_array_7[1], " ", "v_array_65[0]", " ", (v_array_65[0] == -0.09), " ", "v_array_12[3]", " ", v_array_12[3], " ", "v_array_13[0]", " ", (v_array_13[0] == v_array_10), " ", "v_array_18[1]", " ", v_array_18[1], " ", "v_array_24[2]", " ", v_array_24[2], " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_real_bool_3", " ", (v_real_bool_3 == v_real_bool_6), " ", "v_real_bool_2", " ", (v_real_bool_2 == v_real_bool_7), " ", "v_array_7[0]", " ", v_array_7[0], " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_7[2]", " ", v_array_7[2], " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_17[3]", " ", v_array_17[3], " ", "v_array_18[0]", " ", v_array_18[0], " ", "v_array_12[2]", " ", v_array_12[2], " ", "v_int_real_real_9.2", " ", (v_int_real_real_9.2 == 4.16), " ", "v_array_24[3]", " ", v_array_24[3], " ", "v_int_real_real_9.0", " ", v_int_real_real_9.0, " ", "v_int_real_real_9.1", " ", (v_int_real_real_9.1 == 15.40), " ", "v_array_25[0]", " ", v_array_25[0], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_27", " ", (v_array_27 == v_array_27), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_array_6[2]", " ", v_array_6[2], " ", "v_array_19[0]", " ", (v_array_19[0] == v_array_14), " ", "v_array_13[2]", " ", (v_array_13[2] == v_array_12), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == -14.92), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == -25.65), " ", "v_array_69[2]", " ", (v_array_69[2] == -12.59), " ", "v_bool_seq_1.0", " ", v_bool_seq_1.0, " ", "v_array_24[0]", " ", v_array_24[0], " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_bool_seq_1.1", " ", (v_bool_seq_1.1 == [8.43, 23.09, -26.95, 17.33]), " ", "v_array_6[1]", " ", v_array_6[1], " ", "v_array_13[1]", " ", (v_array_13[1] == v_array_11), " ", "v_array_18[2]", " ", v_array_18[2], " ", "v_array_12[4]", " ", v_array_12[4], " ", "v_array_68[4]", " ", (v_array_68[4] == 18.04), " ", "v_array_69[1]", " ", (v_array_69[1] == -24.57), " ", "v_array_24[1]", " ", v_array_24[1], " ", "v_array_1[1]", " ", v_array_1[1], "\n";
			return ;
		}
		var v_seq_30: seq<bool> := [true, true];
		var v_seq_31: seq<bool> := v_seq_30;
		var v_int_52: int := 15;
		var v_int_53: int := safe_index_seq(v_seq_31, v_int_52);
		var v_int_54: int := v_int_53;
		var v_seq_32: seq<bool> := [];
		var v_seq_33: seq<bool> := v_seq_32;
		var v_int_55: int := 20;
		var v_int_56: int := safe_index_seq(v_seq_33, v_int_55);
		var v_int_57: int := v_int_56;
		var v_seq_34: seq<bool> := ((if ((|v_seq_30| > 0)) then (v_seq_30[v_int_54 := true]) else (v_seq_30)) + (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_57 := false]) else (v_seq_32)));
		var v_int_58: int := v_int_28;
		if (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_58]) else (v_array_3[2])) {
			return ;
		} else {
			var v_map_20: map<int, bool> := map[6 := false, 11 := false, 18 := true, 14 := true];
			var v_int_59: int := 6;
			var v_seq_35: seq<bool> := [true, true];
			var v_seq_36: seq<bool> := v_seq_35;
			var v_int_60: int := 16;
			var v_int_61: int := safe_index_seq(v_seq_36, v_int_60);
			var v_int_62: int := v_int_61;
			var v_seq_37: seq<bool> := (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_62 := false]) else (v_seq_35));
			var v_seq_38: seq<bool> := v_seq_37;
			var v_map_21: map<bool, int> := map[true := 4, true := 14, true := 13];
			var v_bool_18: bool := false;
			var v_int_63: int := (if ((v_bool_18 in v_map_21)) then (v_map_21[v_bool_18]) else (5));
			var v_int_64: int := safe_index_seq(v_seq_38, v_int_63);
			var v_int_65: int := v_int_64;
			var v_map_22: map<bool, bool> := map[true := false, false := false, false := false, true := false, false := true];
			var v_bool_19: bool := true;
			var v_seq_39: seq<bool> := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_65 := (if ((v_bool_19 in v_map_22)) then (v_map_22[v_bool_19]) else (false))]) else (v_seq_37));
			var v_map_24: map<bool, int> := map[true := 10, true := 17, true := 28, true := 20, false := 10][true := 6];
			var v_map_23: map<bool, bool> := map[false := true, true := true, true := true];
			var v_bool_20: bool := true;
			var v_bool_21: bool := (if ((v_bool_20 in v_map_23)) then (v_map_23[v_bool_20]) else (true));
			var v_int_66: int := (if ((v_bool_21 in v_map_24)) then (v_map_24[v_bool_21]) else ((28 - -26)));
			var v_seq_40: seq<bool> := [];
			var v_int_67: int := 5;
			v_bool_12, v_array_21[3], v_bool_3 := v_array_3[2], (if ((match false {
				case _ => (16 <= 29)
			})) then (((if ((v_int_59 in v_map_20)) then (v_map_20[v_int_59]) else (true)) <== !(false))) else ((match false {
				case _ => v_array_1[1]
			}))), (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_66]) else ((if (({false} > {false, false})) then ((if ((|v_seq_40| > 0)) then (v_seq_40[v_int_67]) else (false))) else (v_bool_5))));
		}
		if !(v_array_11[3]) {
			
		} else {
			var v_map_25: map<bool, bool> := map[false := true, true := false, false := false, true := true][false := false];
			var v_bool_22: bool := (match false {
				case _ => false
			});
			if (match false {
				case _ => (if ((v_bool_22 in v_map_25)) then (v_map_25[v_bool_22]) else ((if (true) then (true) else (true))))
			}) {
				var v_seq_41: seq<seq<int>> := [[24, 6, 9, 18]];
				var v_int_70: int := 10;
				var v_seq_42: seq<int> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_70]) else ([0]));
				var v_map_26: map<bool, int> := map[true := 16, false := 25, true := 1];
				var v_bool_23: bool := false;
				var v_int_71: int := (if ((v_bool_23 in v_map_26)) then (v_map_26[v_bool_23]) else (23));
				var v_seq_43: seq<int> := [28];
				var v_seq_44: seq<int> := (if ((|v_seq_43| > 0)) then (v_seq_43[9..0]) else (v_seq_43));
				var v_int_72: int := (20 - 8);
				var v_int_68: int := (match true {
					case _ => (if ((|v_seq_44| > 0)) then (v_seq_44[v_int_72]) else ((if (true) then (21) else (26))))
				});
				var v_seq_45: seq<int> := [3, 1, 4];
				var v_seq_47: seq<int> := (if ((|v_seq_45| > 0)) then (v_seq_45[27..16]) else (v_seq_45));
				var v_seq_46: seq<int> := [13];
				var v_int_73: int := 19;
				var v_seq_48: seq<int> := (if ((|v_seq_47| > 0)) then (v_seq_47[|[true, true, false, false]|..(if ((|v_seq_46| > 0)) then (v_seq_46[v_int_73]) else (5))]) else (v_seq_47));
				var v_int_74: int := (v_int_41 + (0 * 12));
				var v_int_69: int := (if ((|v_seq_48| > 0)) then (v_seq_48[v_int_74]) else ((match true {
					case _ => (if (true) then (28) else (-22))
				})));
				while (v_int_68 < v_int_69) 
					decreases v_int_69 - v_int_68;
					invariant (v_int_68 <= v_int_69);
				{
					v_int_68 := (v_int_68 + 1);
				}
				var v_seq_49: seq<int> := [26, 7, 25, 7];
				var v_seq_50: seq<int> := v_seq_49;
				var v_int_77: int := 24;
				var v_int_78: int := safe_index_seq(v_seq_50, v_int_77);
				var v_int_79: int := v_int_78;
				var v_seq_51: seq<int> := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_79 := 13]) else (v_seq_49));
				var v_map_27: map<bool, int> := map[true := 18];
				var v_bool_24: bool := true;
				var v_int_80: int := (if ((v_bool_24 in v_map_27)) then (v_map_27[v_bool_24]) else (-6));
				var v_int_75: int := (if (v_array_26[2]) then ((if ((|v_seq_51| > 0)) then (v_seq_51[v_int_80]) else (v_int_46))) else (v_int_77));
				var v_int_76: int := v_int_real_real_5.0;
				while (v_int_75 < v_int_76) 
					decreases v_int_76 - v_int_75;
					invariant (v_int_75 <= v_int_76);
				{
					v_int_75 := (v_int_75 + 1);
					return ;
				}
				var v_seq_52: seq<bool> := [];
				var v_int_81: int := 13;
				var v_seq_53: seq<bool> := [true, true, true];
				var v_int_82: int := 3;
				v_array_8[1] := (if (((false in [true, false]) !in v_map_27)) then (((if ((|v_seq_52| > 0)) then (v_seq_52[v_int_81]) else (false)) ==> (match false {
					case _ => true
				}))) else ((if ((if ((|v_seq_53| > 0)) then (v_seq_53[v_int_82]) else (false))) then (v_array_10[1]) else ((if (false) then (false) else (false))))));
				var v_map_29: map<bool, bool> := map[false := true, true := false, false := true][false := true];
				var v_map_28: map<bool, bool> := map[false := false, true := true, false := false];
				var v_bool_25: bool := true;
				var v_bool_26: bool := (if ((v_bool_25 in v_map_28)) then (v_map_28[v_bool_25]) else (false));
				if (if ((if ((v_bool_26 in v_map_29)) then (v_map_29[v_bool_26]) else ((false || false)))) then ((match false {
					case _ => (false ==> false)
				})) else (v_array_24[4])) {
					return ;
				}
				assert true;
				expect true;
				var v_seq_55: seq<bool> := v_seq_32;
				var v_seq_54: seq<int> := [3, 21, 15];
				var v_int_83: int := -7;
				var v_seq_56: seq<bool> := (if ((|v_seq_55| > 0)) then (v_seq_55[(if ((|v_seq_54| > 0)) then (v_seq_54[v_int_83]) else (5))..0]) else (v_seq_55));
				var v_DT_5_1_1: DT_5<bool> := DT_5_1;
				var v_DT_5_1_2: DT_5<bool> := DT_5_1;
				var v_DT_5_1_3: DT_5<bool> := DT_5_1;
				var v_DT_5_1_4: DT_5<bool> := DT_5_1;
				var v_map_30: map<bool, int> := map[true := 13, false := 0];
				var v_bool_27: bool := true;
				var v_int_84: int := (if ((v_DT_5_1_1 !in [v_DT_5_1_2, v_DT_5_1_3, v_DT_5_1_4])) then ((if ((v_bool_27 in v_map_30)) then (v_map_30[v_bool_27]) else (25))) else ((6 % 1)));
				if (if ((|v_seq_56| > 0)) then (v_seq_56[v_int_84]) else (v_array_11[0])) {
					return ;
				} else {
					return ;
				}
			}
			var v_seq_57: seq<seq<bool>> := [[true, false, false, false], [true], [false]];
			var v_seq_58: seq<seq<bool>> := v_seq_57;
			var v_int_85: int := 28;
			var v_int_86: int := safe_index_seq(v_seq_58, v_int_85);
			var v_int_87: int := v_int_86;
			var v_seq_59: seq<seq<bool>> := (if ((|v_seq_57| > 0)) then (v_seq_57[v_int_87 := [true]]) else (v_seq_57));
			var v_int_88: int := (if (true) then (17) else (21));
			var v_seq_60: seq<bool> := [false];
			var v_seq_61: seq<bool> := (if ((|v_seq_59| > 0)) then (v_seq_59[v_int_88]) else ((if ((|v_seq_60| > 0)) then (v_seq_60[25..27]) else (v_seq_60))));
			var v_int_89: int := (if (v_bool_int_bool_1.2) then (v_int_31) else ((16 * 5)));
			var v_seq_62: seq<seq<bool>> := [[true], [true]];
			var v_int_90: int := 7;
			var v_seq_63: seq<bool> := (if ((|v_seq_62| > 0)) then (v_seq_62[v_int_90]) else ([]));
			var v_int_91: int := (match true {
				case _ => 2
			});
			var v_map_31: map<bool, bool> := map[false := true];
			var v_bool_28: bool := true;
			var v_DT_2_2_9: DT_2<bool> := DT_2_2(true, true, false);
			var v_DT_2_2_10: DT_2<bool> := DT_2_2(false, true, false);
			var v_DT_2_2_11: DT_2<bool> := DT_2_2(true, true, true);
			var v_DT_2_2_12: DT_2<bool> := DT_2_2(false, true, false);
			var v_DT_2_2_13: DT_2<bool> := DT_2_2(true, true, false);
			var v_DT_2_2_14: DT_2<bool> := DT_2_2(true, false, true);
			var v_DT_2_2_15: DT_2<bool> := DT_2_2(true, false, false);
			var v_DT_2_2_16: DT_2<bool> := DT_2_2(false, false, true);
			var v_DT_2_2_17: DT_2<bool> := DT_2_2(true, false, false);
			var v_DT_2_2_18: DT_2<bool> := DT_2_2(false, true, true);
			var v_DT_2_2_19: DT_2<bool> := DT_2_2(true, false, true);
			var v_DT_2_2_20: DT_2<bool> := DT_2_2(true, true, true);
			var v_DT_2_2_21: DT_2<bool> := DT_2_2(true, false, false);
			var v_DT_2_2_22: DT_2<bool> := DT_2_2(false, true, true);
			var v_map_32: map<bool, set<DT_2<bool>>> := map[false := {v_DT_2_2_15, v_DT_2_2_16}, true := {}, true := {v_DT_2_2_17}, false := {v_DT_2_2_18, v_DT_2_2_19}, true := {v_DT_2_2_20, v_DT_2_2_21, v_DT_2_2_22}];
			var v_bool_29: bool := true;
			var v_DT_2_2_23: DT_2<bool> := DT_2_2(false, false, false);
			var v_DT_2_2_24: DT_2<bool> := DT_2_2(true, true, true);
			var v_DT_2_2_25: DT_2<bool> := DT_2_2(false, true, true);
			var v_seq_64: seq<array<bool>> := [];
			var v_seq_65: seq<array<bool>> := v_seq_64;
			var v_int_92: int := 12;
			var v_int_93: int := safe_index_seq(v_seq_65, v_int_92);
			var v_int_94: int := v_int_93;
			var v_array_77: array<bool> := new bool[4];
			v_array_77[0] := false;
			v_array_77[1] := false;
			v_array_77[2] := false;
			v_array_77[3] := true;
			var v_seq_66: seq<array<bool>> := (if ((|v_seq_64| > 0)) then (v_seq_64[v_int_94 := v_array_77]) else (v_seq_64));
			var v_seq_67: seq<array<bool>> := v_seq_66;
			var v_int_95: int := (if (true) then (6) else (0));
			var v_int_96: int := safe_index_seq(v_seq_67, v_int_95);
			var v_int_97: int := v_int_96;
			var v_seq_68: seq<array<bool>> := (if ((|v_seq_66| > 0)) then (v_seq_66[v_int_97 := v_array_19[2]]) else (v_seq_66));
			var v_int_98: int := v_int_58;
			var v_seq_69: seq<multiset<bool>> := [multiset{true}, multiset{true}, multiset{}, multiset{true}];
			var v_int_99: int := 14;
			var v_map_33: map<bool, multiset<bool>> := map[true := multiset{true}, false := multiset{true, true, false, true}][false := multiset{true, true}];
			var v_bool_30: bool := (if (true) then (false) else (false));
			v_array_21[0], v_array_24[2], v_array_19[4], v_array_18[2] := (if ((|v_seq_61| > 0)) then (v_seq_61[v_int_89]) else ((if ((|v_seq_63| > 0)) then (v_seq_63[v_int_91]) else ((if ((v_bool_28 in v_map_31)) then (v_map_31[v_bool_28]) else (false)))))), ((({v_DT_2_2_9, v_DT_2_2_10, v_DT_2_2_11, v_DT_2_2_12} * {v_DT_2_2_13, v_DT_2_2_14}) !! (if ((v_bool_29 in v_map_32)) then (v_map_32[v_bool_29]) else ({v_DT_2_2_23, v_DT_2_2_24, v_DT_2_2_25}))) !in ((if (true) then (map[true := false]) else (map[true := true, false := false, false := true, true := false, true := false])) + map[false := false, true := true, true := false, false := false, true := false][false := false])), (if ((|v_seq_68| > 0)) then (v_seq_68[v_int_98]) else (v_array_19[2])), ((if ((match 26.83 {
				case _ => true
			})) then ((if (false) then (multiset{false}) else (multiset{true, false, true}))) else ((if ((|v_seq_69| > 0)) then (v_seq_69[v_int_99]) else (multiset{false})))) <= (if ((v_bool_30 in v_map_33)) then (v_map_33[v_bool_30]) else ((match false {
				case _ => multiset({false, true})
			}))));
			var v_map_34: map<char, int> := (map['J' := 22, 'C' := 11, 'T' := 26, 'i' := 3, 'C' := 24] - {'v', 'U', 'f'});
			var v_seq_70: seq<char> := ['H'];
			var v_int_102: int := 25;
			var v_char_13: char := (if ((|v_seq_70| > 0)) then (v_seq_70[v_int_102]) else ('U'));
			var v_seq_71: seq<int> := ([-2] + [28, -3, 0, 27]);
			var v_int_103: int := (match true {
				case _ => 23
			});
			var v_int_100: int := (if ((if ((match true {
				case _ => true
			})) then ((match true {
				case _ => false
			})) else (([] < [true, false])))) then ((if ((v_char_13 in v_map_34)) then (v_map_34[v_char_13]) else ((match true {
				case _ => 16
			})))) else ((if ((|v_seq_71| > 0)) then (v_seq_71[v_int_103]) else (v_int_real_real_5.0))));
			var v_seq_72: seq<bool> := [false];
			var v_seq_73: seq<bool> := v_seq_72;
			var v_int_104: int := 25;
			var v_int_105: int := safe_index_seq(v_seq_73, v_int_104);
			var v_int_106: int := v_int_105;
			var v_seq_75: seq<bool> := (if ((|v_seq_72| > 0)) then (v_seq_72[v_int_106 := true]) else (v_seq_72));
			var v_map_35: map<seq<int>, int> := map[[1, 6] := -21, [24, 29, 15, 16] := 7, [21] := -11, [8, 2, 23] := 28];
			var v_seq_74: seq<int> := [20];
			var v_int_107: int := (if ((v_seq_74 in v_map_35)) then (v_map_35[v_seq_74]) else (27));
			var v_map_36: map<char, bool> := map['d' := false, 'B' := true, 'g' := true, 'S' := true, 'w' := false];
			var v_char_14: char := 'Q';
			var v_bool_bool_6: (bool, bool) := (false, false);
			var v_bool_bool_7: (bool, bool) := (true, false);
			var v_bool_bool_8: (bool, bool) := (true, false);
			var v_bool_bool_9: (bool, bool) := (true, false);
			var v_bool_bool_10: (bool, bool) := (false, false);
			var v_bool_bool_11: (bool, bool) := (false, false);
			var v_bool_bool_12: (bool, bool) := (false, true);
			var v_bool_bool_13: (bool, bool) := (false, true);
			var v_bool_bool_14: (bool, bool) := (true, false);
			var v_bool_bool_15: (bool, bool) := (true, true);
			var v_bool_bool_16: (bool, bool) := (false, false);
			var v_map_37: map<(bool, bool), int> := (match 13 {
				case _ => map[v_bool_bool_16 := 12]
			});
			var v_bool_bool_17: (bool, bool) := (true, true);
			var v_bool_bool_18: (bool, bool) := (false, true);
			var v_seq_76: seq<(bool, bool)> := [v_bool_bool_17, v_bool_bool_18];
			var v_int_108: int := 17;
			var v_bool_bool_19: (bool, bool) := (true, true);
			var v_bool_bool_20: (bool, bool) := (if ((|v_seq_76| > 0)) then (v_seq_76[v_int_108]) else (v_bool_bool_19));
			var v_map_38: map<seq<bool>, int> := map[[false, false, false, true] := 1, [false, false, true, true] := -20][[] := 7];
			var v_seq_77: seq<bool> := [false];
			var v_seq_79: seq<bool> := (if ((|v_seq_77| > 0)) then (v_seq_77[4..23]) else (v_seq_77));
			var v_seq_78: seq<int> := [21];
			var v_int_109: int := 6;
			var v_int_101: int := (if ((if ((|v_seq_75| > 0)) then (v_seq_75[v_int_107]) else ((if ((v_char_14 in v_map_36)) then (v_map_36[v_char_14]) else (true))))) then ((if ((v_bool_bool_20 in v_map_37)) then (v_map_37[v_bool_bool_20]) else ((match false {
				case _ => 1
			})))) else ((if ((v_seq_79 in v_map_38)) then (v_map_38[v_seq_79]) else ((if ((|v_seq_78| > 0)) then (v_seq_78[v_int_109]) else (20))))));
			while (v_int_100 < v_int_101) 
				decreases v_int_101 - v_int_100;
				invariant (v_int_100 <= v_int_101);
			{
				v_int_100 := (v_int_100 + 1);
				var v_seq_80: seq<DT_5<bool>> := [];
				var v_seq_81: seq<DT_5<bool>> := v_seq_80;
				var v_int_110: int := 18;
				var v_int_111: int := safe_index_seq(v_seq_81, v_int_110);
				var v_int_112: int := v_int_111;
				var v_DT_5_1_5: DT_5<bool> := DT_5_1;
				var v_seq_82: seq<DT_5<bool>> := (if ((|v_seq_80| > 0)) then (v_seq_80[v_int_112 := v_DT_5_1_5]) else (v_seq_80));
				var v_int_113: int := v_int_101;
				var v_DT_5_1_6: DT_5<bool> := DT_5_1;
				var v_seq_83: seq<DT_5<bool>> := [v_DT_5_1_6];
				var v_int_114: int := 16;
				var v_DT_5_1_7: DT_5<bool> := DT_5_1;
				var v_int_int_1: (int, int) := (8, 9);
				var v_int_bool_int_int_1: (int, bool, (int, int)) := (12, false, v_int_int_1);
				var v_int_int_2: (int, int) := (4, -19);
				var v_int_bool_int_int_2: (int, bool, (int, int)) := (5, true, v_int_int_2);
				var v_map_39: map<(int, bool, (int, int)), bool> := map[v_int_bool_int_int_1 := true, v_int_bool_int_int_2 := false];
				var v_int_int_3: (int, int) := (27, 1);
				var v_int_bool_int_int_3: (int, bool, (int, int)) := (19, true, v_int_int_3);
				var v_int_bool_int_int_4: (int, bool, (int, int)) := v_int_bool_int_int_3;
				var v_DT_5_1_8: DT_5<bool> := DT_5_1;
				var v_DT_5_1_9: DT_5<bool> := DT_5_1;
				var v_DT_5_1_10: DT_5<bool> := DT_5_1;
				var v_DT_5_1_11: DT_5<bool> := DT_5_1;
				var v_seq_84: seq<DT_5<bool>> := [v_DT_5_1_10, v_DT_5_1_11];
				var v_int_115: int := 5;
				var v_DT_5_1_12: DT_5<bool> := DT_5_1;
				var v_seq_85: seq<bool> := [true, true, true];
				var v_int_116: int := 17;
				var v_DT_5_1_13: DT_5<bool> := DT_5_1;
				var v_DT_5_1_14: DT_5<bool> := DT_5_1;
				var v_DT_5_1_15: DT_5<bool> := DT_5_1;
				var v_DT_5_1_16: DT_5<bool> := DT_5_1;
				var v_seq_86: seq<DT_5<bool>> := [v_DT_5_1_13, v_DT_5_1_14, v_DT_5_1_15, v_DT_5_1_16];
				var v_int_117: int := -19;
				var v_DT_5_1_17: DT_5<bool> := DT_5_1;
				var v_seq_87: seq<DT_5<bool>> := [];
				var v_int_118: int := 25;
				var v_DT_5_1_18: DT_5<bool> := DT_5_1;
				var v_seq_88: seq<real> := (match 'a' {
					case _ => []
				});
				var v_DT_7_1_1: DT_7 := DT_7_1;
				var v_DT_7_1_2: DT_7 := DT_7_1;
				var v_DT_7_1_3: DT_7 := DT_7_1;
				var v_DT_7_1_4: DT_7 := DT_7_1;
				var v_DT_7_1_5: DT_7 := DT_7_1;
				var v_map_40: map<DT_7, int> := map[v_DT_7_1_1 := 5, v_DT_7_1_2 := 4, v_DT_7_1_3 := 2, v_DT_7_1_4 := 6, v_DT_7_1_5 := -15];
				var v_DT_7_1_6: DT_7 := DT_7_1;
				var v_DT_7_1_7: DT_7 := v_DT_7_1_6;
				var v_map_41: map<int, int> := map[7 := 22, 2 := 2];
				var v_int_119: int := 6;
				var v_seq_91: seq<real> := (if ((|v_seq_88| > 0)) then (v_seq_88[(if ((v_DT_7_1_7 in v_map_40)) then (v_map_40[v_DT_7_1_7]) else (24))..(if ((v_int_119 in v_map_41)) then (v_map_41[v_int_119]) else (7))]) else (v_seq_88));
				var v_map_42: map<real, int> := (match 24 {
					case _ => map[18.40 := 9, -22.03 := 10, 25.47 := 20]
				});
				var v_seq_89: seq<real> := [28.92, 14.39, 12.92];
				var v_int_120: int := 25;
				var v_real_3: real := (if ((|v_seq_89| > 0)) then (v_seq_89[v_int_120]) else (-28.94));
				var v_seq_90: seq<int> := [11, 8];
				var v_int_121: int := -17;
				var v_int_122: int := (if ((v_real_3 in v_map_42)) then (v_map_42[v_real_3]) else ((if ((|v_seq_90| > 0)) then (v_seq_90[v_int_121]) else (23))));
				var v_DT_5_1_19: DT_5<bool>, v_real_4: real := (match true {
					case _ => (if ((if ((|v_seq_85| > 0)) then (v_seq_85[v_int_116]) else (true))) then ((if ((|v_seq_86| > 0)) then (v_seq_86[v_int_117]) else (v_DT_5_1_17))) else ((if ((|v_seq_87| > 0)) then (v_seq_87[v_int_118]) else (v_DT_5_1_18))))
				}), (if ((|v_seq_91| > 0)) then (v_seq_91[v_int_122]) else ((match 21 {
					case _ => (match false {
						case _ => -7.29
					})
				})));
			}
			var v_DT_6_4_1: DT_6<bool, int> := DT_6_4(true, {true}, true, 14);
			var v_DT_6_4_multiset_1: (DT_6<bool, int>, multiset<real>) := (v_DT_6_4_1, multiset{-12.14});
			var v_bool_real_real_1: (bool, real, real) := (false, -19.89, 24.43);
			var v_bool_real_real_2: (bool, real, real) := (false, 1.61, -19.71);
			var v_bool_real_real_3: (bool, real, real) := (false, 13.86, 1.48);
			var v_bool_real_real_4: (bool, real, real) := (false, -24.60, -22.74);
			var v_map_43: map<(DT_6<bool, int>, multiset<real>), map<seq<(bool, real, real)>, int>> := map[v_DT_6_4_multiset_1 := map[[v_bool_real_real_1, v_bool_real_real_2, v_bool_real_real_3, v_bool_real_real_4] := 13]];
			var v_DT_6_4_2: DT_6<bool, int> := DT_6_4(true, {}, true, 14);
			var v_DT_6_4_multiset_2: (DT_6<bool, int>, multiset<real>) := (v_DT_6_4_2, multiset({-15.39, 17.43, 17.99, -29.60}));
			var v_DT_6_4_multiset_3: (DT_6<bool, int>, multiset<real>) := v_DT_6_4_multiset_2;
			var v_bool_real_real_5: (bool, real, real) := (true, 29.56, -7.27);
			var v_bool_real_real_6: (bool, real, real) := (true, 26.52, -6.47);
			var v_bool_real_real_7: (bool, real, real) := (true, -2.21, 20.86);
			var v_bool_real_real_8: (bool, real, real) := (false, 22.96, -16.06);
			var v_bool_real_real_9: (bool, real, real) := (false, -6.04, -10.40);
			var v_bool_real_real_10: (bool, real, real) := (true, -25.47, 7.85);
			var v_bool_real_real_11: (bool, real, real) := (false, -11.34, -6.09);
			var v_map_44: map<seq<(bool, real, real)>, int> := (if ((v_DT_6_4_multiset_3 in v_map_43)) then (v_map_43[v_DT_6_4_multiset_3]) else (map[[v_bool_real_real_5] := 29, [v_bool_real_real_6, v_bool_real_real_7] := 5, [v_bool_real_real_8, v_bool_real_real_9] := 10, [v_bool_real_real_10] := 21, [v_bool_real_real_11] := 1]));
			var v_bool_real_real_12: (bool, real, real) := (false, 4.82, -26.35);
			var v_bool_real_real_13: (bool, real, real) := (false, -20.06, -20.78);
			var v_bool_real_real_14: (bool, real, real) := (false, 28.87, -26.82);
			var v_seq_92: seq<(bool, real, real)> := [v_bool_real_real_12, v_bool_real_real_13, v_bool_real_real_14];
			var v_seq_93: seq<(bool, real, real)> := v_seq_92;
			var v_int_124: int := 5;
			var v_int_125: int := safe_index_seq(v_seq_93, v_int_124);
			var v_int_126: int := v_int_125;
			var v_bool_real_real_15: (bool, real, real) := (false, -16.59, 0.89);
			var v_seq_94: seq<(bool, real, real)> := (if ((|v_seq_92| > 0)) then (v_seq_92[v_int_126 := v_bool_real_real_15]) else (v_seq_92));
			var v_seq_95: seq<int> := [3, 0, 6, 19];
			var v_seq_96: seq<int> := (if ((|v_seq_95| > 0)) then (v_seq_95[11..14]) else (v_seq_95));
			var v_int_127: int := (if (true) then (6) else (21));
			var v_seq_97: seq<int> := [16, 5, 23, 15];
			var v_seq_98: seq<int> := [];
			var v_seq_99: seq<int> := v_seq_98;
			var v_int_128: int := 25;
			var v_int_129: int := safe_index_seq(v_seq_99, v_int_128);
			var v_int_130: int := v_int_129;
			var v_seq_100: seq<int> := (match 27 {
				case _ => (if ((|v_seq_98| > 0)) then (v_seq_98[v_int_130 := 10]) else (v_seq_98))
			});
			var v_map_45: map<set<bool>, real> := map[{true, true} := -8.05, {false, false, true, true} := 28.49, {false, false, false, false} := -1.88];
			var v_set_4: set<bool> := {false, true, true};
			var v_int_131: int := ((if ((v_set_4 in v_map_45)) then (v_map_45[v_set_4]) else (-1.81))).Floor;
			var v_map_46: map<bool, int> := (map[true := -10] + map[false := 7, false := -7, false := 19, false := -24, false := -19]);
			var v_bool_31: bool := (true in [false, false]);
			var v_seq_101: seq<int> := [13, 3, 0];
			var v_int_132: int := 8;
			var v_int_144: int, v_int_145: int := (if (((map[false := -14.72]).Values == ({} + {14.67}))) then ((if ((v_seq_94 in v_map_44)) then (v_map_44[v_seq_94]) else ((24 + -28)))) else ((if ((|v_seq_96| > 0)) then (v_seq_96[v_int_127]) else ((if (false) then (21) else (4)))))), (if ((|v_seq_100| > 0)) then (v_seq_100[v_int_131]) else ((if ((v_bool_31 in v_map_46)) then (v_map_46[v_bool_31]) else ((if ((|v_seq_101| > 0)) then (v_seq_101[v_int_132]) else (22))))));
			for v_int_123 := v_int_144 to v_int_145 
				invariant (v_int_145 - v_int_123 >= 0)
			{
				var v_bool_int_int_1: (bool, int, int) := (false, 13, 27);
				var v_bool_int_int_2: (bool, int, int) := (true, 20, 13);
				var v_bool_int_int_3: (bool, int, int) := (false, 14, 18);
				var v_bool_int_int_4: (bool, int, int) := (true, 20, 9);
				var v_bool_int_int_5: (bool, int, int) := (true, -17, -5);
				var v_bool_int_int_6: (bool, int, int) := (false, 25, 18);
				var v_bool_int_int_7: (bool, int, int) := (false, 13, 3);
				var v_bool_int_int_8: (bool, int, int) := (true, 23, 21);
				var v_bool_int_int_9: (bool, int, int) := (true, 26, 27);
				var v_map_47: map<seq<(bool, int, int)>, int> := map[[v_bool_int_int_1, v_bool_int_int_2] := 22, [v_bool_int_int_3, v_bool_int_int_4] := 5, [v_bool_int_int_5, v_bool_int_int_6] := 24, [v_bool_int_int_7, v_bool_int_int_8, v_bool_int_int_9] := 12];
				var v_bool_int_int_10: (bool, int, int) := (true, 22, -15);
				var v_seq_102: seq<(bool, int, int)> := [v_bool_int_int_10];
				var v_seq_103: seq<int> := (match 25 {
					case _ => [-28, -15]
				});
				var v_int_135: int := (-23 * 15);
				var v_int_133: int := (match false {
					case _ => (if ((|v_seq_103| > 0)) then (v_seq_103[v_int_135]) else ((match 'O' {
						case _ => 21
					})))
				});
				var v_seq_104: seq<int> := [0];
				var v_seq_105: seq<int> := v_seq_104;
				var v_int_136: int := 4;
				var v_int_137: int := safe_index_seq(v_seq_105, v_int_136);
				var v_int_138: int := v_int_137;
				var v_seq_106: seq<int> := (if ((|v_seq_104| > 0)) then (v_seq_104[v_int_138 := 14]) else (v_seq_104));
				var v_seq_108: seq<int> := (if ((|v_seq_106| > 0)) then (v_seq_106[(if (false) then (4) else (19))..v_int_127]) else (v_seq_106));
				var v_seq_107: seq<int> := [];
				var v_int_139: int := 10;
				var v_int_140: int := ((if ((|v_seq_107| > 0)) then (v_seq_107[v_int_139]) else (17)) - (if (true) then (3) else (11)));
				var v_map_48: map<bool, int> := map[false := 27, true := 9, true := 27];
				var v_bool_32: bool := true;
				var v_int_134: int := (if ((|v_seq_108| > 0)) then (v_seq_108[v_int_140]) else ((v_int_127 - (if ((v_bool_32 in v_map_48)) then (v_map_48[v_bool_32]) else (19)))));
				while (v_int_133 < v_int_134) 
					decreases v_int_134 - v_int_133;
					invariant (v_int_133 <= v_int_134);
				{
					v_int_133 := (v_int_133 + 1);
					return ;
				}
				var v_int_142: int, v_int_143: int := v_int_real_real_13.0, v_int_137;
				for v_int_141 := v_int_142 to v_int_143 
					invariant (v_int_143 - v_int_141 >= 0)
				{
					return ;
				}
				var v_bool_33: bool, v_char_15: char, v_set_5: set<bool> := v_bool_int_bool_1.2, v_char_10, v_DT_6_4_2.DT_6_4_2;
			}
			var v_seq_109: seq<multiset<(seq<bool>, DT_8)>> := [];
			var v_int_146: int := 12;
			var v_DT_8_1_1: DT_8 := DT_8_1;
			var v_seq_DT_8_1_1: (seq<bool>, DT_8) := ([true, false], v_DT_8_1_1);
			var v_DT_8_1_2: DT_8 := DT_8_1;
			var v_seq_DT_8_1_2: (seq<bool>, DT_8) := ([], v_DT_8_1_2);
			var v_DT_8_1_3: DT_8 := DT_8_1;
			var v_seq_DT_8_1_3: (seq<bool>, DT_8) := ([true, true], v_DT_8_1_3);
			var v_DT_8_1_4: DT_8 := DT_8_1;
			var v_seq_DT_8_1_4: (seq<bool>, DT_8) := ([false], v_DT_8_1_4);
			var v_DT_8_1_5: DT_8 := DT_8_1;
			var v_seq_DT_8_1_5: (seq<bool>, DT_8) := ([], v_DT_8_1_5);
			var v_DT_8_1_6: DT_8 := DT_8_1;
			var v_seq_DT_8_1_6: (seq<bool>, DT_8) := ([], v_DT_8_1_6);
			var v_DT_8_1_7: DT_8 := DT_8_1;
			var v_seq_DT_8_1_7: (seq<bool>, DT_8) := ([false], v_DT_8_1_7);
			var v_DT_8_1_8: DT_8 := DT_8_1;
			var v_seq_DT_8_1_8: (seq<bool>, DT_8) := ([false, true, false], v_DT_8_1_8);
			var v_DT_8_1_9: DT_8 := DT_8_1;
			var v_seq_DT_8_1_9: (seq<bool>, DT_8) := ([false], v_DT_8_1_9);
			var v_DT_8_1_10: DT_8 := DT_8_1;
			var v_seq_DT_8_1_10: (seq<bool>, DT_8) := ([true, true, false, false], v_DT_8_1_10);
			var v_DT_8_1_11: DT_8 := DT_8_1;
			var v_seq_DT_8_1_11: (seq<bool>, DT_8) := ([false, false], v_DT_8_1_11);
			var v_DT_8_1_12: DT_8 := DT_8_1;
			var v_seq_DT_8_1_12: (seq<bool>, DT_8) := ([true, false], v_DT_8_1_12);
			var v_map_49: map<bool, multiset<(seq<bool>, DT_8)>> := map[true := multiset({v_seq_DT_8_1_11, v_seq_DT_8_1_12}), false := multiset{}, true := multiset{}, false := multiset({})];
			var v_bool_34: bool := false;
			var v_DT_8_1_13: DT_8 := DT_8_1;
			var v_seq_DT_8_1_13: (seq<bool>, DT_8) := ([true], v_DT_8_1_13);
			var v_DT_8_1_14: DT_8 := DT_8_1;
			var v_seq_DT_8_1_14: (seq<bool>, DT_8) := ([true, true, true, false], v_DT_8_1_14);
			var v_DT_1_1_18: DT_1<bool, bool> := DT_1_1;
			var v_DT_4_5_1: DT_4 := DT_4_5;
			var v_DT_1_1_DT_4_5_bool_1: (DT_1<bool, bool>, DT_4, bool) := (v_DT_1_1_18, v_DT_4_5_1, true);
			var v_DT_8_1_15: DT_8 := DT_8_1;
			var v_seq_DT_8_1_15: (seq<bool>, DT_8) := ([false, true, true], v_DT_8_1_15);
			var v_DT_8_1_16: DT_8 := DT_8_1;
			var v_seq_DT_8_1_16: (seq<bool>, DT_8) := ([], v_DT_8_1_16);
			var v_DT_1_1_19: DT_1<bool, bool> := DT_1_1;
			var v_DT_4_5_2: DT_4 := DT_4_5;
			var v_DT_1_1_DT_4_5_bool_2: (DT_1<bool, bool>, DT_4, bool) := (v_DT_1_1_19, v_DT_4_5_2, false);
			var v_DT_8_1_17: DT_8 := DT_8_1;
			var v_seq_DT_8_1_17: (seq<bool>, DT_8) := ([false, false, false, true], v_DT_8_1_17);
			var v_DT_8_1_18: DT_8 := DT_8_1;
			var v_seq_DT_8_1_18: (seq<bool>, DT_8) := ([false, true, true, true], v_DT_8_1_18);
			var v_map_50: map<(DT_1<bool, bool>, DT_4, bool), multiset<(seq<bool>, DT_8)>> := map[v_DT_1_1_DT_4_5_bool_1 := multiset{v_seq_DT_8_1_15, v_seq_DT_8_1_16}, v_DT_1_1_DT_4_5_bool_2 := multiset({v_seq_DT_8_1_17, v_seq_DT_8_1_18})];
			var v_DT_1_1_20: DT_1<bool, bool> := DT_1_1;
			var v_DT_4_5_3: DT_4 := DT_4_5;
			var v_DT_1_1_DT_4_5_bool_3: (DT_1<bool, bool>, DT_4, bool) := (v_DT_1_1_20, v_DT_4_5_3, false);
			var v_DT_1_1_DT_4_5_bool_4: (DT_1<bool, bool>, DT_4, bool) := v_DT_1_1_DT_4_5_bool_3;
			var v_DT_8_1_19: DT_8 := DT_8_1;
			var v_seq_DT_8_1_19: (seq<bool>, DT_8) := ([], v_DT_8_1_19);
			var v_DT_8_1_20: DT_8 := DT_8_1;
			var v_seq_DT_8_1_20: (seq<bool>, DT_8) := ([false, false], v_DT_8_1_20);
			var v_DT_8_1_21: DT_8 := DT_8_1;
			var v_seq_DT_8_1_21: (seq<bool>, DT_8) := ([true, true], v_DT_8_1_21);
			var v_DT_8_1_22: DT_8 := DT_8_1;
			var v_seq_DT_8_1_22: (seq<bool>, DT_8) := ([false, true, false], v_DT_8_1_22);
			var v_DT_8_1_23: DT_8 := DT_8_1;
			var v_seq_DT_8_1_23: (seq<bool>, DT_8) := ([], v_DT_8_1_23);
			if ((match 28 {
				case _ => (match 13 {
					case _ => multiset{}
				})
			}) != (match -5.55 {
				case _ => (multiset{v_seq_DT_8_1_19, v_seq_DT_8_1_20} - multiset{v_seq_DT_8_1_21, v_seq_DT_8_1_22, v_seq_DT_8_1_23})
			})) {
				var v_seq_110: seq<bool> := [true];
				var v_seq_111: seq<bool> := (if ((|v_seq_110| > 0)) then (v_seq_110[9..20]) else (v_seq_110));
				var v_seq_112: seq<bool> := v_seq_111;
				var v_int_147: int := (if (true) then (1) else (20));
				var v_int_148: int := safe_index_seq(v_seq_112, v_int_147);
				var v_int_149: int := v_int_148;
				var v_seq_114: seq<bool> := (if ((|v_seq_111| > 0)) then (v_seq_111[v_int_149 := (if (true) then (false) else (false))]) else (v_seq_111));
				var v_array_78: array<real> := new real[5] [-6.26, -26.36, -27.65, -8.20, 10.57];
				var v_array_79: array<real> := new real[4] [-22.50, 21.46, 5.57, -25.85];
				var v_array_80: array<real> := new real[3] [-10.86, 6.07, -3.94];
				var v_array_81: array<real> := new real[3];
				v_array_81[0] := -29.75;
				v_array_81[1] := 9.40;
				v_array_81[2] := 10.82;
				var v_array_82: array<real> := new real[4] [-23.78, 24.77, 6.42, 20.56];
				var v_array_83: array<real> := new real[3] [26.81, -12.57, -27.77];
				var v_array_84: array<real> := new real[4] [27.76, 9.29, 0.07, 10.12];
				var v_array_85: array<real> := new real[4] [23.21, 2.32, 21.23, -22.19];
				var v_array_86: array<real> := new real[3] [1.52, 23.80, 20.64];
				var v_array_87: array<real> := new real[5] [-2.69, 24.66, -24.37, 7.20, 13.61];
				var v_array_88: array<real> := new real[5] [3.84, -0.42, 29.39, 8.40, 23.43];
				var v_array_89: array<real> := new real[4] [-23.03, -28.03, -20.61, -24.97];
				var v_array_90: array<seq<array<real>>> := new seq<array<real>>[3] [[v_array_78, v_array_79, v_array_80, v_array_81], [v_array_82, v_array_83, v_array_84, v_array_85], [v_array_86, v_array_87, v_array_88, v_array_89]];
				var v_array_91: array<real> := new real[4] [-29.59, 6.37, -15.17, -26.40];
				var v_array_92: array<real> := new real[4] [20.35, -0.53, -6.40, 3.60];
				var v_array_93: array<real> := new real[4] [16.15, -15.62, -18.70, 29.71];
				var v_array_94: array<real> := new real[4] [-26.02, 3.66, 13.38, -23.34];
				var v_array_95: array<real> := new real[3] [2.09, 16.59, 24.34];
				var v_array_96: array<real> := new real[3] [26.26, 0.25, 21.25];
				var v_array_97: array<real> := new real[3] [8.11, 19.88, 14.93];
				var v_array_98: array<real> := new real[3] [4.75, -16.89, 8.17];
				var v_array_99: array<real> := new real[3] [-1.73, -22.57, -12.58];
				var v_array_100: array<seq<array<real>>> := new seq<array<real>>[3] [[v_array_91, v_array_92, v_array_93], [v_array_94, v_array_95], [v_array_96, v_array_97, v_array_98, v_array_99]];
				var v_array_101: array<real> := new real[3] [23.65, 13.70, 15.84];
				var v_array_102: array<real> := new real[5] [-13.14, -2.59, -18.29, -24.85, 13.64];
				var v_array_103: array<real> := new real[5] [14.70, 28.77, -21.88, 18.64, 18.63];
				var v_array_104: array<seq<array<real>>> := new seq<array<real>>[4] [[], [v_array_101, v_array_102, v_array_103], [], []];
				var v_seq_113: seq<array<seq<array<real>>>> := [v_array_90, v_array_100, v_array_104];
				var v_int_150: int := 5;
				var v_array_105: array<real> := new real[4] [29.91, -25.65, 18.30, 9.31];
				var v_array_106: array<real> := new real[5] [12.40, -0.99, -11.13, -19.63, 18.17];
				var v_array_107: array<real> := new real[5] [-21.03, -5.41, 13.01, 13.20, -17.89];
				var v_array_108: array<real> := new real[5] [8.05, 17.24, 4.35, -20.10, -10.52];
				var v_array_109: array<real> := new real[4] [6.31, 5.74, -25.28, 26.93];
				var v_array_110: array<real> := new real[5] [-20.39, 10.80, -23.95, 10.26, -10.08];
				var v_array_111: array<real> := new real[5] [-9.92, 13.71, 13.71, 2.04, -27.36];
				var v_array_112: array<real> := new real[5] [-1.40, -22.40, 22.06, -27.25, 29.10];
				var v_array_113: array<real> := new real[3] [-19.48, 18.42, 19.98];
				var v_array_114: array<real> := new real[4] [-13.24, 6.42, 12.93, 16.78];
				var v_array_115: array<seq<array<real>>> := new seq<array<real>>[3] [[v_array_105, v_array_106, v_array_107], [v_array_108, v_array_109, v_array_110, v_array_111], [v_array_112, v_array_113, v_array_114]];
				var v_int_151: int := (if ((|v_seq_113| > 0)) then (v_seq_113[v_int_150]) else (v_array_115)).Length;
				if (if ((|v_seq_114| > 0)) then (v_seq_114[v_int_151]) else (v_array_77[2])) {
					return ;
				} else {
					return ;
				}
			} else {
				assert true;
				expect true;
				var v_map_52: map<bool, bool> := (map[true := false][true := false] - (map[true := true]).Keys);
				var v_bool_35: bool := (if ((if (false) then (false) else (true))) then ((-25.36 >= 16.92)) else ((match false {
					case _ => true
				})));
				var v_map_51: map<multiset<map<bool, bool>>, seq<bool>> := map[multiset{map[false := false, false := false]} := [true, true], multiset({map[true := true, true := false, false := false]}) := [true, true]];
				var v_multiset_7: multiset<map<bool, bool>> := multiset{map[false := false, true := false, true := false, false := false], map[false := true, false := true], map[false := true, false := true, false := false], map[false := false, false := true, false := false, false := true]};
				var v_seq_115: seq<bool> := (if ((v_multiset_7 in v_map_51)) then (v_map_51[v_multiset_7]) else ([false]));
				var v_int_152: int := (match false {
					case _ => 4
				});
				if (if ((v_bool_35 in v_map_52)) then (v_map_52[v_bool_35]) else ((if ((|v_seq_115| > 0)) then (v_seq_115[v_int_152]) else ((if (false) then (false) else (false)))))) {
					return ;
				}
				var v_map_53: map<bool, bool> := map[false := true, false := false, true := false];
				var v_bool_36: bool := false;
				var v_map_54: map<bool, bool> := map[false := false, false := true, false := false, false := true, true := true];
				var v_bool_37: bool := true;
				var v_map_55: map<bool, bool> := map[true := true, true := false];
				var v_bool_38: bool := false;
				var v_map_56: map<bool, bool> := map[false := true, true := false, true := true];
				var v_bool_39: bool := true;
				var v_int_real_1: (int, real) := (25, 3.73);
				var v_bool_int_real_1: (bool, int, real) := (false, 8, 10.37);
				var v_int_real_bool_int_real_bool_1: ((int, real), (bool, int, real), bool) := (v_int_real_1, v_bool_int_real_1, false);
				var v_seq_116: seq<((int, real), (bool, int, real), bool)> := [v_int_real_bool_int_real_bool_1];
				var v_seq_117: seq<((int, real), (bool, int, real), bool)> := (if ((|v_seq_116| > 0)) then (v_seq_116[17..0]) else (v_seq_116));
				var v_seq_118: seq<((int, real), (bool, int, real), bool)> := (if ((|v_seq_117| > 0)) then (v_seq_117[(-25 % 11)..0]) else (v_seq_117));
				var v_map_58: map<bool, int> := (map[false := 29, true := 25, true := 28] - {true});
				var v_map_57: map<bool, bool> := map[false := true, false := false];
				var v_bool_40: bool := true;
				var v_bool_41: bool := (if ((v_bool_40 in v_map_57)) then (v_map_57[v_bool_40]) else (true));
				var v_int_153: int := (if ((v_bool_41 in v_map_58)) then (v_map_58[v_bool_41]) else (v_int_102));
				var v_int_real_2: (int, real) := (3, -27.17);
				var v_bool_int_real_2: (bool, int, real) := (true, 23, -26.37);
				var v_int_real_bool_int_real_bool_2: ((int, real), (bool, int, real), bool) := (v_int_real_2, v_bool_int_real_2, false);
				var v_int_real_3: (int, real) := (-8, -1.66);
				var v_bool_int_real_3: (bool, int, real) := (false, 28, 20.23);
				var v_int_real_bool_int_real_bool_3: ((int, real), (bool, int, real), bool) := (v_int_real_3, v_bool_int_real_3, false);
				var v_seq_119: seq<((int, real), (bool, int, real), bool)> := [v_int_real_bool_int_real_bool_2, v_int_real_bool_int_real_bool_3];
				var v_int_154: int := -14;
				var v_int_real_4: (int, real) := (26, 9.17);
				var v_bool_int_real_4: (bool, int, real) := (false, -9, -25.09);
				var v_int_real_bool_int_real_bool_4: ((int, real), (bool, int, real), bool) := (v_int_real_4, v_bool_int_real_4, false);
				var v_array_116: array<(int, int, real)> := new (int, int, real)[4];
				var v_int_int_real_1: (int, int, real) := (28, -23, 29.23);
				v_array_116[0] := v_int_int_real_1;
				var v_int_int_real_2: (int, int, real) := (1, -29, 6.13);
				v_array_116[1] := v_int_int_real_2;
				var v_int_int_real_3: (int, int, real) := (25, 20, -5.60);
				v_array_116[2] := v_int_int_real_3;
				var v_int_int_real_4: (int, int, real) := (9, 22, 21.13);
				v_array_116[3] := v_int_int_real_4;
				var v_array_117: array<(int, int, real)> := new (int, int, real)[4];
				var v_int_int_real_5: (int, int, real) := (23, -12, -28.20);
				v_array_117[0] := v_int_int_real_5;
				var v_int_int_real_6: (int, int, real) := (17, 7, -20.15);
				v_array_117[1] := v_int_int_real_6;
				var v_int_int_real_7: (int, int, real) := (6, 13, 20.69);
				v_array_117[2] := v_int_int_real_7;
				var v_int_int_real_8: (int, int, real) := (19, 9, -13.78);
				v_array_117[3] := v_int_int_real_8;
				var v_seq_120: seq<array<(int, int, real)>> := [v_array_116, v_array_117];
				var v_seq_123: seq<array<(int, int, real)>> := (if ((|v_seq_120| > 0)) then (v_seq_120[21..0]) else (v_seq_120));
				var v_seq_124: seq<array<(int, int, real)>> := v_seq_123;
				var v_seq_121: seq<int> := [];
				var v_int_155: int := 15;
				var v_int_157: int := (if ((|v_seq_121| > 0)) then (v_seq_121[v_int_155]) else (27));
				var v_int_158: int := safe_index_seq(v_seq_124, v_int_157);
				var v_int_159: int := v_int_158;
				var v_int_int_real_9: (int, int, real) := (22, 28, -2.68);
				var v_int_int_real_10: (int, int, real) := (2, 2, 19.51);
				var v_int_int_real_11: (int, int, real) := (21, 2, -8.27);
				var v_int_int_real_12: (int, int, real) := (1, 23, 25.68);
				var v_int_int_real_13: (int, int, real) := (28, 12, -22.55);
				var v_array_118: array<(int, int, real)> := new (int, int, real)[5] [v_int_int_real_9, v_int_int_real_10, v_int_int_real_11, v_int_int_real_12, v_int_int_real_13];
				var v_int_int_real_14: (int, int, real) := (2, 23, -0.26);
				var v_int_int_real_15: (int, int, real) := (18, -12, -17.99);
				var v_int_int_real_16: (int, int, real) := (0, 17, -8.21);
				var v_array_119: array<(int, int, real)> := new (int, int, real)[3] [v_int_int_real_14, v_int_int_real_15, v_int_int_real_16];
				var v_seq_122: seq<array<(int, int, real)>> := [v_array_118, v_array_119];
				var v_int_156: int := 26;
				var v_int_int_real_17: (int, int, real) := (8, -28, 28.80);
				var v_int_int_real_18: (int, int, real) := (18, 12, 25.68);
				var v_int_int_real_19: (int, int, real) := (3, 25, 14.64);
				var v_int_int_real_20: (int, int, real) := (-18, 16, 26.64);
				var v_array_120: array<(int, int, real)> := new (int, int, real)[4] [v_int_int_real_17, v_int_int_real_18, v_int_int_real_19, v_int_int_real_20];
				var v_seq_125: seq<array<(int, int, real)>> := (if ((|v_seq_123| > 0)) then (v_seq_123[v_int_159 := (if ((|v_seq_122| > 0)) then (v_seq_122[v_int_156]) else (v_array_120))]) else (v_seq_123));
				var v_int_160: int := v_int_int_real_13.0;
				var v_int_int_real_21: (int, int, real) := (-19, 13, 16.02);
				var v_int_int_real_22: (int, int, real) := (25, 17, -9.09);
				var v_int_int_real_23: (int, int, real) := (3, 0, -14.78);
				var v_int_int_real_24: (int, int, real) := (29, 24, 18.08);
				var v_int_int_real_25: (int, int, real) := (24, 19, -16.52);
				var v_array_121: array<(int, int, real)> := new (int, int, real)[5] [v_int_int_real_21, v_int_int_real_22, v_int_int_real_23, v_int_int_real_24, v_int_int_real_25];
				var v_int_int_real_26: (int, int, real) := (2, 9, -20.50);
				var v_int_int_real_27: (int, int, real) := (28, -13, -22.59);
				var v_int_int_real_28: (int, int, real) := (14, -25, 22.38);
				var v_int_int_real_29: (int, int, real) := (22, 3, -2.17);
				var v_array_122: array<(int, int, real)> := new (int, int, real)[4] [v_int_int_real_26, v_int_int_real_27, v_int_int_real_28, v_int_int_real_29];
				var v_array_123: array<(int, int, real)> := new (int, int, real)[3];
				var v_int_int_real_30: (int, int, real) := (8, 21, -12.61);
				v_array_123[0] := v_int_int_real_30;
				var v_int_int_real_31: (int, int, real) := (11, 25, -10.46);
				v_array_123[1] := v_int_int_real_31;
				var v_int_int_real_32: (int, int, real) := (22, 13, 10.33);
				v_array_123[2] := v_int_int_real_32;
				var v_int_int_real_33: (int, int, real) := (24, 29, 11.99);
				var v_int_int_real_34: (int, int, real) := (13, 12, -2.90);
				var v_int_int_real_35: (int, int, real) := (12, 10, 9.15);
				var v_int_int_real_36: (int, int, real) := (18, 23, -10.14);
				var v_int_int_real_37: (int, int, real) := (18, 7, -23.31);
				var v_array_124: array<(int, int, real)> := new (int, int, real)[5] [v_int_int_real_33, v_int_int_real_34, v_int_int_real_35, v_int_int_real_36, v_int_int_real_37];
				var v_seq_126: seq<array<(int, int, real)>> := [v_array_121, v_array_122, v_array_123, v_array_124];
				var v_seq_127: seq<array<(int, int, real)>> := (if ((|v_seq_126| > 0)) then (v_seq_126[-4..25]) else (v_seq_126));
				var v_int_161: int := (match false {
					case _ => 12
				});
				var v_seq_128: seq<bool> := [true];
				var v_int_162: int := 23;
				var v_seq_129: seq<bool> := [];
				var v_int_163: int := 22;
				var v_bool_42: bool, v_int_real_bool_int_real_bool_5: ((int, real), (bool, int, real), bool), v_array_125: array<(int, int, real)>, v_bool_43: bool := (if (v_array_20[1]) then ((if ((if ((v_bool_36 in v_map_53)) then (v_map_53[v_bool_36]) else (false))) then ((if ((v_bool_37 in v_map_54)) then (v_map_54[v_bool_37]) else (true))) else ((if (true) then (false) else (true))))) else ((if (v_array_20[2]) then ((if ((v_bool_38 in v_map_55)) then (v_map_55[v_bool_38]) else (true))) else ((if ((v_bool_39 in v_map_56)) then (v_map_56[v_bool_39]) else (true)))))), (if ((|v_seq_118| > 0)) then (v_seq_118[v_int_153]) else ((if (v_array_18[2]) then (v_int_real_bool_int_real_bool_1) else ((if ((|v_seq_119| > 0)) then (v_seq_119[v_int_154]) else (v_int_real_bool_int_real_bool_4)))))), (if ((|v_seq_125| > 0)) then (v_seq_125[v_int_160]) else ((if ((|v_seq_127| > 0)) then (v_seq_127[v_int_161]) else (v_array_123)))), (if (v_array_10[2]) then ((match true {
					case _ => (match true {
						case _ => false
					})
				})) else ((if ((false !in {true, false, false, false})) then (([false, false] < [false])) else (v_array_1[2]))));
				var v_seq_130: seq<bool> := [];
				var v_seq_131: seq<bool> := [];
				var v_int_164: int := 11;
				match (if (((false <== false) !in (if ((|v_seq_130| > 0)) then (v_seq_130[14..15]) else (v_seq_130)))) then ((match false {
					case _ => (if ((|v_seq_131| > 0)) then (v_seq_131[v_int_164]) else (false))
				})) else ((match false {
					case _ => (-20 == 24)
				}))) {
					case _ => {
						return ;
					}
					
				}
				
				var v_int_165: int := (match true {
					case _ => v_int_real_real_10.0
				});
				var v_map_59: map<bool, bool> := map[false := true, true := false, true := true, false := false][false := true];
				var v_seq_132: seq<bool> := [false, false, false];
				var v_int_167: int := 29;
				var v_bool_44: bool := (if ((|v_seq_132| > 0)) then (v_seq_132[v_int_167]) else (true));
				var v_seq_133: seq<int> := [25, 0, 7, 11];
				var v_seq_134: seq<int> := v_seq_133;
				var v_int_168: int := 15;
				var v_int_169: int := safe_index_seq(v_seq_134, v_int_168);
				var v_int_170: int := v_int_169;
				var v_seq_135: seq<int> := (if ((|v_seq_133| > 0)) then (v_seq_133[v_int_170 := 9]) else (v_seq_133));
				var v_int_171: int := (match false {
					case _ => -28
				});
				var v_int_166: int := (if ((if ((v_bool_44 in v_map_59)) then (v_map_59[v_bool_44]) else ((true ==> true)))) then ((if ((|v_seq_135| > 0)) then (v_seq_135[v_int_171]) else ((match false {
					case _ => 11
				})))) else (v_int_55));
				while (v_int_165 < v_int_166) 
					decreases v_int_166 - v_int_165;
					invariant (v_int_165 <= v_int_166);
				{
					v_int_165 := (v_int_165 + 1);
					return ;
				}
				return ;
			}
		}
		var v_map_60: map<bool, bool> := (if (false) then (map[true := true, false := true]) else (map[true := true, false := true]));
		var v_bool_45: bool := (if (false) then (false) else (false));
		var v_seq_136: seq<map<bool, bool>> := [map[false := true, false := false, true := false, true := true, true := false], map[false := false, true := false, true := true, false := true], map[false := true, true := true], map[false := false, false := false, false := false]];
		var v_int_172: int := -2;
		var v_map_61: map<bool, bool> := (if ((|v_seq_136| > 0)) then (v_seq_136[v_int_172]) else (map[false := true]));
		var v_bool_46: bool := (if (true) then (false) else (true));
		var v_seq_137: seq<bool> := [true];
		var v_seq_138: seq<bool> := (if ((|v_seq_137| > 0)) then (v_seq_137[5..12]) else (v_seq_137));
		var v_seq_139: seq<bool> := v_seq_138;
		var v_int_173: int := (-27.68).Floor;
		var v_int_174: int := safe_index_seq(v_seq_139, v_int_173);
		var v_int_175: int := v_int_174;
		var v_seq_140: seq<bool> := (if ((|v_seq_138| > 0)) then (v_seq_138[v_int_175 := v_array_7[0]]) else (v_seq_138));
		var v_int_176: int := v_int_37;
		var v_map_62: map<bool, bool> := v_map_14;
		var v_bool_47: bool := (match true {
			case _ => true
		});
		var v_seq_141: seq<bool> := [false];
		var v_int_177: int := 29;
		v_array_17[0], v_array_15[3] := (match false {
			case _ => (if ((v_bool_46 in v_map_61)) then (v_map_61[v_bool_46]) else ((if (true) then (true) else (true))))
		}), (if ((|v_seq_140| > 0)) then (v_seq_140[v_int_176]) else ((if ((v_bool_47 in v_map_62)) then (v_map_62[v_bool_47]) else ((if ((|v_seq_141| > 0)) then (v_seq_141[v_int_177]) else (false))))));
		var v_map_63: map<bool, int> := map[false := 3, true := 23][false := -7];
		var v_bool_48: bool := (true !in {false});
		var v_seq_142: seq<int> := v_seq_18;
		var v_array_126: array<bool> := new bool[4] [true, true, false, true];
		var v_int_180: int := v_array_126.Length;
		var v_map_64: map<bool, int> := map[false := 22, false := 13, false := -9, false := -1, false := 8];
		var v_bool_49: bool := false;
		var v_int_178: int := ((if ((v_bool_48 in v_map_63)) then (v_map_63[v_bool_48]) else ((match true {
			case _ => 10
		}))) % (if ((|v_seq_142| > 0)) then (v_seq_142[v_int_180]) else ((if ((v_bool_49 in v_map_64)) then (v_map_64[v_bool_49]) else (23)))));
		var v_map_65: map<bool, int> := map[false := 8, false := 11, true := 23];
		var v_bool_50: bool := false;
		var v_map_66: map<multiset<multiset<int>>, int> := map[multiset{} := 12, multiset({multiset({22, 25, 11}), multiset{19, 17, 2}, multiset{21, -5, 21}, multiset{}}) := 22, multiset{} := 0, multiset({}) := 16, multiset({multiset{17, 26}, multiset{10}, multiset{1, 17, 22, 3}, multiset{17}}) := 15];
		var v_multiset_8: multiset<multiset<int>> := multiset{multiset{27, 18, 6}, multiset{16, 2}, multiset{20, 2, 6, 23}, multiset({2, 3, 14, 1})};
		var v_seq_143: seq<int> := [];
		var v_int_181: int := 3;
		var v_DT_2_1_4: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_1: (map<bool, real>, DT_2<(bool, real)>) := (map[true := 16.76, false := 16.37], v_DT_2_1_4);
		var v_DT_2_1_5: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_2: (map<bool, real>, DT_2<(bool, real)>) := (map[false := -29.87, true := -19.45], v_DT_2_1_5);
		var v_map_67: map<(map<bool, real>, DT_2<(bool, real)>), int> := map[v_map_DT_2_1_1 := 2][v_map_DT_2_1_2 := 21];
		var v_DT_2_1_6: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_3: (map<bool, real>, DT_2<(bool, real)>) := (map[false := -19.62, true := 19.86, false := -15.20], v_DT_2_1_6);
		var v_DT_2_1_7: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_4: (map<bool, real>, DT_2<(bool, real)>) := (map[true := -6.36, true := 7.59, false := 14.88], v_DT_2_1_7);
		var v_DT_2_1_8: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_5: (map<bool, real>, DT_2<(bool, real)>) := (map[true := -1.23, true := -29.06, false := -3.22, true := 18.38, false := -25.14], v_DT_2_1_8);
		var v_seq_144: seq<(map<bool, real>, DT_2<(bool, real)>)> := [v_map_DT_2_1_3, v_map_DT_2_1_4, v_map_DT_2_1_5];
		var v_int_182: int := 18;
		var v_DT_2_1_9: DT_2<(bool, real)> := DT_2_1;
		var v_map_DT_2_1_6: (map<bool, real>, DT_2<(bool, real)>) := (map[true := 23.42, true := 6.60, true := 23.89, false := -22.48, true := 10.38], v_DT_2_1_9);
		var v_map_DT_2_1_7: (map<bool, real>, DT_2<(bool, real)>) := (if ((|v_seq_144| > 0)) then (v_seq_144[v_int_182]) else (v_map_DT_2_1_6));
		var v_seq_145: seq<int> := [23, 7, 22];
		var v_int_183: int := 11;
		var v_seq_146: seq<int> := [18, -19, 12];
		var v_seq_147: seq<int> := (if ((|v_seq_146| > 0)) then (v_seq_146[19..-7]) else (v_seq_146));
		var v_int_184: int := (-13 / 0);
		var v_int_179: int := (match false {
			case _ => (if ((|v_seq_147| > 0)) then (v_seq_147[v_int_184]) else ((if (false) then (-19) else (16))))
		});
		while (v_int_178 < v_int_179) 
			decreases v_int_179 - v_int_178;
			invariant (v_int_178 <= v_int_179);
		{
			v_int_178 := (v_int_178 + 1);
			continue;
		}
		assert true;
		expect true;
		return ;
	}
	return ;
}
