// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_3(DT_1_3_1: T_1, DT_1_3_2: T_2, DT_1_3_3: T_1) | DT_1_4(DT_1_4_1: T_1, DT_1_4_2: T_2, DT_1_4_3: int, DT_1_4_4: T_2)
datatype DT_2 = DT_2_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: int, p_m_method_7_2: int) returns (ret_1: (seq<bool>, int))
	requires ((p_m_method_7_2 == 10) && (p_m_method_7_1 == 4));
	ensures (((p_m_method_7_2 == 10) && (p_m_method_7_1 == 4)) ==> (|(ret_1).0| == 3 && ((ret_1).0[0] == true) && ((ret_1).0[1] == true) && ((ret_1).0[2] == true) && ((ret_1).1 == 21)));
{
	var v_seq_int_1: (seq<bool>, int) := ([true, true, true], 21);
	print "v_seq_int_1.1", " ", v_seq_int_1.1, " ", "v_seq_int_1.0", " ", v_seq_int_1.0, " ", "p_m_method_7_2", " ", p_m_method_7_2, " ", "p_m_method_7_1", " ", p_m_method_7_1, " ", "v_seq_int_1", " ", v_seq_int_1, "\n";
	return v_seq_int_1;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: real, p_m_method_6_2: char, p_m_method_6_3: (bool, real)) returns (ret_1: seq<char>)
	requires (((p_m_method_6_3).0 == true) && (-12.54 < (p_m_method_6_3).1 < -12.34) && (p_m_method_6_2 == 'n') && (-23.67 < p_m_method_6_1 < -23.47));
	ensures ((((p_m_method_6_3).0 == true) && (-12.54 < (p_m_method_6_3).1 < -12.34) && (p_m_method_6_2 == 'n') && (-23.67 < p_m_method_6_1 < -23.47)) ==> (|ret_1| == 3 && (ret_1[0] == 'u') && (ret_1[1] == 'S') && (ret_1[2] == 'p')));
{
	assert ((p_m_method_6_1 == -23.57) && (p_m_method_6_3.1 == -12.44));
	expect ((p_m_method_6_1 == -23.57) && (p_m_method_6_3.1 == -12.44));
	var v_bool_int_1: (bool, int) := (false, 22);
	var v_bool_5: bool, v_bool_int_2: (bool, int), v_bool_6: bool, v_int_25: int := false, v_bool_int_1, false, 13;
	var v_int_26: int := 0;
	var v_int_27: int := 21;
	while (v_int_26 < v_int_27) 
		decreases v_int_27 - v_int_26;
		invariant (v_int_26 <= v_int_27);
	{
		v_int_26 := (v_int_26 + 1);
	}
	var v_int_28: int, v_int_29: int := 25, 28;
	assert ((v_bool_int_1.0 == false) && (p_m_method_6_1 == -23.57) && (v_int_28 == 25) && (v_bool_5 == false) && (v_bool_6 == false));
	expect ((v_bool_int_1.0 == false) && (p_m_method_6_1 == -23.57) && (v_int_28 == 25) && (v_bool_5 == false) && (v_bool_6 == false));
	var v_bool_real_3: (bool, real) := (true, -12.44);
	print "p_m_method_6_3.1", " ", (p_m_method_6_3.1 == -12.44), " ", "v_bool_int_1.1", " ", v_bool_int_1.1, " ", "v_bool_int_1.0", " ", v_bool_int_1.0, " ", "v_int_29", " ", v_int_29, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_6", " ", v_bool_6, " ", "v_bool_int_1", " ", v_bool_int_1, " ", "v_bool_int_2", " ", v_bool_int_2, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "p_m_method_6_3", " ", (p_m_method_6_3 == v_bool_real_3), " ", "p_m_method_6_2", " ", (p_m_method_6_2 == 'n'), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == -23.57), " ", "p_m_method_6_3.0", " ", p_m_method_6_3.0, "\n";
	return ['u', 'S', 'p'];
}

method m_method_5(p_m_method_5_1: (int, int), p_m_method_5_2: char, p_m_method_5_3: bool, p_m_method_5_4: char) returns (ret_1: DT_1<(real, int, bool), int>)
	requires ((p_m_method_5_4 == 'I') && ((p_m_method_5_1).0 == 17) && ((p_m_method_5_1).1 == 18) && (p_m_method_5_3 == false) && (p_m_method_5_2 == 'I'));
	ensures (((p_m_method_5_4 == 'I') && ((p_m_method_5_1).0 == 17) && ((p_m_method_5_1).1 == 18) && (p_m_method_5_3 == false) && (p_m_method_5_2 == 'I')) ==> ((ret_1.DT_1_4? && ((-13.82 < (ret_1.DT_1_4_1).0 < -13.62) && ((ret_1.DT_1_4_1).1 == 0) && ((ret_1.DT_1_4_1).2 == false) && (ret_1.DT_1_4_2 == 22) && (ret_1.DT_1_4_3 == 18) && (ret_1.DT_1_4_4 == 11)))));
{
	var v_real_1: real := -23.57;
	var v_char_6: char := 'n';
	var v_bool_real_1: (bool, real) := (true, -12.44);
	var v_bool_real_2: (bool, real) := v_bool_real_1;
	var v_seq_14: seq<char> := m_method_6(v_real_1, v_char_6, v_bool_real_2);
	var v_DT_1_3_1: DT_1<real, real> := DT_1_3(7.77, 15.04, 22.01);
	var v_DT_1_3_2: DT_1<real, real> := DT_1_3(-21.49, -10.57, 22.26);
	var v_DT_1_3_3: DT_1<real, real> := DT_1_3(-14.38, 7.25, -24.92);
	var v_array_1: array<DT_1<real, real>> := new DT_1<real, real>[3] [v_DT_1_3_1, v_DT_1_3_2, v_DT_1_3_3];
	var v_DT_1_3_4: DT_1<real, real> := DT_1_3(29.94, -21.10, -18.08);
	var v_DT_1_3_5: DT_1<real, real> := DT_1_3(27.87, -9.20, 10.32);
	var v_DT_1_3_6: DT_1<real, real> := DT_1_3(-16.31, -26.54, 27.20);
	var v_array_2: array<DT_1<real, real>> := new DT_1<real, real>[3] [v_DT_1_3_4, v_DT_1_3_5, v_DT_1_3_6];
	var v_int_30: int := 4;
	var v_int_31: int := 10;
	var v_seq_int_2: (seq<bool>, int) := m_method_7(v_int_30, v_int_31);
	var v_seq_15: seq<char>, v_array_3: array<DT_1<real, real>>, v_seq_int_3: (seq<bool>, int), v_bool_7: bool, v_set_1: set<char> := v_seq_14, (match 20 {
		case 19 => v_array_1
		case _ => v_array_2
	}), v_seq_int_2, p_m_method_5_3, ({'g'} + {});
	if (23 !in map[0 := 1, 4 := 9]) {
		var v_int_42: int, v_int_43: int := v_int_31, p_m_method_5_1.0;
		for v_int_32 := v_int_42 to v_int_43 
			invariant (v_int_43 - v_int_32 >= 0) && ((((v_int_32 == 10)) ==> ((((v_int_31 == 10))))))
		{
			var v_seq_16: seq<int> := [-22];
			var v_int_33: int := 18;
			var v_seq_38: seq<int> := v_seq_16;
			var v_int_81: int := v_int_33;
			var v_int_82: int := safe_index_seq(v_seq_38, v_int_81);
			v_int_33 := v_int_82;
			v_int_31 := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_33]) else (18));
			var v_map_6: map<int, int> := map[16 := 22, 26 := 25, 13 := 22, 1 := -1, 25 := 20];
			var v_int_35: int := 12;
			var v_int_36: int := 18;
			var v_int_37: int := 20;
			var v_int_38: int := safe_division(v_int_36, v_int_37);
			var v_int_40: int, v_int_41: int := (if ((v_int_35 in v_map_6)) then (v_map_6[v_int_35]) else (3)), v_int_38;
			for v_int_34 := v_int_40 downto v_int_41 
				invariant (v_int_34 - v_int_41 >= 0)
			{
				var v_seq_17: seq<DT_1<(real, int, bool), int>> := [];
				var v_int_39: int := 3;
				var v_real_int_bool_27: (real, int, bool) := (-13.72, 0, false);
				var v_DT_1_4_29: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_27, 22, 18, 11);
				var v_real_int_bool_64: (real, int, bool) := (-13.72, 0, false);
				var v_real_int_bool_65: (real, int, bool) := (-13.72, 0, false);
				var v_DT_1_4_53: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_65, 22, 18, 11);
				var v_real_int_bool_66: (real, int, bool) := (-13.72, 0, false);
				var v_bool_real_4: (bool, real) := (true, -12.44);
				var v_bool_real_5: (bool, real) := (true, -12.44);
				print "v_int_34", " ", v_int_34, " ", "v_real_int_bool_27", " ", (v_real_int_bool_27 == v_real_int_bool_64), " ", "v_seq_17", " ", (v_seq_17 == []), " ", "v_int_39", " ", v_int_39, " ", "v_real_int_bool_27.1", " ", v_real_int_bool_27.1, " ", "v_real_int_bool_27.0", " ", (v_real_int_bool_27.0 == -13.72), " ", "v_DT_1_4_29", " ", (v_DT_1_4_29 == v_DT_1_4_53), " ", "v_real_int_bool_27.2", " ", v_real_int_bool_27.2, " ", "v_DT_1_4_29.DT_1_4_4", " ", v_DT_1_4_29.DT_1_4_4, " ", "v_DT_1_4_29.DT_1_4_3", " ", v_DT_1_4_29.DT_1_4_3, " ", "v_DT_1_4_29.DT_1_4_2", " ", v_DT_1_4_29.DT_1_4_2, " ", "v_DT_1_4_29.DT_1_4_1", " ", (v_DT_1_4_29.DT_1_4_1 == v_real_int_bool_66), " ", "v_int_35", " ", v_int_35, " ", "v_seq_16", " ", v_seq_16, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_map_6", " ", (v_map_6 == map[16 := 22, 1 := -1, 25 := 20, 26 := 25, 13 := 22]), " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_int_31", " ", v_int_31, " ", "v_char_6", " ", (v_char_6 == 'n'), " ", "v_bool_real_1", " ", (v_bool_real_1 == v_bool_real_4), " ", "v_bool_real_2", " ", (v_bool_real_2 == v_bool_real_5), " ", "v_seq_int_3", " ", v_seq_int_3, " ", "p_m_method_5_1.0", " ", p_m_method_5_1.0, " ", "v_seq_int_2", " ", v_seq_int_2, " ", "v_bool_7", " ", v_bool_7, " ", "p_m_method_5_1.1", " ", p_m_method_5_1.1, " ", "v_seq_14", " ", (v_seq_14 == ['u', 'S', 'p']), " ", "v_array_3", " ", "v_seq_15", " ", (v_seq_15 == ['u', 'S', 'p']), " ", "v_set_1", " ", (v_set_1 == {'g'}), " ", "v_bool_real_1.1", " ", (v_bool_real_1.1 == -12.44), " ", "v_bool_real_1.0", " ", v_bool_real_1.0, " ", "p_m_method_5_4", " ", (p_m_method_5_4 == 'I'), " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "v_real_1", " ", (v_real_1 == -23.57), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, " ", "p_m_method_5_2", " ", (p_m_method_5_2 == 'I'), " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
				return (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_39]) else (v_DT_1_4_29));
			}
		}
		var v_real_int_bool_28: (real, int, bool) := (-24.98, 8, true);
		var v_DT_1_4_30: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_28, 23, 11, -28);
		var v_real_int_bool_29: (real, int, bool) := (25.01, 28, false);
		var v_DT_1_4_31: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_29, 18, 28, 28);
		var v_real_int_bool_30: (real, int, bool) := (-10.20, 19, false);
		var v_DT_1_4_32: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_30, 0, 15, 15);
		return (match -8.37 {
			case _ => v_DT_1_4_32
		});
	} else {
		if (if (false) then (false) else (false)) {
			
		}
		var v_int_44: int := v_int_31;
		var v_int_46: int := 27;
		var v_int_47: int := 28;
		var v_int_48: int := safe_division(v_int_46, v_int_47);
		var v_int_45: int := v_int_48;
		while (v_int_44 < v_int_45) 
			decreases v_int_45 - v_int_44;
			invariant (v_int_44 <= v_int_45);
		{
			v_int_44 := (v_int_44 + 1);
			if (multiset{-17} !! multiset{29, 20}) {
				
			}
			continue;
		}
		var v_map_7: map<int, int> := map[29 := 19, 28 := 6, 15 := 15];
		var v_int_49: int := 29;
		var v_seq_18: seq<int> := [1, 17, 12];
		var v_int_50: int := -11;
		v_int_47, v_int_30, v_int_31, v_int_48 := (if ((v_int_49 in v_map_7)) then (v_map_7[v_int_49]) else (21)), (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_50]) else (7)), (if (true) then (10) else (27)), (16 - 17);
		if (true <==> false) {
			
		}
		var v_real_int_bool_31: (real, int, bool) := (7.36, 21, false);
		var v_DT_1_4_33: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_31, 0, 7, -6);
		var v_real_int_bool_32: (real, int, bool) := (20.15, 19, true);
		var v_DT_1_4_34: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_32, 3, 8, 8);
		var v_real_int_bool_33: (real, int, bool) := (-10.45, 6, false);
		var v_DT_1_4_35: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_33, 15, 1, -15);
		var v_seq_19: seq<DT_1<(real, int, bool), int>> := [v_DT_1_4_33, v_DT_1_4_34, v_DT_1_4_35];
		var v_int_51: int := 27;
		var v_real_int_bool_34: (real, int, bool) := (-14.14, 13, false);
		var v_DT_1_4_36: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_34, 3, 16, 9);
		return (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_51]) else (v_DT_1_4_36));
	}
}

method m_method_4(p_m_method_4_1: (bool, int, real), p_m_method_4_2: char, p_m_method_4_3: char) returns (ret_1: seq<DT_1<(real, int, bool), int>>)
	requires ((p_m_method_4_2 == 'A') && ((p_m_method_4_1).0 == true) && ((p_m_method_4_1).1 == 4) && (-26.19 < (p_m_method_4_1).2 < -25.99) && (p_m_method_4_3 == 'r'));
	ensures (((p_m_method_4_2 == 'A') && ((p_m_method_4_1).0 == true) && ((p_m_method_4_1).1 == 4) && (-26.19 < (p_m_method_4_1).2 < -25.99) && (p_m_method_4_3 == 'r')) ==> (|ret_1| == 4 && (ret_1[0].DT_1_4? && ((-26.93 < (ret_1[0].DT_1_4_1).0 < -26.73) && ((ret_1[0].DT_1_4_1).1 == 20) && ((ret_1[0].DT_1_4_1).2 == true) && (ret_1[0].DT_1_4_2 == 14) && (ret_1[0].DT_1_4_3 == 24) && (ret_1[0].DT_1_4_4 == 20))) && (ret_1[1].DT_1_4? && ((-30.00 < (ret_1[1].DT_1_4_1).0 < -29.80) && ((ret_1[1].DT_1_4_1).1 == 14) && ((ret_1[1].DT_1_4_1).2 == true) && (ret_1[1].DT_1_4_2 == 22) && (ret_1[1].DT_1_4_3 == -29) && (ret_1[1].DT_1_4_4 == 13))) && (ret_1[2].DT_1_4? && ((-10.96 < (ret_1[2].DT_1_4_1).0 < -10.76) && ((ret_1[2].DT_1_4_1).1 == -13) && ((ret_1[2].DT_1_4_1).2 == true) && (ret_1[2].DT_1_4_2 == -9) && (ret_1[2].DT_1_4_3 == 27) && (ret_1[2].DT_1_4_4 == -10))) && (ret_1[3].DT_1_4? && ((-4.27 < (ret_1[3].DT_1_4_1).0 < -4.07) && ((ret_1[3].DT_1_4_1).1 == 20) && ((ret_1[3].DT_1_4_1).2 == false) && (ret_1[3].DT_1_4_2 == 10) && (ret_1[3].DT_1_4_3 == 4) && (ret_1[3].DT_1_4_4 == 1)))));
{
	var v_real_int_bool_14: (real, int, bool) := (-26.83, 20, true);
	var v_DT_1_4_16: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_14, 14, 24, 20);
	var v_real_int_bool_15: (real, int, bool) := (-29.90, 14, true);
	var v_DT_1_4_17: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_15, 22, -29, 13);
	var v_real_int_bool_16: (real, int, bool) := (-10.86, -13, true);
	var v_DT_1_4_18: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_16, -9, 27, -10);
	var v_real_int_bool_17: (real, int, bool) := (-4.17, 20, false);
	var v_DT_1_4_19: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_17, 10, 4, 1);
	var v_real_int_bool_37: (real, int, bool) := (-4.17, 20, false);
	var v_real_int_bool_38: (real, int, bool) := (-10.86, -13, true);
	var v_real_int_bool_39: (real, int, bool) := (-29.90, 14, true);
	var v_real_int_bool_40: (real, int, bool) := (-26.83, 20, true);
	var v_real_int_bool_41: (real, int, bool) := (-4.17, 20, false);
	var v_bool_int_real_3: (bool, int, real) := (true, 4, -26.09);
	var v_real_int_bool_42: (real, int, bool) := (-26.83, 20, true);
	var v_real_int_bool_43: (real, int, bool) := (-29.90, 14, true);
	var v_real_int_bool_44: (real, int, bool) := (-10.86, -13, true);
	var v_real_int_bool_45: (real, int, bool) := (-26.83, 20, true);
	var v_DT_1_4_40: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_45, 14, 24, 20);
	var v_real_int_bool_46: (real, int, bool) := (-29.90, 14, true);
	var v_DT_1_4_41: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_46, 22, -29, 13);
	var v_real_int_bool_47: (real, int, bool) := (-10.86, -13, true);
	var v_DT_1_4_42: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_47, -9, 27, -10);
	var v_real_int_bool_48: (real, int, bool) := (-4.17, 20, false);
	var v_DT_1_4_43: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_48, 10, 4, 1);
	print "v_real_int_bool_17", " ", (v_real_int_bool_17 == v_real_int_bool_37), " ", "v_real_int_bool_16", " ", (v_real_int_bool_16 == v_real_int_bool_38), " ", "v_real_int_bool_15", " ", (v_real_int_bool_15 == v_real_int_bool_39), " ", "v_real_int_bool_14", " ", (v_real_int_bool_14 == v_real_int_bool_40), " ", "v_DT_1_4_16.DT_1_4_4", " ", v_DT_1_4_16.DT_1_4_4, " ", "v_DT_1_4_19.DT_1_4_3", " ", v_DT_1_4_19.DT_1_4_3, " ", "v_DT_1_4_19.DT_1_4_4", " ", v_DT_1_4_19.DT_1_4_4, " ", "v_DT_1_4_16.DT_1_4_2", " ", v_DT_1_4_16.DT_1_4_2, " ", "v_DT_1_4_19.DT_1_4_1", " ", (v_DT_1_4_19.DT_1_4_1 == v_real_int_bool_41), " ", "v_DT_1_4_16.DT_1_4_3", " ", v_DT_1_4_16.DT_1_4_3, " ", "v_DT_1_4_19.DT_1_4_2", " ", v_DT_1_4_19.DT_1_4_2, " ", "p_m_method_4_1", " ", (p_m_method_4_1 == v_bool_int_real_3), " ", "v_DT_1_4_16.DT_1_4_1", " ", (v_DT_1_4_16.DT_1_4_1 == v_real_int_bool_42), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'r'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'A'), " ", "v_DT_1_4_17.DT_1_4_4", " ", v_DT_1_4_17.DT_1_4_4, " ", "v_DT_1_4_17.DT_1_4_3", " ", v_DT_1_4_17.DT_1_4_3, " ", "v_DT_1_4_17.DT_1_4_2", " ", v_DT_1_4_17.DT_1_4_2, " ", "v_DT_1_4_17.DT_1_4_1", " ", (v_DT_1_4_17.DT_1_4_1 == v_real_int_bool_43), " ", "v_DT_1_4_18.DT_1_4_1", " ", (v_DT_1_4_18.DT_1_4_1 == v_real_int_bool_44), " ", "v_DT_1_4_18.DT_1_4_3", " ", v_DT_1_4_18.DT_1_4_3, " ", "v_DT_1_4_18.DT_1_4_2", " ", v_DT_1_4_18.DT_1_4_2, " ", "v_DT_1_4_18.DT_1_4_4", " ", v_DT_1_4_18.DT_1_4_4, " ", "p_m_method_4_1.1", " ", p_m_method_4_1.1, " ", "v_real_int_bool_14.2", " ", v_real_int_bool_14.2, " ", "v_DT_1_4_16", " ", (v_DT_1_4_16 == v_DT_1_4_40), " ", "v_real_int_bool_15.1", " ", v_real_int_bool_15.1, " ", "v_real_int_bool_16.0", " ", (v_real_int_bool_16.0 == -10.86), " ", "p_m_method_4_1.2", " ", (p_m_method_4_1.2 == -26.09), " ", "v_real_int_bool_15.2", " ", v_real_int_bool_15.2, " ", "v_DT_1_4_17", " ", (v_DT_1_4_17 == v_DT_1_4_41), " ", "v_real_int_bool_16.1", " ", v_real_int_bool_16.1, " ", "v_real_int_bool_17.0", " ", (v_real_int_bool_17.0 == -4.17), " ", "v_real_int_bool_16.2", " ", v_real_int_bool_16.2, " ", "v_DT_1_4_18", " ", (v_DT_1_4_18 == v_DT_1_4_42), " ", "v_real_int_bool_17.1", " ", v_real_int_bool_17.1, " ", "v_real_int_bool_17.2", " ", v_real_int_bool_17.2, " ", "v_DT_1_4_19", " ", (v_DT_1_4_19 == v_DT_1_4_43), " ", "v_real_int_bool_14.0", " ", (v_real_int_bool_14.0 == -26.83), " ", "p_m_method_4_1.0", " ", p_m_method_4_1.0, " ", "v_real_int_bool_14.1", " ", v_real_int_bool_14.1, " ", "v_real_int_bool_15.0", " ", (v_real_int_bool_15.0 == -29.90), "\n";
	return [v_DT_1_4_16, v_DT_1_4_17, v_DT_1_4_18, v_DT_1_4_19];
}

method m_method_3(p_m_method_3_1: (bool, real, bool), p_m_method_3_2: char) returns (ret_1: char)
	requires (((p_m_method_3_1).0 == true) && (9.91 < (p_m_method_3_1).1 < 10.11) && ((p_m_method_3_1).2 == false) && (p_m_method_3_2 == 'G'));
	ensures ((((p_m_method_3_1).0 == true) && (9.91 < (p_m_method_3_1).1 < 10.11) && ((p_m_method_3_1).2 == false) && (p_m_method_3_2 == 'G')) ==> ((ret_1 == 'I')));
{
	var v_bool_real_bool_5: (bool, real, bool) := (true, 10.01, false);
	print "p_m_method_3_1.2", " ", p_m_method_3_1.2, " ", "p_m_method_3_1.0", " ", p_m_method_3_1.0, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'G'), " ", "p_m_method_3_1.1", " ", (p_m_method_3_1.1 == 10.01), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == v_bool_real_bool_5), "\n";
	return 'I';
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: int, p_m_method_2_3: int) returns (ret_1: seq<DT_1<(real, int, bool), int>>)
	requires ((p_m_method_2_2 == 4) && (p_m_method_2_1 == -6) && (p_m_method_2_3 == 0));
	ensures (((p_m_method_2_2 == 4) && (p_m_method_2_1 == -6) && (p_m_method_2_3 == 0)) ==> (|ret_1| == 4 && (ret_1[0].DT_1_4? && ((-26.93 < (ret_1[0].DT_1_4_1).0 < -26.73) && ((ret_1[0].DT_1_4_1).1 == 20) && ((ret_1[0].DT_1_4_1).2 == true) && (ret_1[0].DT_1_4_2 == 14) && (ret_1[0].DT_1_4_3 == 24) && (ret_1[0].DT_1_4_4 == 20))) && (ret_1[1].DT_1_4? && ((-30.00 < (ret_1[1].DT_1_4_1).0 < -29.80) && ((ret_1[1].DT_1_4_1).1 == 14) && ((ret_1[1].DT_1_4_1).2 == true) && (ret_1[1].DT_1_4_2 == 22) && (ret_1[1].DT_1_4_3 == -29) && (ret_1[1].DT_1_4_4 == 13))) && (ret_1[2].DT_1_4? && ((-10.96 < (ret_1[2].DT_1_4_1).0 < -10.76) && ((ret_1[2].DT_1_4_1).1 == -13) && ((ret_1[2].DT_1_4_1).2 == true) && (ret_1[2].DT_1_4_2 == -9) && (ret_1[2].DT_1_4_3 == 27) && (ret_1[2].DT_1_4_4 == -10))) && (ret_1[3].DT_1_4? && ((-4.27 < (ret_1[3].DT_1_4_1).0 < -4.07) && ((ret_1[3].DT_1_4_1).1 == 20) && ((ret_1[3].DT_1_4_1).2 == false) && (ret_1[3].DT_1_4_2 == 10) && (ret_1[3].DT_1_4_3 == 4) && (ret_1[3].DT_1_4_4 == 1)))));
{
	assert ((p_m_method_2_3 == 0) && (p_m_method_2_2 == 4));
	expect ((p_m_method_2_3 == 0) && (p_m_method_2_2 == 4));
	if (true <==> true) {
		var v_real_int_bool_4: (real, int, bool) := (26.65, -28, false);
		var v_DT_1_4_6: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_4, 6, 20, 4);
		var v_real_int_bool_5: (real, int, bool) := (20.93, 12, true);
		var v_DT_1_4_7: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_5, -11, 11, 19);
		var v_map_2: map<int, DT_1<(real, int, bool), int>> := map[9 := v_DT_1_4_6, 29 := v_DT_1_4_7];
		var v_int_10: int := 21;
		var v_real_int_bool_6: (real, int, bool) := (-11.77, 16, false);
		var v_DT_1_4_8: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_6, 22, 2, 16);
		v_DT_1_4_6 := (if ((v_int_10 in v_map_2)) then (v_map_2[v_int_10]) else (v_DT_1_4_8));
		if v_real_int_bool_4.2 {
			var v_bool_real_bool_1: (bool, real, bool) := (false, -22.61, false);
			var v_bool_real_bool_2: (bool, real, bool) := v_bool_real_bool_1;
			var v_char_1: char := 'N';
			var v_char_2: char := m_method_3(v_bool_real_bool_2, v_char_1);
			var v_int_11: int := 25;
			var v_int_12: int := 16;
			var v_int_13: int := safe_division(v_int_11, v_int_12);
			var v_char_3: char, v_bool_4: bool, v_int_14: int, v_multiset_1: multiset<char> := v_char_2, (match true {
				case _ => true
			}), v_int_13, (multiset{'L'} - multiset({}));
			var v_real_int_bool_7: (real, int, bool) := (-10.49, 9, true);
			var v_DT_1_4_9: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_7, 17, 2, 14);
			var v_real_int_bool_8: (real, int, bool) := (-9.96, 14, false);
			var v_DT_1_4_10: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_8, 17, 3, 22);
			var v_real_int_bool_9: (real, int, bool) := (-22.30, 8, false);
			var v_DT_1_4_11: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_9, 7, -9, 8);
			var v_real_int_bool_10: (real, int, bool) := (3.65, 17, false);
			var v_DT_1_4_12: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_10, 8, 15, 8);
			var v_map_3: map<seq<bool>, seq<DT_1<(real, int, bool), int>>> := map[[true, true, true, true] := [v_DT_1_4_9, v_DT_1_4_10, v_DT_1_4_11, v_DT_1_4_12]];
			var v_seq_7: seq<bool> := [true, true];
			var v_real_int_bool_11: (real, int, bool) := (13.47, 25, true);
			var v_DT_1_4_13: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_11, 24, 5, 12);
			var v_real_int_bool_12: (real, int, bool) := (-25.91, 0, true);
			var v_DT_1_4_14: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_12, 11, 26, 21);
			var v_real_int_bool_13: (real, int, bool) := (14.63, -23, true);
			var v_DT_1_4_15: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_13, 9, 8, 9);
			return (if ((v_seq_7 in v_map_3)) then (v_map_3[v_seq_7]) else ([v_DT_1_4_13, v_DT_1_4_14, v_DT_1_4_15]));
		} else {
			var v_map_4: map<int, bool> := map[23 := true, 15 := true, 26 := true, 6 := true];
			var v_int_15: int := -23;
			if (if ((v_int_15 in v_map_4)) then (v_map_4[v_int_15]) else (true)) {
				var v_bool_int_real_1: (bool, int, real) := (true, 4, -26.09);
				var v_bool_int_real_2: (bool, int, real) := v_bool_int_real_1;
				var v_char_4: char := 'A';
				var v_char_5: char := 'r';
				var v_seq_8: seq<DT_1<(real, int, bool), int>> := m_method_4(v_bool_int_real_2, v_char_4, v_char_5);
				var v_real_int_bool_49: (real, int, bool) := (-26.83, 20, true);
				var v_DT_1_4_44: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_49, 14, 24, 20);
				var v_real_int_bool_50: (real, int, bool) := (-29.90, 14, true);
				var v_DT_1_4_45: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_50, 22, -29, 13);
				var v_real_int_bool_51: (real, int, bool) := (-10.86, -13, true);
				var v_DT_1_4_46: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_51, -9, 27, -10);
				var v_real_int_bool_52: (real, int, bool) := (-4.17, 20, false);
				var v_DT_1_4_47: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_52, 10, 4, 1);
				var v_bool_int_real_4: (bool, int, real) := (true, 4, -26.09);
				var v_bool_int_real_5: (bool, int, real) := (true, 4, -26.09);
				var v_real_int_bool_53: (real, int, bool) := (-11.77, 16, false);
				var v_DT_1_4_48: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_53, 22, 2, 16);
				var v_real_int_bool_54: (real, int, bool) := (26.65, -28, false);
				var v_real_int_bool_55: (real, int, bool) := (-11.77, 16, false);
				var v_real_int_bool_56: (real, int, bool) := (20.93, 12, true);
				var v_real_int_bool_57: (real, int, bool) := (-11.77, 16, false);
				var v_DT_1_4_49: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_57, 22, 2, 16);
				var v_real_int_bool_58: (real, int, bool) := (20.93, 12, true);
				var v_DT_1_4_50: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_58, -11, 11, 19);
				var v_real_int_bool_59: (real, int, bool) := (-11.77, 16, false);
				var v_real_int_bool_60: (real, int, bool) := (-11.77, 16, false);
				var v_real_int_bool_61: (real, int, bool) := (26.65, -28, false);
				var v_DT_1_4_51: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_61, 6, 20, 4);
				var v_real_int_bool_62: (real, int, bool) := (20.93, 12, true);
				var v_DT_1_4_52: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_62, -11, 11, 19);
				var v_real_int_bool_63: (real, int, bool) := (20.93, 12, true);
				print "v_seq_8", " ", (v_seq_8 == [v_DT_1_4_44, v_DT_1_4_45, v_DT_1_4_46, v_DT_1_4_47]), " ", "v_bool_int_real_1.2", " ", (v_bool_int_real_1.2 == -26.09), " ", "v_char_5", " ", (v_char_5 == 'r'), " ", "v_char_4", " ", (v_char_4 == 'A'), " ", "v_bool_int_real_2", " ", (v_bool_int_real_2 == v_bool_int_real_4), " ", "v_bool_int_real_1", " ", (v_bool_int_real_1 == v_bool_int_real_5), " ", "v_bool_int_real_1.1", " ", v_bool_int_real_1.1, " ", "v_bool_int_real_1.0", " ", v_bool_int_real_1.0, " ", "v_map_4", " ", (v_map_4 == map[6 := true, 23 := true, 26 := true, 15 := true]), " ", "v_int_15", " ", v_int_15, " ", "v_DT_1_4_6", " ", (v_DT_1_4_6 == v_DT_1_4_48), " ", "v_real_int_bool_4", " ", (v_real_int_bool_4 == v_real_int_bool_54), " ", "v_DT_1_4_7.DT_1_4_2", " ", v_DT_1_4_7.DT_1_4_2, " ", "v_DT_1_4_7.DT_1_4_3", " ", v_DT_1_4_7.DT_1_4_3, " ", "v_DT_1_4_7.DT_1_4_4", " ", v_DT_1_4_7.DT_1_4_4, " ", "v_real_int_bool_6", " ", (v_real_int_bool_6 == v_real_int_bool_55), " ", "v_real_int_bool_5", " ", (v_real_int_bool_5 == v_real_int_bool_56), " ", "v_DT_1_4_8", " ", (v_DT_1_4_8 == v_DT_1_4_49), " ", "v_DT_1_4_7", " ", (v_DT_1_4_7 == v_DT_1_4_50), " ", "v_DT_1_4_8.DT_1_4_1", " ", (v_DT_1_4_8.DT_1_4_1 == v_real_int_bool_59), " ", "v_DT_1_4_8.DT_1_4_2", " ", v_DT_1_4_8.DT_1_4_2, " ", "v_DT_1_4_6.DT_1_4_4", " ", v_DT_1_4_6.DT_1_4_4, " ", "v_DT_1_4_6.DT_1_4_3", " ", v_DT_1_4_6.DT_1_4_3, " ", "v_DT_1_4_6.DT_1_4_2", " ", v_DT_1_4_6.DT_1_4_2, " ", "v_DT_1_4_6.DT_1_4_1", " ", (v_DT_1_4_6.DT_1_4_1 == v_real_int_bool_60), " ", "v_real_int_bool_6.2", " ", v_real_int_bool_6.2, " ", "v_real_int_bool_5.2", " ", v_real_int_bool_5.2, " ", "v_real_int_bool_6.1", " ", v_real_int_bool_6.1, " ", "v_real_int_bool_4.0", " ", (v_real_int_bool_4.0 == 26.65), " ", "v_real_int_bool_4.2", " ", v_real_int_bool_4.2, " ", "v_real_int_bool_5.1", " ", v_real_int_bool_5.1, " ", "v_real_int_bool_6.0", " ", (v_real_int_bool_6.0 == -11.77), " ", "v_real_int_bool_4.1", " ", v_real_int_bool_4.1, " ", "v_real_int_bool_5.0", " ", (v_real_int_bool_5.0 == 20.93), " ", "v_DT_1_4_8.DT_1_4_3", " ", v_DT_1_4_8.DT_1_4_3, " ", "v_DT_1_4_8.DT_1_4_4", " ", v_DT_1_4_8.DT_1_4_4, " ", "v_map_2", " ", (v_map_2 == map[9 := v_DT_1_4_51, 29 := v_DT_1_4_52]), " ", "v_int_10", " ", v_int_10, " ", "v_DT_1_4_7.DT_1_4_1", " ", (v_DT_1_4_7.DT_1_4_1 == v_real_int_bool_63), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, "\n";
				return v_seq_8;
			} else {
				var v_real_int_bool_18: (real, int, bool) := (19.16, 29, false);
				var v_DT_1_4_20: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_18, 27, 3, 3);
				var v_real_int_bool_19: (real, int, bool) := (-23.65, 18, true);
				var v_DT_1_4_21: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_19, 29, 22, 25);
				var v_real_int_bool_20: (real, int, bool) := (29.74, 25, false);
				var v_DT_1_4_22: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_20, -22, 19, 16);
				var v_real_int_bool_21: (real, int, bool) := (-16.41, 13, false);
				var v_DT_1_4_23: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_21, 20, 15, 25);
				return (match 23.68 {
					case _ => [v_DT_1_4_20, v_DT_1_4_21, v_DT_1_4_22, v_DT_1_4_23]
				});
			}
		}
	}
	var v_real_int_bool_22: (real, int, bool) := (3.12, 6, false);
	var v_DT_1_4_24: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_22, 0, 19, 29);
	var v_real_int_bool_23: (real, int, bool) := (7.97, 2, true);
	var v_DT_1_4_25: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_23, 5, 6, 28);
	var v_real_int_bool_24: (real, int, bool) := (-18.82, 3, false);
	var v_DT_1_4_26: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_24, 8, 23, 26);
	var v_real_int_bool_25: (real, int, bool) := (17.14, 18, false);
	var v_DT_1_4_27: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_25, 18, 0, 17);
	var v_seq_9: seq<DT_1<(real, int, bool), int>> := [v_DT_1_4_24, v_DT_1_4_25, v_DT_1_4_26, v_DT_1_4_27];
	var v_seq_10: seq<DT_1<(real, int, bool), int>> := v_seq_9;
	var v_int_16: int := 22;
	var v_int_17: int := safe_index_seq(v_seq_10, v_int_16);
	var v_int_18: int := v_int_17;
	var v_real_int_bool_26: (real, int, bool) := (10.92, -13, false);
	var v_DT_1_4_28: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_26, 10, 23, 22);
	return (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_18 := v_DT_1_4_28]) else (v_seq_9));
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: DT_1<(real, int, bool), int>, p_m_method_1_3: seq<int>) returns (ret_1: (char, (bool, bool, bool), bool))
	requires ((p_m_method_1_1 == false) && |p_m_method_1_3| == 0 && (p_m_method_1_2.DT_1_4? && ((24.13 < (p_m_method_1_2.DT_1_4_1).0 < 24.33) && ((p_m_method_1_2.DT_1_4_1).1 == 2) && ((p_m_method_1_2.DT_1_4_1).2 == true) && (p_m_method_1_2.DT_1_4_2 == 22) && (p_m_method_1_2.DT_1_4_3 == 4) && (p_m_method_1_2.DT_1_4_4 == 17)))) || ((p_m_method_1_1 == true) && |p_m_method_1_3| == 1 && (p_m_method_1_3[0] == 24) && (p_m_method_1_2.DT_1_4? && ((18.08 < (p_m_method_1_2.DT_1_4_1).0 < 18.28) && ((p_m_method_1_2.DT_1_4_1).1 == 22) && ((p_m_method_1_2.DT_1_4_1).2 == false) && (p_m_method_1_2.DT_1_4_2 == 23) && (p_m_method_1_2.DT_1_4_3 == 19) && (p_m_method_1_2.DT_1_4_4 == 19))));
	ensures (((p_m_method_1_1 == true) && |p_m_method_1_3| == 1 && (p_m_method_1_3[0] == 24) && (p_m_method_1_2.DT_1_4? && ((18.08 < (p_m_method_1_2.DT_1_4_1).0 < 18.28) && ((p_m_method_1_2.DT_1_4_1).1 == 22) && ((p_m_method_1_2.DT_1_4_1).2 == false) && (p_m_method_1_2.DT_1_4_2 == 23) && (p_m_method_1_2.DT_1_4_3 == 19) && (p_m_method_1_2.DT_1_4_4 == 19)))) ==> (((ret_1).0 == 'w') && (((ret_1).1).0 == false) && (((ret_1).1).1 == false) && (((ret_1).1).2 == false) && ((ret_1).2 == false))) && (((p_m_method_1_1 == false) && |p_m_method_1_3| == 0 && (p_m_method_1_2.DT_1_4? && ((24.13 < (p_m_method_1_2.DT_1_4_1).0 < 24.33) && ((p_m_method_1_2.DT_1_4_1).1 == 2) && ((p_m_method_1_2.DT_1_4_1).2 == true) && (p_m_method_1_2.DT_1_4_2 == 22) && (p_m_method_1_2.DT_1_4_3 == 4) && (p_m_method_1_2.DT_1_4_4 == 17)))) ==> (((ret_1).0 == 'w') && (((ret_1).1).0 == false) && (((ret_1).1).1 == false) && (((ret_1).1).2 == false) && ((ret_1).2 == false)));
{
	var v_int_7: int := 15;
	var v_int_8: int := -7;
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		continue;
	}
	var v_bool_bool_bool_1: (bool, bool, bool) := (false, false, false);
	var v_char_bool_bool_bool_bool_1: (char, (bool, bool, bool), bool) := ('w', v_bool_bool_bool_1, false);
	var v_real_int_bool_35: (real, int, bool) := (18.18, 22, false);
	var v_bool_bool_bool_2: (bool, bool, bool) := (false, false, false);
	var v_char_bool_bool_bool_bool_5: (char, (bool, bool, bool), bool) := ('w', v_bool_bool_bool_2, false);
	var v_real_int_bool_36: (real, int, bool) := (18.18, 22, false);
	var v_DT_1_4_39: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_36, 23, 19, 19);
	print "p_m_method_1_2.DT_1_4_2", " ", p_m_method_1_2.DT_1_4_2, " ", "p_m_method_1_2.DT_1_4_1", " ", (p_m_method_1_2.DT_1_4_1 == v_real_int_bool_35), " ", "p_m_method_1_2.DT_1_4_4", " ", p_m_method_1_2.DT_1_4_4, " ", "p_m_method_1_2.DT_1_4_3", " ", p_m_method_1_2.DT_1_4_3, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_char_bool_bool_bool_bool_1", " ", (v_char_bool_bool_bool_bool_1 == v_char_bool_bool_bool_bool_5), " ", "v_bool_bool_bool_1", " ", v_bool_bool_bool_1, " ", "v_bool_bool_bool_1.2", " ", v_bool_bool_bool_1.2, " ", "v_bool_bool_bool_1.1", " ", v_bool_bool_bool_1.1, " ", "v_char_bool_bool_bool_bool_1.0", " ", (v_char_bool_bool_bool_bool_1.0 == 'w'), " ", "p_m_method_1_2", " ", (p_m_method_1_2 == v_DT_1_4_39), " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_char_bool_bool_bool_bool_1.1", " ", v_char_bool_bool_bool_bool_1.1, " ", "v_char_bool_bool_bool_bool_1.2", " ", v_char_bool_bool_bool_bool_1.2, " ", "p_m_method_1_2.DT_1_4_1.2", " ", p_m_method_1_2.DT_1_4_1.2, " ", "p_m_method_1_2.DT_1_4_1.0", " ", (p_m_method_1_2.DT_1_4_1.0 == 18.18), " ", "p_m_method_1_2.DT_1_4_1.1", " ", p_m_method_1_2.DT_1_4_1.1, " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_bool_bool_bool_1.0", " ", v_bool_bool_bool_1.0, "\n";
	return v_char_bool_bool_bool_bool_1;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_1: map<bool, bool> := map[false := false, true := false];
	var v_bool_1: bool := false;
	var v_bool_2: bool := true;
	var v_real_int_bool_1: (real, int, bool) := (18.18, 22, false);
	var v_DT_1_4_1: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_1, 23, 19, 19);
	var v_DT_1_4_2: DT_1<(real, int, bool), int> := v_DT_1_4_1;
	var v_seq_3: seq<int> := [24];
	var v_char_bool_bool_bool_bool_2: (char, (bool, bool, bool), bool) := m_method_1(v_bool_2, v_DT_1_4_2, v_seq_3);
	var v_bool_3: bool := (match true {
		case false => false
		case true => false
		case _ => false
	});
	var v_real_int_bool_2: (real, int, bool) := (24.23, 2, true);
	var v_DT_1_4_3: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_2, 22, 4, 17);
	var v_seq_4: seq<DT_1<(real, int, bool), int>> := [v_DT_1_4_3];
	var v_int_9: int := -20;
	var v_seq_36: seq<DT_1<(real, int, bool), int>> := v_seq_4;
	var v_int_73: int := v_int_9;
	var v_int_74: int := safe_index_seq(v_seq_36, v_int_73);
	v_int_9 := v_int_74;
	var v_real_int_bool_3: (real, int, bool) := (21.18, 3, false);
	var v_DT_1_4_4: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_3, -28, 14, 8);
	var v_DT_1_4_5: DT_1<(real, int, bool), int> := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_9]) else (v_DT_1_4_4));
	var v_seq_5: seq<int> := [4, -9, 1];
	var v_seq_37: seq<int> := v_seq_5;
	var v_int_77: int := 8;
	var v_int_78: int := 0;
	var v_int_79: int, v_int_80: int := safe_subsequence(v_seq_37, v_int_77, v_int_78);
	var v_int_75: int, v_int_76: int := v_int_79, v_int_80;
	var v_seq_6: seq<int> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_75..v_int_76]) else (v_seq_5));
	var v_char_bool_bool_bool_bool_3: (char, (bool, bool, bool), bool) := m_method_1(v_bool_3, v_DT_1_4_5, v_seq_6);
	var v_int_21: int := (20 + -26);
	var v_DT_2_1_1: DT_2 := DT_2_1;
	var v_DT_2_1_2: DT_2 := DT_2_1;
	var v_map_5: map<DT_2, int> := map[v_DT_2_1_1 := 4];
	var v_DT_2_1_3: DT_2 := DT_2_1;
	var v_DT_2_1_4: DT_2 := v_DT_2_1_3;
	var v_int_22: int := (if ((v_DT_2_1_4 in v_map_5)) then (v_map_5[v_DT_2_1_4]) else (13));
	var v_seq_11: seq<int> := [11, 15, 15];
	var v_int_19: int := 16;
	var v_int_20: int := safe_index_seq(v_seq_11, v_int_19);
	var v_int_23: int := v_int_20;
	var v_seq_12: seq<DT_1<(real, int, bool), int>> := m_method_2(v_int_21, v_int_22, v_int_23);
	var v_seq_13: seq<DT_1<(real, int, bool), int>> := v_seq_12;
	var v_int_24: int := v_int_19;
	var v_seq_41: seq<DT_1<(real, int, bool), int>> := v_seq_13;
	var v_int_91: int := v_int_24;
	var v_int_92: int := safe_index_seq(v_seq_41, v_int_91);
	v_int_24 := v_int_92;
	var v_int_int_1: (int, int) := (17, 18);
	var v_int_int_2: (int, int) := (28, 14);
	var v_int_int_3: (int, int) := (if (true) then (v_int_int_1) else (v_int_int_2));
	var v_bool_real_bool_3: (bool, real, bool) := (true, 10.01, false);
	var v_bool_real_bool_4: (bool, real, bool) := v_bool_real_bool_3;
	var v_char_7: char := 'G';
	var v_char_8: char := m_method_3(v_bool_real_bool_4, v_char_7);
	var v_char_9: char := v_char_8;
	var v_bool_8: bool := v_bool_real_bool_3.2;
	var v_char_10: char := v_char_8;
	var v_DT_1_4_37: DT_1<(real, int, bool), int> := m_method_5(v_int_int_3, v_char_9, v_bool_8, v_char_10);
	var v_DT_1_1_1: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_2: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_3: DT_1<int, real> := DT_1_1;
	var v_seq_20: seq<DT_1<int, real>> := [v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3];
	var v_seq_39: seq<DT_1<int, real>> := v_seq_20;
	var v_int_85: int := 28;
	var v_int_86: int := 12;
	var v_int_87: int, v_int_88: int := safe_subsequence(v_seq_39, v_int_85, v_int_86);
	var v_int_83: int, v_int_84: int := v_int_87, v_int_88;
	var v_seq_22: seq<DT_1<int, real>> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_83..v_int_84]) else (v_seq_20));
	var v_seq_23: seq<DT_1<int, real>> := v_seq_22;
	var v_int_53: int := |{2}|;
	var v_int_54: int := safe_index_seq(v_seq_23, v_int_53);
	var v_int_55: int := v_int_54;
	var v_DT_1_1_4: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_5: DT_1<int, real> := DT_1_1;
	var v_seq_21: seq<DT_1<int, real>> := [v_DT_1_1_4, v_DT_1_1_5];
	var v_int_52: int := 26;
	var v_DT_1_1_6: DT_1<int, real> := DT_1_1;
	var v_seq_27: seq<DT_1<int, real>> := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_55 := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_52]) else (v_DT_1_1_6))]) else (v_seq_22));
	var v_seq_24: seq<int> := [2, 8, 16];
	var v_seq_25: seq<int> := v_seq_24;
	var v_int_56: int := 20;
	var v_int_57: int := safe_index_seq(v_seq_25, v_int_56);
	var v_int_58: int := v_int_57;
	var v_seq_26: seq<int> := (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_58 := 26]) else (v_seq_24));
	var v_int_59: int := |multiset{22, 9, 17}|;
	var v_seq_40: seq<int> := v_seq_26;
	var v_int_89: int := v_int_59;
	var v_int_90: int := safe_index_seq(v_seq_40, v_int_89);
	v_int_59 := v_int_90;
	var v_int_60: int := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_59]) else (v_int_57));
	var v_seq_28: seq<DT_1<int, real>> := v_seq_21;
	var v_int_61: int := (if (true) then (10) else (0));
	var v_seq_42: seq<DT_1<int, real>> := v_seq_28;
	var v_int_93: int := v_int_61;
	var v_int_94: int := safe_index_seq(v_seq_42, v_int_93);
	v_int_61 := v_int_94;
	var v_DT_1_1_7: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_8: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_9: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_10: DT_1<int, real> := DT_1_1;
	var v_map_8: map<int, DT_1<int, real>> := map[-18 := v_DT_1_1_7, 1 := v_DT_1_1_8, 20 := v_DT_1_1_9, 22 := v_DT_1_1_10];
	var v_int_62: int := 20;
	var v_DT_1_1_11: DT_1<int, real> := DT_1_1;
	var v_seq_29: seq<bool> := [];
	var v_int_63: int := 10;
	var v_seq_30: seq<int> := v_seq_26;
	var v_int_64: int := (if (true) then (25) else (12));
	var v_char_bool_bool_bool_bool_4: (char, (bool, bool, bool), bool), v_DT_1_4_38: DT_1<(real, int, bool), int>, v_DT_1_1_12: DT_1<int, real>, v_int_65: int := (match 13 {
		case 6 => (if ((if ((v_bool_1 in v_map_1)) then (v_map_1[v_bool_1]) else (true))) then (v_char_bool_bool_bool_bool_2) else (v_char_bool_bool_bool_bool_2))
		case _ => v_char_bool_bool_bool_bool_3
	}), (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_24]) else (v_DT_1_4_37)), (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_60]) else ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_61]) else ((if ((v_int_62 in v_map_8)) then (v_map_8[v_int_62]) else (v_DT_1_1_11)))))), (if ((match -29 {
		case 5 => (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_63]) else (true))
		case _ => (18 !in [27, -15])
	})) then (v_int_61) else ((if ((|v_seq_30| > 0)) then (v_seq_30[v_int_64]) else ((match 1 {
		case _ => 0
	})))));
	var v_seq_31: seq<seq<int>> := [[11, 6, 27, 27], [18, 21, 19]];
	var v_int_66: int := 6;
	var v_seq_44: seq<seq<int>> := v_seq_31;
	var v_int_97: int := v_int_66;
	var v_int_98: int := safe_index_seq(v_seq_44, v_int_97);
	v_int_66 := v_int_98;
	var v_seq_32: seq<int> := ([14, 20, 0] + [13, 2, 19]);
	var v_int_67: int := (15 * 3);
	var v_seq_45: seq<int> := v_seq_32;
	var v_int_99: int := v_int_67;
	var v_int_100: int := safe_index_seq(v_seq_45, v_int_99);
	v_int_67 := v_int_100;
	var v_map_9: map<int, int> := map[7 := 17, 6 := 27];
	var v_int_68: int := 16;
	var v_seq_33: seq<seq<int>> := [[13, 17, -14], [], [27]];
	var v_int_69: int := 26;
	var v_seq_43: seq<seq<int>> := v_seq_33;
	var v_int_95: int := v_int_69;
	var v_int_96: int := safe_index_seq(v_seq_43, v_int_95);
	v_int_69 := v_int_96;
	var v_seq_34: seq<int> := (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_69]) else ([-28, 2]));
	var v_int_70: int := v_int_57;
	var v_seq_35: seq<int> := [10];
	var v_int_71: int := 10;
	var v_map_10: map<int, int> := map[4 := 23, 13 := 1, 29 := 20][-14 := -17];
	var v_int_72: int := (24 * 28);
	v_int_61, v_int_23, v_int_54, v_int_65 := v_int_62, (if (((if ((|v_seq_31| > 0)) then (v_seq_31[v_int_66]) else ([26, 17])) <= ([6, 11] + [19, 19]))) then ((if (v_bool_real_bool_3.0) then ((10 * 13)) else ((match 9 {
		case _ => 24
	})))) else ((if ((|v_seq_32| > 0)) then (v_seq_32[v_int_67]) else ((if ((v_int_68 in v_map_9)) then (v_map_9[v_int_68]) else (24)))))), (if (v_bool_real_bool_3.0) then ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_70]) else ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_71]) else (9))))) else ((if ((v_int_72 in v_map_10)) then (v_map_10[v_int_72]) else ((25 / 21))))), v_int_68;
	var v_real_int_bool_67: (real, int, bool) := (-26.83, 20, true);
	var v_DT_1_4_54: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_67, 14, 24, 20);
	var v_real_int_bool_68: (real, int, bool) := (-13.72, 0, false);
	var v_DT_1_4_55: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_68, 22, 18, 11);
	var v_bool_bool_bool_3: (bool, bool, bool) := (false, false, false);
	var v_char_bool_bool_bool_bool_6: (char, (bool, bool, bool), bool) := ('w', v_bool_bool_bool_3, false);
	var v_real_int_bool_69: (real, int, bool) := (-26.83, 20, true);
	var v_DT_1_4_56: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_69, 14, 24, 20);
	var v_real_int_bool_70: (real, int, bool) := (-29.90, 14, true);
	var v_DT_1_4_57: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_70, 22, -29, 13);
	var v_real_int_bool_71: (real, int, bool) := (-10.86, -13, true);
	var v_DT_1_4_58: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_71, -9, 27, -10);
	var v_real_int_bool_72: (real, int, bool) := (-4.17, 20, false);
	var v_DT_1_4_59: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_72, 10, 4, 1);
	var v_real_int_bool_73: (real, int, bool) := (-26.83, 20, true);
	var v_DT_1_4_60: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_73, 14, 24, 20);
	var v_real_int_bool_74: (real, int, bool) := (-29.90, 14, true);
	var v_DT_1_4_61: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_74, 22, -29, 13);
	var v_real_int_bool_75: (real, int, bool) := (-10.86, -13, true);
	var v_DT_1_4_62: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_75, -9, 27, -10);
	var v_real_int_bool_76: (real, int, bool) := (-4.17, 20, false);
	var v_DT_1_4_63: DT_1<(real, int, bool), int> := DT_1_4(v_real_int_bool_76, 10, 4, 1);
	var v_DT_2_1_5: DT_2 := DT_2_1;
	var v_DT_1_1_13: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_14: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_15: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_16: DT_1<int, real> := DT_1_1;
	var v_bool_real_bool_6: (bool, real, bool) := (true, 10.01, false);
	var v_bool_real_bool_7: (bool, real, bool) := (true, 10.01, false);
	print "v_map_10", " ", (v_map_10 == map[4 := 23, 13 := 1, 29 := 20, -14 := -17]), " ", "v_seq_32", " ", v_seq_32, " ", "v_seq_33", " ", v_seq_33, " ", "v_seq_34", " ", v_seq_34, " ", "v_seq_35", " ", v_seq_35, " ", "v_seq_30", " ", v_seq_30, " ", "v_seq_31", " ", v_seq_31, " ", "v_seq_25", " ", v_seq_25, " ", "v_seq_26", " ", v_seq_26, " ", "v_seq_27", " ", v_seq_27, " ", "v_seq_28", " ", v_seq_28, " ", "v_seq_21", " ", v_seq_21, " ", "v_seq_22", " ", v_seq_22, " ", "v_seq_23", " ", v_seq_23, " ", "v_seq_24", " ", v_seq_24, " ", "v_DT_1_4_38", " ", (v_DT_1_4_38 == v_DT_1_4_54), " ", "v_int_71", " ", v_int_71, " ", "v_int_70", " ", v_int_70, " ", "v_int_int_1.1", " ", v_int_int_1.1, " ", "v_int_int_1.0", " ", v_int_int_1.0, " ", "v_seq_20", " ", v_seq_20, " ", "v_DT_1_4_37", " ", (v_DT_1_4_37 == v_DT_1_4_55), " ", "v_int_72", " ", v_int_72, " ", "v_bool_real_bool_3.2", " ", v_bool_real_bool_3.2, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_bool_real_bool_3.1", " ", (v_bool_real_bool_3.1 == 10.01), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_real_bool_3.0", " ", v_bool_real_bool_3.0, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_bool_8", " ", v_bool_8, " ", "v_int_19", " ", v_int_19, " ", "v_char_bool_bool_bool_bool_4", " ", (v_char_bool_bool_bool_bool_4 == v_char_bool_bool_bool_bool_6), " ", "v_int_24", " ", v_int_24, " ", "v_int_68", " ", v_int_68, " ", "v_int_23", " ", v_int_23, " ", "v_int_67", " ", v_int_67, " ", "v_int_22", " ", v_int_22, " ", "v_int_66", " ", v_int_66, " ", "v_int_21", " ", v_int_21, " ", "v_int_65", " ", v_int_65, " ", "v_seq_11", " ", v_seq_11, " ", "v_seq_12", " ", (v_seq_12 == [v_DT_1_4_56, v_DT_1_4_57, v_DT_1_4_58, v_DT_1_4_59]), " ", "v_seq_13", " ", (v_seq_13 == [v_DT_1_4_60, v_DT_1_4_61, v_DT_1_4_62, v_DT_1_4_63]), " ", "v_int_69", " ", v_int_69, " ", "v_int_60", " ", v_int_60, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_int_20", " ", v_int_20, " ", "v_int_64", " ", v_int_64, " ", "v_int_62", " ", v_int_62, " ", "v_int_61", " ", v_int_61, " ", "v_map_5", " ", (v_map_5 == map[v_DT_2_1_5 := 4]), " ", "v_int_int_1", " ", v_int_int_1, " ", "v_int_int_2", " ", v_int_int_2, " ", "v_int_int_3", " ", v_int_int_3, " ", "v_map_9", " ", (v_map_9 == map[6 := 27, 7 := 17]), " ", "v_map_8", " ", (v_map_8 == map[-18 := v_DT_1_1_13, 1 := v_DT_1_1_14, 20 := v_DT_1_1_15, 22 := v_DT_1_1_16]), " ", "v_char_7", " ", (v_char_7 == 'G'), " ", "v_char_9", " ", (v_char_9 == 'I'), " ", "v_char_8", " ", (v_char_8 == 'I'), " ", "v_bool_real_bool_3", " ", (v_bool_real_bool_3 == v_bool_real_bool_6), " ", "v_bool_real_bool_4", " ", (v_bool_real_bool_4 == v_bool_real_bool_7), " ", "v_DT_2_1_4", " ", v_DT_2_1_4, " ", "v_int_57", " ", v_int_57, " ", "v_DT_2_1_3", " ", v_DT_2_1_3, " ", "v_int_56", " ", v_int_56, " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "v_int_55", " ", v_int_55, " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_int_54", " ", v_int_54, " ", "v_int_59", " ", v_int_59, " ", "v_int_58", " ", v_int_58, " ", "v_char_10", " ", (v_char_10 == 'I'), " ", "v_int_int_2.0", " ", v_int_int_2.0, " ", "v_int_53", " ", v_int_53, " ", "v_int_int_2.1", " ", v_int_int_2.1, " ", "v_int_52", " ", v_int_52, "\n";
}
