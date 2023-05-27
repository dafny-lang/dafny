// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1 | DT_1_3(DT_1_3_1: bool, DT_1_3_2: real, DT_1_3_3: int, DT_1_3_4: int)
datatype DT_2 = DT_2_1
datatype DT_3<T_1, T_2> = DT_3_1 | DT_3_2(DT_3_2_1: T_2, DT_3_2_2: T_1, DT_3_2_3: T_2, DT_3_2_4: T_1)
datatype DT_4<T_3, T_4> = DT_4_1 | DT_4_3(DT_4_3_1: T_3, DT_4_3_2: T_3, DT_4_3_3: T_4, DT_4_3_4: real)
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

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int) returns (ret_1: (char, bool))
{
	assert true;
	expect true;
	var v_int_45: int, v_int_46: int, v_int_47: int, v_int_48: int := 18, 17, -20, 23;
	var v_char_bool_3: (char, bool) := ('S', false);
	return v_char_bool_3;
}

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: int, p_m_method_4_3: int) returns (ret_1: int)
{
	return 2;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int, p_m_method_3_3: int, p_m_method_3_4: int) returns (ret_1: int, ret_2: int, ret_3: int)
{
	return 8, 0, 8;
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

method m_method_2(p_m_method_2_1: DT_1, p_m_method_2_2: seq<bool>, p_m_method_2_3: int, p_m_method_2_4: seq<real>) returns (ret_1: seq<(char, bool)>)
{
	var v_seq_9: seq<bool> := [false, true, false, true];
	var v_bool_2: bool := true;
	var v_int_19: int := 22;
	var v_int_20: int := 25;
	while (v_int_19 < v_int_20) 
		decreases v_int_20 - v_int_19;
		invariant (v_int_19 <= v_int_20);
	{
		v_int_19 := (v_int_19 + 1);
		if false {
			
		}
	}
	if false {
		var v_char_bool_1: (char, bool) := ('E', true);
		return [v_char_bool_1];
	} else {
		assert true;
		expect true;
		var v_DT_2_1_1: DT_2 := DT_2_1;
		var v_DT_4_3_1: DT_4<int, int> := DT_4_3(15, 2, 14, -28.14);
		var v_DT_4_3_2: DT_4<int, int> := DT_4_3(1, 23, -20, 12.11);
		var v_DT_3_2_1: DT_3<int, DT_4<int, int>> := DT_3_2(v_DT_4_3_1, 29, v_DT_4_3_2, -14);
		var v_int_21: int, v_DT_2_1_2: DT_2, v_int_22: int, v_int_23: int, v_DT_3_2_2: DT_3<int, DT_4<int, int>> := 3, v_DT_2_1_1, 26, 23, v_DT_3_2_1;
		v_int_23, v_int_21, v_int_22 := 16, 28, 6;
		var v_int_24: int := 27;
		var v_int_25: int := -4;
		while (v_int_24 < v_int_25) 
			decreases v_int_25 - v_int_24;
			invariant (v_int_24 <= v_int_25);
		{
			v_int_24 := (v_int_24 + 1);
		}
		var v_int_26: int := -6;
		var v_int_27: int := 0;
		var v_int_28: int := safe_modulus(v_int_26, v_int_27);
		v_int_27 := v_int_28;
	}
	var v_int_41: int, v_int_42: int := 26, 6;
	for v_int_29 := v_int_41 to v_int_42 
		invariant (v_int_42 - v_int_29 >= 0)
	{
		var v_int_30: int := 19;
		var v_int_31: int := -6;
		var v_int_32: int := 6;
		var v_int_33: int := 10;
		var v_int_34: int, v_int_35: int, v_int_36: int := m_method_3(v_int_30, v_int_31, v_int_32, v_int_33);
		v_int_35, v_int_31, v_int_30 := v_int_34, v_int_35, v_int_36;
		match 1 {
			case _ => {
				v_int_36, v_int_31, v_int_30, v_int_33, v_int_34 := 23, 21, 23, 0, 16;
				v_int_30, v_int_36, v_int_33 := 9, 23, 18;
				var v_int_37: int := 28;
				var v_int_38: int := 16;
				var v_int_39: int := 2;
				var v_int_40: int := m_method_4(v_int_37, v_int_38, v_int_39);
				v_int_39 := v_int_40;
				v_int_38, v_int_39, v_int_30 := 24, 4, 15;
			}
			
		}
		
		assert true;
		expect true;
		continue;
	}
	var v_char_bool_2: (char, bool) := ('A', true);
	return [v_char_bool_2];
}

method m_method_1(p_m_method_1_1: DT_1, p_m_method_1_2: char, p_m_method_1_3: bool) returns (ret_1: seq<int>)
	requires ((p_m_method_1_1.DT_1_3? && ((p_m_method_1_1.DT_1_3_1 == true) && (16.67 < p_m_method_1_1.DT_1_3_2 < 16.87) && (p_m_method_1_1.DT_1_3_3 == 24) && (p_m_method_1_1.DT_1_3_4 == 16))) && (p_m_method_1_3 == false) && (p_m_method_1_2 == 'Q'));
	ensures (((p_m_method_1_1.DT_1_3? && ((p_m_method_1_1.DT_1_3_1 == true) && (16.67 < p_m_method_1_1.DT_1_3_2 < 16.87) && (p_m_method_1_1.DT_1_3_3 == 24) && (p_m_method_1_1.DT_1_3_4 == 16))) && (p_m_method_1_3 == false) && (p_m_method_1_2 == 'Q')) ==> (|ret_1| == 0));
{
	var v_int_9: int, v_int_10: int := 3, 6;
	for v_int_8 := v_int_9 to v_int_10 
		invariant (v_int_10 - v_int_8 >= 0)
	{
		var v_char_multiset_1: (char, multiset<real>) := ('g', multiset{19.08, -25.68});
		var v_char_multiset_2: (char, multiset<real>), v_map_1: map<real, char> := v_char_multiset_1, map[25.32 := 'Q', 27.07 := 's', 26.09 := 'u', -4.42 := 'U', -12.06 := 'j'];
		var v_char_multiset_3: (char, multiset<real>) := ('g', multiset{19.08, -25.68});
		var v_char_multiset_4: (char, multiset<real>) := ('g', multiset{19.08, -25.68});
		var v_DT_1_3_3: DT_1 := DT_1_3(true, 16.77, 24, 16);
		print "v_char_multiset_1.0", " ", (v_char_multiset_1.0 == 'g'), " ", "v_char_multiset_1.1", " ", (v_char_multiset_1.1 == multiset{19.08, -25.68}), " ", "v_char_multiset_2", " ", (v_char_multiset_2 == v_char_multiset_3), " ", "v_char_multiset_1", " ", (v_char_multiset_1 == v_char_multiset_4), " ", "v_int_8", " ", v_int_8, " ", "v_map_1", " ", (v_map_1 == map[-12.06 := 'j', 25.32 := 'Q', -4.42 := 'U', 27.07 := 's', 26.09 := 'u']), " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 'Q'), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == v_DT_1_3_3), " ", "p_m_method_1_1.DT_1_3_1", " ", p_m_method_1_1.DT_1_3_1, " ", "p_m_method_1_1.DT_1_3_2", " ", (p_m_method_1_1.DT_1_3_2 == 16.77), " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "p_m_method_1_1.DT_1_3_3", " ", p_m_method_1_1.DT_1_3_3, " ", "p_m_method_1_1.DT_1_3_4", " ", p_m_method_1_1.DT_1_3_4, "\n";
		return [];
	}
	return [];
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_DT_1_3_1: DT_1 := DT_1_3(true, 16.77, 24, 16);
	var v_DT_1_3_2: DT_1 := v_DT_1_3_1;
	var v_char_1: char := 'Q';
	var v_bool_1: bool := false;
	var v_seq_3: seq<int> := m_method_1(v_DT_1_3_2, v_char_1, v_bool_1);
	var v_seq_4: seq<int> := [21, 4, 11, 17];
	var v_seq_5: seq<int> := v_seq_4;
	var v_int_11: int := 29;
	var v_int_12: int := safe_index_seq(v_seq_5, v_int_11);
	var v_int_13: int := v_int_12;
	var v_seq_6: seq<int> := (v_seq_3 + (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_13 := -17]) else (v_seq_4)));
	var v_int_14: int := v_int_11;
	var v_seq_17: seq<int> := v_seq_6;
	var v_int_55: int := v_int_14;
	var v_int_56: int := safe_index_seq(v_seq_17, v_int_55);
	v_int_14 := v_int_56;
	var v_int_15: int, v_int_16: int := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_14]) else (v_int_14)), v_int_14;
	for v_int_7 := v_int_15 to v_int_16 
		invariant (v_int_16 - v_int_7 >= 0)
	{
		var v_DT_1_3_4: DT_1 := DT_1_3(true, 16.77, 24, 16);
		var v_DT_1_3_5: DT_1 := DT_1_3(true, 16.77, 24, 16);
		print "v_int_7", " ", v_int_7, " ", "v_char_1", " ", (v_char_1 == 'Q'), " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_3_1", " ", (v_DT_1_3_1 == v_DT_1_3_4), " ", "v_DT_1_3_2", " ", (v_DT_1_3_2 == v_DT_1_3_5), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_DT_1_3_1.DT_1_3_4", " ", v_DT_1_3_1.DT_1_3_4, " ", "v_int_11", " ", v_int_11, " ", "v_seq_6", " ", v_seq_6, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_14", " ", v_int_14, " ", "v_DT_1_3_1.DT_1_3_2", " ", (v_DT_1_3_1.DT_1_3_2 == 16.77), " ", "v_DT_1_3_1.DT_1_3_3", " ", v_DT_1_3_1.DT_1_3_3, " ", "v_DT_1_3_1.DT_1_3_1", " ", v_DT_1_3_1.DT_1_3_1, "\n";
		return ;
	}
	var v_seq_7: seq<seq<set<real>>> := ([[]] + (if (false) then ([[], [{17.12, 27.15, -19.59, -8.03}, {-0.11, 6.71}], [{}, {14.55, -17.98, 23.82, 9.31}, {12.87, 6.22}, {14.12, 21.37}]]) else ([[{-22.26, -5.97, 2.69}, {-21.34, 10.32, -29.83, -26.32}, {-9.37}, {-25.15}], [{23.85}, {}, {-9.90, 18.80, 24.12}, {-3.42, 7.56, 14.41}], [{29.88}, {10.15, 21.04, -1.80, 19.83}, {-10.14, 6.97, -21.52}, {9.69, -22.13}]])));
	var v_map_3: map<int, int> := (map[23 := 22, 2 := 21, 0 := -9, 13 := 6, 4 := 23] - {-10, 16, 17});
	var v_map_2: map<multiset<bool>, int> := map[multiset{false} := 21, multiset{false, true, false, false} := 25, multiset{false} := 19];
	var v_multiset_1: multiset<bool> := multiset{true};
	var v_int_17: int := (if ((v_multiset_1 in v_map_2)) then (v_map_2[v_multiset_1]) else (15));
	var v_int_18: int := (if ((v_int_17 in v_map_3)) then (v_map_3[v_int_17]) else (v_int_14));
	var v_seq_8: seq<set<real>> := [];
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_DT_1_1_2: DT_1 := v_DT_1_1_1;
	var v_seq_10: seq<bool> := [false, true, false];
	var v_int_43: int := 26;
	var v_seq_11: seq<real> := [9.94];
	var v_seq_12: seq<(char, bool)> := m_method_2(v_DT_1_1_2, v_seq_10, v_int_43, v_seq_11);
	var v_seq_13: seq<(char, bool)> := v_seq_12;
	var v_int_44: int := v_int_15;
	var v_int_49: int := -9;
	var v_int_50: int := 7;
	var v_char_bool_4: (char, bool) := m_method_5(v_int_49, v_int_50);
	var v_char_bool_5: (char, bool) := ('V', true);
	var v_char_bool_6: (char, bool) := ('N', true);
	var v_seq_14: seq<(char, bool)> := ([v_char_bool_5, v_char_bool_6] + []);
	var v_map_4: map<int, int> := map[27 := 17, 20 := 1, -7 := 16, 7 := 8, 17 := 12];
	var v_int_51: int := 21;
	var v_int_52: int := (if ((v_int_51 in v_map_4)) then (v_map_4[v_int_51]) else (6));
	var v_char_bool_7: (char, bool) := ('i', false);
	var v_map_5: map<int, (char, bool)> := map[27 := v_char_bool_7];
	var v_int_53: int := 24;
	var v_char_bool_8: (char, bool) := ('s', false);
	var v_char_bool_9: (char, bool) := ('C', false);
	var v_char_bool_10: (char, bool) := ('x', false);
	var v_char_bool_11: (char, bool) := ('Z', false);
	var v_char_bool_12: (char, bool) := ('C', true);
	var v_char_bool_13: (char, bool) := ('F', true);
	var v_char_bool_14: (char, bool) := ('c', false);
	var v_seq_15: seq<(char, bool)> := ([v_char_bool_9, v_char_bool_10] + [v_char_bool_11, v_char_bool_12, v_char_bool_13, v_char_bool_14]);
	var v_int_54: int := v_int_11;
	var v_seq_16: seq<set<real>>, v_char_bool_15: (char, bool) := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_18]) else (((if ((|v_seq_8| > 0)) then (v_seq_8[12..5]) else (v_seq_8)) + ([{-10.25, 28.45, 16.07}, {27.93, 7.80}, {4.90, -7.09}, {-5.63, 6.55}] + [])))), (match 'A' {
		case _ => (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_54]) else (v_char_bool_10))
	});
	return ;
}
