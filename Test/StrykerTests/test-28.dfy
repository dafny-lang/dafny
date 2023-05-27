// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1 | DT_1_2(DT_1_2_1: real, DT_1_2_2: bool)
datatype DT_2<T_1> = DT_2_1 | DT_2_3(DT_2_3_1: T_1, DT_2_3_2: T_1, DT_2_3_3: T_1, DT_2_3_4: T_1)
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: bool, p_m_method_9_2: bool) returns (ret_1: char)
	requires ((p_m_method_9_1 == false) && (p_m_method_9_2 == false));
	ensures (((p_m_method_9_1 == false) && (p_m_method_9_2 == false)) ==> ((ret_1 == 'n')));
{
	var v_seq_15: seq<char> := ['n'];
	var v_int_38: int := 9;
	var v_seq_20: seq<char> := v_seq_15;
	var v_int_45: int := v_int_38;
	var v_int_46: int := safe_index_seq(v_seq_20, v_int_45);
	v_int_38 := v_int_46;
	print "v_seq_15", " ", (v_seq_15 == ['n']), " ", "v_int_38", " ", v_int_38, " ", "p_m_method_9_2", " ", p_m_method_9_2, " ", "p_m_method_9_1", " ", p_m_method_9_1, "\n";
	return (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_38]) else ('L'));
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: bool, p_m_method_8_2: bool, p_m_method_8_3: bool, p_m_method_8_4: bool) returns (ret_1: bool)
	requires ((p_m_method_8_2 == false) && (p_m_method_8_1 == true) && (p_m_method_8_4 == false) && (p_m_method_8_3 == true)) || ((p_m_method_8_2 == true) && (p_m_method_8_1 == false) && (p_m_method_8_4 == true) && (p_m_method_8_3 == true));
	ensures (((p_m_method_8_2 == true) && (p_m_method_8_1 == false) && (p_m_method_8_4 == true) && (p_m_method_8_3 == true)) ==> ((ret_1 == true))) && (((p_m_method_8_2 == false) && (p_m_method_8_1 == true) && (p_m_method_8_4 == false) && (p_m_method_8_3 == true)) ==> ((ret_1 == true)));
{
	print "p_m_method_8_4", " ", p_m_method_8_4, " ", "p_m_method_8_1", " ", p_m_method_8_1, " ", "p_m_method_8_3", " ", p_m_method_8_3, " ", "p_m_method_8_2", " ", p_m_method_8_2, "\n";
	return true;
}

method m_method_7(p_m_method_7_1: bool, p_m_method_7_2: bool) returns (ret_1: seq<bool>)
	requires ((p_m_method_7_2 == false) && (p_m_method_7_1 == false));
	ensures (((p_m_method_7_2 == false) && (p_m_method_7_1 == false)) ==> (|ret_1| == 2 && (ret_1[0] == false) && (ret_1[1] == true)));
{
	print "p_m_method_7_2", " ", p_m_method_7_2, " ", "p_m_method_7_1", " ", p_m_method_7_1, "\n";
	return [false, true];
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: bool, p_m_method_6_2: bool, p_m_method_6_3: bool) returns (ret_1: char)
{
	var v_bool_2: bool, v_bool_3: bool, v_bool_4: bool := true, true, false;
	var v_int_20: int, v_int_21: int := 11, 19;
	for v_int_19 := v_int_20 to v_int_21 
		invariant (v_int_21 - v_int_19 >= 0)
	{
		return 'q';
	}
	var v_int_23: int, v_int_24: int := 5, 12;
	for v_int_22 := v_int_23 to v_int_24 
		invariant (v_int_24 - v_int_22 >= 0)
	{
		return 'P';
	}
	var v_bool_5: bool, v_bool_6: bool, v_bool_7: bool, v_bool_8: bool := false, false, true, true;
	return 'W';
}

method m_method_5(p_m_method_5_1: (int, real, bool)) returns (ret_1: seq<map<int, bool>>)
{
	return [];
}

method m_method_4(p_m_method_4_1: int) returns (ret_1: char)
{
	return 't';
}

method m_method_3(p_m_method_3_1: DT_2<array<real>>, p_m_method_3_2: DT_1, p_m_method_3_3: bool, p_m_method_3_4: map<int, int>) returns (ret_1: char)
	requires ((p_m_method_3_1.DT_2_1? && ((p_m_method_3_1 == DT_2_1))) && (p_m_method_3_3 == true) && (p_m_method_3_2.DT_1_1? && ((p_m_method_3_2 == DT_1_1))) && (p_m_method_3_4 == map[15 := 8]));
	ensures (((p_m_method_3_1.DT_2_1? && ((p_m_method_3_1 == DT_2_1))) && (p_m_method_3_3 == true) && (p_m_method_3_2.DT_1_1? && ((p_m_method_3_2 == DT_1_1))) && (p_m_method_3_4 == map[15 := 8])) ==> ((ret_1 == 'S')));
{
	if ([map['M' := 12]] < [map['A' := 1], map['X' := 20, 'q' := 10, 'M' := 28], map['D' := 17, 'c' := 25], map['b' := 7, 'N' := 7]]) {
		var v_int_12: int := 25;
		var v_int_13: int := 11;
		var v_int_14: int := safe_modulus(v_int_12, v_int_13);
		var v_int_10: int := v_int_14;
		var v_int_11: int := v_int_12;
		while (v_int_10 < v_int_11) 
			decreases v_int_11 - v_int_10;
			invariant (v_int_10 <= v_int_11);
		{
			v_int_10 := (v_int_10 + 1);
			var v_int_15: int := 6;
			var v_char_1: char := m_method_4(v_int_15);
			return v_char_1;
		}
		var v_int_real_bool_1: (int, real, bool) := (3, 0.60, false);
		var v_int_real_bool_2: (int, real, bool) := v_int_real_bool_1;
		var v_seq_3: seq<map<int, bool>> := m_method_5(v_int_real_bool_2);
		var v_map_3: map<bool, char>, v_seq_4: seq<map<int, bool>>, v_real_1: real, v_bool_1: bool, v_map_4: map<int, set<real>> := map[true := 'M', false := 'K'][false := 'S'], v_seq_3, v_int_real_bool_1.1, p_m_method_3_3, (map[18 := {-4.53, -4.94, -13.97, 2.58}, 11 := {-7.63, 12.39}, 26 := {-12.84, 4.01}, 11 := {}] + map[13 := {-18.03, 1.73, 20.06}]);
	} else {
		if p_m_method_3_3 {
			var v_map_5: map<int, char> := map[-18 := 'a', 1 := 'M'];
			var v_int_16: int := 28;
			print "v_map_5", " ", (v_map_5 == map[-18 := 'a', 1 := 'M']), " ", "v_int_16", " ", v_int_16, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", (p_m_method_3_4 == map[15 := 8]), " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
			return (if ((v_int_16 in v_map_5)) then (v_map_5[v_int_16]) else ('S'));
		} else {
			var v_int_17: int := 5;
			var v_char_2: char := m_method_4(v_int_17);
			return v_char_2;
		}
	}
	var v_DT_1_2_1: DT_1 := DT_1_2(26.81, true);
	var v_DT_1_2_2: DT_1 := DT_1_2(-8.13, true);
	var v_DT_1_2_3: DT_1 := DT_1_2(-22.23, true);
	var v_DT_1_2_4: DT_1 := DT_1_2(15.02, false);
	var v_map_6: map<multiset<seq<int>>, seq<DT_1>> := map[multiset{[6]} := [v_DT_1_2_1, v_DT_1_2_2, v_DT_1_2_3, v_DT_1_2_4]];
	var v_multiset_2: multiset<seq<int>> := multiset{[20, 14, 5, 5], [-4, 6, 23, 25]};
	var v_DT_1_2_5: DT_1 := DT_1_2(5.83, true);
	var v_DT_1_2_6: DT_1 := DT_1_2(7.47, true);
	var v_DT_1_2_7: DT_1 := DT_1_2(12.51, false);
	var v_DT_1_2_8: DT_1 := DT_1_2(27.44, false);
	var v_seq_5: seq<char> := ['c', 'Z', 'R'];
	var v_int_18: int := 29;
	var v_bool_9: bool := false;
	var v_bool_10: bool := false;
	var v_bool_11: bool := true;
	var v_char_3: char := m_method_6(v_bool_9, v_bool_10, v_bool_11);
	var v_bool_12: bool, v_seq_6: seq<DT_1>, v_int_25: int, v_char_4: char, v_char_5: char := p_m_method_3_3, (if ((v_multiset_2 in v_map_6)) then (v_map_6[v_multiset_2]) else ([v_DT_1_2_5, v_DT_1_2_6, v_DT_1_2_7, v_DT_1_2_8])), (24 / -24), (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_18]) else ('K')), v_char_3;
	var v_int_26: int := -22;
	var v_char_6: char := m_method_4(v_int_26);
	return v_char_6;
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

method m_method_2(p_m_method_2_1: seq<bool>, p_m_method_2_2: DT_1, p_m_method_2_3: char) returns (ret_1: char)
	requires ((p_m_method_2_2.DT_1_2? && ((11.67 < p_m_method_2_2.DT_1_2_1 < 11.87) && (p_m_method_2_2.DT_1_2_2 == false))) && |p_m_method_2_1| == 2 && (p_m_method_2_1[0] == true) && (p_m_method_2_1[1] == true) && (p_m_method_2_3 == 'n'));
	ensures (((p_m_method_2_2.DT_1_2? && ((11.67 < p_m_method_2_2.DT_1_2_1 < 11.87) && (p_m_method_2_2.DT_1_2_2 == false))) && |p_m_method_2_1| == 2 && (p_m_method_2_1[0] == true) && (p_m_method_2_1[1] == true) && (p_m_method_2_3 == 'n')) ==> ((ret_1 == 'S')));
{
	var v_DT_2_3_1: DT_2<int> := DT_2_3(14, 4, 4, -11);
	var v_multiset_real_DT_2_3_1: (multiset<real>, real, DT_2<int>) := (multiset{19.40}, 10.19, v_DT_2_3_1);
	var v_DT_2_1_1: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_2: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_3: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_4: DT_2<array<real>> := DT_2_1;
	var v_map_1: map<(multiset<real>, real, DT_2<int>), map<multiset<multiset<real>>, DT_2<array<real>>>> := map[v_multiset_real_DT_2_3_1 := map[multiset{multiset({4.91, 24.78, -24.86})} := v_DT_2_1_1, multiset{multiset({11.90, -10.74, 18.31}), multiset{3.06, 0.49, -3.14}, multiset{29.21, 11.58}, multiset{-8.93, -2.64, 25.63, 16.08}} := v_DT_2_1_2, multiset({multiset{}}) := v_DT_2_1_3, multiset({multiset({}), multiset{}, multiset({26.01, 5.82, -27.58}), multiset{-26.85}}) := v_DT_2_1_4]];
	var v_DT_2_3_2: DT_2<int> := DT_2_3(9, 5, 20, 12);
	var v_multiset_real_DT_2_3_2: (multiset<real>, real, DT_2<int>) := (multiset{-20.35}, 7.28, v_DT_2_3_2);
	var v_multiset_real_DT_2_3_3: (multiset<real>, real, DT_2<int>) := v_multiset_real_DT_2_3_2;
	var v_DT_2_1_5: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_6: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_7: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_8: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_9: DT_2<array<real>> := DT_2_1;
	var v_map_2: map<multiset<multiset<real>>, DT_2<array<real>>> := (if ((v_multiset_real_DT_2_3_3 in v_map_1)) then (v_map_1[v_multiset_real_DT_2_3_3]) else (map[multiset{multiset{10.05}, multiset({})} := v_DT_2_1_5, multiset{multiset({9.95, -13.57, 0.38, 16.19}), multiset({-24.90, -3.72, -6.30}), multiset{-9.62, -3.76, 1.38}, multiset({-28.63, 16.39})} := v_DT_2_1_6, multiset{} := v_DT_2_1_7, multiset{multiset{-25.10, -24.30, 13.66, -14.24}, multiset{-19.10, -0.08}, multiset{10.58}, multiset{-28.62, 29.22, 27.64}} := v_DT_2_1_8, multiset{multiset{-10.07, 21.48}} := v_DT_2_1_9]));
	var v_multiset_1: multiset<multiset<real>> := (multiset({multiset{-11.09, 26.56, -9.55, -29.77}, multiset{-21.91, -9.44}, multiset{-28.36, -27.38, -12.38, -15.13}, multiset({-17.98, 3.25, -29.01})}) * multiset{});
	var v_DT_2_1_10: DT_2<array<real>>, v_int_9: int := (if ((v_multiset_1 in v_map_2)) then (v_map_2[v_multiset_1]) else (v_DT_2_1_7)), v_DT_2_3_2.DT_2_3_2;
	var v_DT_2_1_11: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_12: DT_2<array<real>> := DT_2_1;
	var v_seq_7: seq<DT_2<array<real>>> := [v_DT_2_1_11, v_DT_2_1_12];
	var v_int_27: int := 3;
	var v_seq_21: seq<DT_2<array<real>>> := v_seq_7;
	var v_int_47: int := v_int_27;
	var v_int_48: int := safe_index_seq(v_seq_21, v_int_47);
	v_int_27 := v_int_48;
	var v_DT_2_1_13: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_14: DT_2<array<real>> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_27]) else (v_DT_2_1_13));
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_DT_1_1_3: DT_1 := (if (false) then (v_DT_1_1_1) else (v_DT_1_1_2));
	var v_bool_13: bool := (if (true) then (true) else (false));
	var v_seq_8: seq<map<int, int>> := [];
	var v_int_28: int := 21;
	var v_map_7: map<int, int> := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_28]) else (map[15 := 8]));
	var v_char_7: char := m_method_3(v_DT_2_1_14, v_DT_1_1_3, v_bool_13, v_map_7);
	var v_DT_1_2_20: DT_1 := DT_1_2(11.77, false);
	var v_DT_2_3_3: DT_2<int> := DT_2_3(9, 5, 20, 12);
	var v_multiset_real_DT_2_3_4: (multiset<real>, real, DT_2<int>) := (multiset{-20.35}, 7.28, v_DT_2_3_3);
	var v_DT_2_3_4: DT_2<int> := DT_2_3(9, 5, 20, 12);
	var v_multiset_real_DT_2_3_5: (multiset<real>, real, DT_2<int>) := (multiset{-20.35}, 7.28, v_DT_2_3_4);
	var v_DT_2_3_5: DT_2<int> := DT_2_3(14, 4, 4, -11);
	var v_multiset_real_DT_2_3_6: (multiset<real>, real, DT_2<int>) := (multiset{19.40}, 10.19, v_DT_2_3_5);
	var v_DT_2_3_6: DT_2<int> := DT_2_3(14, 4, 4, -11);
	var v_multiset_real_DT_2_3_7: (multiset<real>, real, DT_2<int>) := (multiset{19.40}, 10.19, v_DT_2_3_6);
	var v_DT_2_1_15: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_16: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_17: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_18: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_19: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_20: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_21: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_22: DT_2<array<real>> := DT_2_1;
	var v_DT_2_1_23: DT_2<array<real>> := DT_2_1;
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_multiset_real_DT_2_3_1.1", " ", (v_multiset_real_DT_2_3_1.1 == 10.19), " ", "v_multiset_real_DT_2_3_1.2", " ", v_multiset_real_DT_2_3_1.2, " ", "p_m_method_2_3", " ", (p_m_method_2_3 == 'n'), " ", "p_m_method_2_2", " ", (p_m_method_2_2 == v_DT_1_2_20), " ", "v_multiset_real_DT_2_3_1.0", " ", (v_multiset_real_DT_2_3_1.0 == multiset{19.40}), " ", "v_DT_2_3_2.DT_2_3_4", " ", v_DT_2_3_2.DT_2_3_4, " ", "v_DT_2_3_2.DT_2_3_3", " ", v_DT_2_3_2.DT_2_3_3, " ", "v_DT_2_3_2.DT_2_3_2", " ", v_DT_2_3_2.DT_2_3_2, " ", "v_DT_2_3_2.DT_2_3_1", " ", v_DT_2_3_2.DT_2_3_1, " ", "v_multiset_1", " ", (v_multiset_1 == multiset{}), " ", "v_DT_2_1_10", " ", v_DT_2_1_10, " ", "v_DT_2_1_11", " ", v_DT_2_1_11, " ", "v_DT_2_1_12", " ", v_DT_2_1_12, " ", "v_DT_2_1_13", " ", v_DT_2_1_13, " ", "v_DT_2_1_14", " ", v_DT_2_1_14, " ", "v_bool_13", " ", v_bool_13, " ", "v_DT_2_3_1.DT_2_3_2", " ", v_DT_2_3_1.DT_2_3_2, " ", "v_DT_2_3_1.DT_2_3_3", " ", v_DT_2_3_1.DT_2_3_3, " ", "v_DT_2_3_1.DT_2_3_1", " ", v_DT_2_3_1.DT_2_3_1, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "p_m_method_2_2.DT_1_2_2", " ", p_m_method_2_2.DT_1_2_2, " ", "p_m_method_2_2.DT_1_2_1", " ", (p_m_method_2_2.DT_1_2_1 == 11.77), " ", "v_DT_2_3_1.DT_2_3_4", " ", v_DT_2_3_1.DT_2_3_4, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_9", " ", v_int_9, " ", "v_multiset_real_DT_2_3_2.2", " ", v_multiset_real_DT_2_3_2.2, " ", "v_multiset_real_DT_2_3_2.0", " ", (v_multiset_real_DT_2_3_2.0 == multiset{-20.35}), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_multiset_real_DT_2_3_2.1", " ", (v_multiset_real_DT_2_3_2.1 == 7.28), " ", "v_map_7", " ", (v_map_7 == map[15 := 8]), " ", "v_multiset_real_DT_2_3_2", " ", (v_multiset_real_DT_2_3_2 == v_multiset_real_DT_2_3_4), " ", "v_multiset_real_DT_2_3_3", " ", (v_multiset_real_DT_2_3_3 == v_multiset_real_DT_2_3_5), " ", "v_char_7", " ", (v_char_7 == 'S'), " ", "v_multiset_real_DT_2_3_1", " ", (v_multiset_real_DT_2_3_1 == v_multiset_real_DT_2_3_6), " ", "v_map_1", " ", (v_map_1 == map[v_multiset_real_DT_2_3_7 := map[multiset{multiset{}} := v_DT_2_1_15, multiset{multiset{}, multiset{-26.85}, multiset{26.01, 5.82, -27.58}} := v_DT_2_1_16, multiset{multiset{25.63, -2.64, -8.93, 16.08}, multiset{11.58, 29.21}, multiset{0.49, 3.06, -3.14}, multiset{18.31, 11.90, -10.74}} := v_DT_2_1_17, multiset{multiset{24.78, 4.91, -24.86}} := v_DT_2_1_18]]), " ", "v_map_2", " ", (v_map_2 == map[multiset{} := v_DT_2_1_19, multiset{multiset{21.48, -10.07}} := v_DT_2_1_20, multiset{multiset{-14.24, 13.66, -25.10, -24.30}, multiset{-28.62, 29.22, 27.64}, multiset{10.58}, multiset{-0.08, -19.10}} := v_DT_2_1_21, multiset{multiset{-13.57, 0.38, 16.19, 9.95}, multiset{-3.72, -6.30, -24.90}, multiset{1.38, -3.76, -9.62}, multiset{16.39, -28.63}} := v_DT_2_1_22, multiset{multiset{}, multiset{10.05}} := v_DT_2_1_23]), " ", "v_DT_2_1_4", " ", v_DT_2_1_4, " ", "v_DT_2_3_2", " ", v_DT_2_3_2, " ", "v_seq_8", " ", (v_seq_8 == []), " ", "v_DT_2_3_1", " ", v_DT_2_3_1, " ", "v_DT_2_1_3", " ", v_DT_2_1_3, " ", "v_seq_7", " ", v_seq_7, " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_DT_2_1_8", " ", v_DT_2_1_8, " ", "v_DT_2_1_7", " ", v_DT_2_1_7, " ", "v_DT_2_1_6", " ", v_DT_2_1_6, " ", "v_DT_2_1_5", " ", v_DT_2_1_5, " ", "v_DT_2_1_9", " ", v_DT_2_1_9, "\n";
	return v_char_7;
}

method m_method_1(p_m_method_1_1: int) returns (ret_1: int)
	requires ((p_m_method_1_1 == -12));
	ensures (((p_m_method_1_1 == -12)) ==> ((ret_1 == -12)));
{
	assert ((p_m_method_1_1 == -12));
	expect ((p_m_method_1_1 == -12));
	print "p_m_method_1_1", " ", p_m_method_1_1, "\n";
	return p_m_method_1_1;
}

method m_method_10(p_m_method_10_1: bool) returns (ret_1: bool)
	requires ((p_m_method_10_1 == true));
	ensures (((p_m_method_10_1 == true)) ==> ((ret_1 == true)));
{
	var v_bool_23: bool := false;
	var v_bool_24: bool := true;
	var v_bool_25: bool := true;
	var v_bool_26: bool := true;
	var v_bool_27: bool := m_method_8(v_bool_23, v_bool_24, v_bool_25, v_bool_26);
	print "v_bool_26", " ", v_bool_26, " ", "v_bool_27", " ", v_bool_27, " ", "v_bool_24", " ", v_bool_24, " ", "v_bool_25", " ", v_bool_25, " ", "v_bool_23", " ", v_bool_23, " ", "p_m_method_10_1", " ", p_m_method_10_1, "\n";
	return v_bool_27;
}

method Main() returns ()
{
	var v_int_7: int := ((19 / 16) + -13);
	var v_int_8: int := m_method_1(v_int_7);
	var v_bool_14: bool := false;
	var v_bool_15: bool := false;
	var v_seq_9: seq<bool> := m_method_7(v_bool_14, v_bool_15);
	var v_seq_10: seq<bool> := v_seq_9;
	var v_seq_11: seq<bool> := v_seq_10;
	var v_int_29: int := 22;
	var v_int_30: int := 13;
	var v_int_31: int := safe_modulus(v_int_29, v_int_30);
	var v_int_32: int := v_int_31;
	var v_int_33: int := safe_index_seq(v_seq_11, v_int_32);
	var v_int_34: int := v_int_33;
	var v_bool_16: bool := true;
	var v_bool_17: bool := false;
	var v_bool_18: bool := true;
	var v_bool_19: bool := false;
	var v_bool_20: bool := m_method_8(v_bool_16, v_bool_17, v_bool_18, v_bool_19);
	var v_seq_16: seq<bool> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_34 := v_bool_20]) else (v_seq_10));
	var v_DT_1_2_9: DT_1 := DT_1_2(11.77, false);
	var v_DT_1_2_10: DT_1 := DT_1_2(-6.40, false);
	var v_seq_12: seq<seq<DT_1>> := [[v_DT_1_2_9, v_DT_1_2_10]];
	var v_int_35: int := 5;
	var v_seq_18: seq<seq<DT_1>> := v_seq_12;
	var v_int_41: int := v_int_35;
	var v_int_42: int := safe_index_seq(v_seq_18, v_int_41);
	v_int_35 := v_int_42;
	var v_DT_1_2_11: DT_1 := DT_1_2(17.88, false);
	var v_DT_1_2_12: DT_1 := DT_1_2(0.68, false);
	var v_DT_1_2_13: DT_1 := DT_1_2(-22.74, false);
	var v_seq_13: seq<DT_1> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_35]) else ([v_DT_1_2_11, v_DT_1_2_12, v_DT_1_2_13]));
	var v_int_36: int := v_int_30;
	var v_seq_19: seq<DT_1> := v_seq_13;
	var v_int_43: int := v_int_36;
	var v_int_44: int := safe_index_seq(v_seq_19, v_int_43);
	v_int_36 := v_int_44;
	var v_DT_1_2_14: DT_1 := DT_1_2(20.55, false);
	var v_DT_1_2_15: DT_1 := DT_1_2(14.58, false);
	var v_DT_1_2_16: DT_1 := DT_1_2(-26.61, false);
	var v_DT_1_2_17: DT_1 := DT_1_2(-1.88, true);
	var v_seq_14: seq<DT_1> := [v_DT_1_2_14, v_DT_1_2_15, v_DT_1_2_16, v_DT_1_2_17];
	var v_int_37: int := 4;
	var v_DT_1_2_18: DT_1 := DT_1_2(-17.80, false);
	var v_DT_1_2_19: DT_1 := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_36]) else ((if ((|v_seq_14| > 0)) then (v_seq_14[v_int_37]) else (v_DT_1_2_18))));
	var v_bool_21: bool := v_DT_1_2_12.DT_1_2_2;
	var v_bool_22: bool := v_DT_1_2_9.DT_1_2_2;
	var v_char_8: char := m_method_9(v_bool_21, v_bool_22);
	var v_char_9: char := v_char_8;
	var v_char_10: char := m_method_2(v_seq_16, v_DT_1_2_19, v_char_9);
	v_int_34, v_char_10, v_char_9 := v_int_8, v_char_10, v_char_10;
	var v_bool_28: bool := (false || true);
	var v_bool_29: bool := m_method_10(v_bool_28);
	var v_seq_17: seq<bool> := [true];
	var v_int_39: int := 15;
	var v_int_40: int := safe_index_seq(v_seq_17, v_int_39);
	v_bool_17, v_bool_29, v_bool_19 := (if (v_DT_1_2_15.DT_1_2_2) then (v_bool_29) else ((v_int_40 < (if (true) then (15) else (20))))), v_bool_28, v_bool_21;
	var v_DT_1_2_21: DT_1 := DT_1_2(11.77, false);
	var v_DT_1_2_22: DT_1 := DT_1_2(11.77, false);
	var v_DT_1_2_23: DT_1 := DT_1_2(-17.80, false);
	var v_DT_1_2_24: DT_1 := DT_1_2(-22.74, false);
	var v_DT_1_2_25: DT_1 := DT_1_2(0.68, false);
	var v_DT_1_2_26: DT_1 := DT_1_2(17.88, false);
	var v_DT_1_2_27: DT_1 := DT_1_2(-6.40, false);
	var v_DT_1_2_28: DT_1 := DT_1_2(-1.88, true);
	var v_DT_1_2_29: DT_1 := DT_1_2(-26.61, false);
	var v_DT_1_2_30: DT_1 := DT_1_2(14.58, false);
	var v_DT_1_2_31: DT_1 := DT_1_2(20.55, false);
	var v_DT_1_2_32: DT_1 := DT_1_2(20.55, false);
	var v_DT_1_2_33: DT_1 := DT_1_2(14.58, false);
	var v_DT_1_2_34: DT_1 := DT_1_2(-26.61, false);
	var v_DT_1_2_35: DT_1 := DT_1_2(-1.88, true);
	var v_DT_1_2_36: DT_1 := DT_1_2(11.77, false);
	var v_DT_1_2_37: DT_1 := DT_1_2(-6.40, false);
	var v_DT_1_2_38: DT_1 := DT_1_2(11.77, false);
	var v_DT_1_2_39: DT_1 := DT_1_2(-6.40, false);
	print "v_bool_28", " ", v_bool_28, " ", "v_bool_29", " ", v_bool_29, " ", "v_DT_1_2_16.DT_1_2_1", " ", (v_DT_1_2_16.DT_1_2_1 == -26.61), " ", "v_DT_1_2_9", " ", (v_DT_1_2_9 == v_DT_1_2_21), " ", "v_DT_1_2_16.DT_1_2_2", " ", v_DT_1_2_16.DT_1_2_2, " ", "v_DT_1_2_10.DT_1_2_2", " ", v_DT_1_2_10.DT_1_2_2, " ", "v_DT_1_2_10.DT_1_2_1", " ", (v_DT_1_2_10.DT_1_2_1 == -6.40), " ", "v_bool_22", " ", v_bool_22, " ", "v_bool_20", " ", v_bool_20, " ", "v_bool_21", " ", v_bool_21, " ", "v_DT_1_2_13.DT_1_2_1", " ", (v_DT_1_2_13.DT_1_2_1 == -22.74), " ", "v_int_40", " ", v_int_40, " ", "v_DT_1_2_13.DT_1_2_2", " ", v_DT_1_2_13.DT_1_2_2, " ", "v_bool_19", " ", v_bool_19, " ", "v_bool_17", " ", v_bool_17, " ", "v_bool_18", " ", v_bool_18, " ", "v_bool_15", " ", v_bool_15, " ", "v_bool_16", " ", v_bool_16, " ", "v_int_29", " ", v_int_29, " ", "v_DT_1_2_11.DT_1_2_2", " ", v_DT_1_2_11.DT_1_2_2, " ", "v_DT_1_2_11.DT_1_2_1", " ", (v_DT_1_2_11.DT_1_2_1 == 17.88), " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_DT_1_2_12.DT_1_2_1", " ", (v_DT_1_2_12.DT_1_2_1 == 0.68), " ", "v_int_33", " ", v_int_33, " ", "v_DT_1_2_19", " ", (v_DT_1_2_19 == v_DT_1_2_22), " ", "v_int_32", " ", v_int_32, " ", "v_DT_1_2_18", " ", (v_DT_1_2_18 == v_DT_1_2_23), " ", "v_int_39", " ", v_int_39, " ", "v_DT_1_2_12.DT_1_2_2", " ", v_DT_1_2_12.DT_1_2_2, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_DT_1_2_13", " ", (v_DT_1_2_13 == v_DT_1_2_24), " ", "v_bool_14", " ", v_bool_14, " ", "v_DT_1_2_12", " ", (v_DT_1_2_12 == v_DT_1_2_25), " ", "v_DT_1_2_11", " ", (v_DT_1_2_11 == v_DT_1_2_26), " ", "v_DT_1_2_10", " ", (v_DT_1_2_10 == v_DT_1_2_27), " ", "v_int_31", " ", v_int_31, " ", "v_DT_1_2_17", " ", (v_DT_1_2_17 == v_DT_1_2_28), " ", "v_int_30", " ", v_int_30, " ", "v_DT_1_2_16", " ", (v_DT_1_2_16 == v_DT_1_2_29), " ", "v_DT_1_2_15", " ", (v_DT_1_2_15 == v_DT_1_2_30), " ", "v_DT_1_2_17.DT_1_2_2", " ", v_DT_1_2_17.DT_1_2_2, " ", "v_DT_1_2_14", " ", (v_DT_1_2_14 == v_DT_1_2_31), " ", "v_DT_1_2_17.DT_1_2_1", " ", (v_DT_1_2_17.DT_1_2_1 == -1.88), " ", "v_DT_1_2_9.DT_1_2_1", " ", (v_DT_1_2_9.DT_1_2_1 == 11.77), " ", "v_DT_1_2_9.DT_1_2_2", " ", v_DT_1_2_9.DT_1_2_2, " ", "v_DT_1_2_15.DT_1_2_1", " ", (v_DT_1_2_15.DT_1_2_1 == 14.58), " ", "v_DT_1_2_15.DT_1_2_2", " ", v_DT_1_2_15.DT_1_2_2, " ", "v_seq_14", " ", (v_seq_14 == [v_DT_1_2_32, v_DT_1_2_33, v_DT_1_2_34, v_DT_1_2_35]), " ", "v_seq_16", " ", v_seq_16, " ", "v_seq_17", " ", v_seq_17, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", v_seq_11, " ", "v_DT_1_2_18.DT_1_2_2", " ", v_DT_1_2_18.DT_1_2_2, " ", "v_seq_12", " ", (v_seq_12 == [[v_DT_1_2_36, v_DT_1_2_37]]), " ", "v_DT_1_2_18.DT_1_2_1", " ", (v_DT_1_2_18.DT_1_2_1 == -17.80), " ", "v_seq_13", " ", (v_seq_13 == [v_DT_1_2_38, v_DT_1_2_39]), " ", "v_DT_1_2_14.DT_1_2_1", " ", (v_DT_1_2_14.DT_1_2_1 == 20.55), " ", "v_DT_1_2_14.DT_1_2_2", " ", v_DT_1_2_14.DT_1_2_2, " ", "v_int_8", " ", v_int_8, " ", "v_char_9", " ", (v_char_9 == 'S'), " ", "v_int_7", " ", v_int_7, " ", "v_char_8", " ", (v_char_8 == 'n'), " ", "v_seq_9", " ", v_seq_9, " ", "v_char_10", " ", (v_char_10 == 'S'), "\n";
	return ;
}
