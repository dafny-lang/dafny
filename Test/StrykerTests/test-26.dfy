// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1
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

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char) returns (ret_1: char)
	requires ((p_m_method_4_2 == 'z') && (p_m_method_4_1 == 'w')) || ((p_m_method_4_2 == 'B') && (p_m_method_4_1 == 'Q')) || ((p_m_method_4_2 == 'a') && (p_m_method_4_1 == 'e'));
	ensures (((p_m_method_4_2 == 'a') && (p_m_method_4_1 == 'e')) ==> ((ret_1 == 's'))) && (((p_m_method_4_2 == 'B') && (p_m_method_4_1 == 'Q')) ==> ((ret_1 == 's'))) && (((p_m_method_4_2 == 'z') && (p_m_method_4_1 == 'w')) ==> ((ret_1 == 's')));
{
	var v_seq_7: seq<char> := ['s'];
	var v_int_12: int := 5;
	var v_seq_25: seq<char> := v_seq_7;
	var v_int_42: int := v_int_12;
	var v_int_43: int := safe_index_seq(v_seq_25, v_int_42);
	v_int_12 := v_int_43;
	print "v_seq_7", " ", (v_seq_7 == ['s']), " ", "v_int_12", " ", v_int_12, " ", "p_m_method_4_1", " ", (p_m_method_4_1 == 'Q'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'B'), "\n";
	return (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_12]) else ('R'));
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char, p_m_method_3_4: char) returns (ret_1: bool)
	requires ((p_m_method_3_1 == 'b') && (p_m_method_3_3 == 'o') && (p_m_method_3_2 == 'E') && (p_m_method_3_4 == 'j')) || ((p_m_method_3_1 == 'I') && (p_m_method_3_3 == 'H') && (p_m_method_3_2 == 'U') && (p_m_method_3_4 == 's')) || ((p_m_method_3_1 == 'Q') && (p_m_method_3_3 == 'n') && (p_m_method_3_2 == 'H') && (p_m_method_3_4 == 'a'));
	ensures (((p_m_method_3_1 == 'b') && (p_m_method_3_3 == 'o') && (p_m_method_3_2 == 'E') && (p_m_method_3_4 == 'j')) ==> ((ret_1 == true))) && (((p_m_method_3_1 == 'Q') && (p_m_method_3_3 == 'n') && (p_m_method_3_2 == 'H') && (p_m_method_3_4 == 'a')) ==> ((ret_1 == true))) && (((p_m_method_3_1 == 'I') && (p_m_method_3_3 == 'H') && (p_m_method_3_2 == 'U') && (p_m_method_3_4 == 's')) ==> ((ret_1 == true)));
{
	print "p_m_method_3_2", " ", (p_m_method_3_2 == 'U'), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'I'), " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 's'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'H'), "\n";
	return true;
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

method m_method_2(p_m_method_2_1: bool, p_m_method_2_2: DT_1<int, int>, p_m_method_2_3: int, p_m_method_2_4: int) returns (ret_1: seq<bool>)
	requires ((p_m_method_2_2.DT_1_1? && ((p_m_method_2_2 == DT_1_1))) && (p_m_method_2_1 == false) && (p_m_method_2_4 == 2) && (p_m_method_2_3 == 9));
	ensures (((p_m_method_2_2.DT_1_1? && ((p_m_method_2_2 == DT_1_1))) && (p_m_method_2_1 == false) && (p_m_method_2_4 == 2) && (p_m_method_2_3 == 9)) ==> (|ret_1| == 2 && (ret_1[0] == true) && (ret_1[1] == false)));
{
	var v_bool_1: bool, v_char_1: char, v_char_2: char := false, 'a', 'I';
	print "v_bool_1", " ", v_bool_1, " ", "v_char_1", " ", (v_char_1 == 'a'), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_char_2", " ", (v_char_2 == 'I'), " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", p_m_method_2_2, " ", "p_m_method_2_4", " ", p_m_method_2_4, "\n";
	return [true, false];
}

method m_method_1(p_m_method_1_1: array<real>, p_m_method_1_2: char) returns (ret_1: char, ret_2: int, ret_3: int)
	requires (p_m_method_1_1.Length == 5 && (-22.82 < p_m_method_1_1[0] < -22.62) && (2.57 < p_m_method_1_1[1] < 2.77) && (-7.16 < p_m_method_1_1[2] < -6.96) && (4.25 < p_m_method_1_1[3] < 4.45) && (19.91 < p_m_method_1_1[4] < 20.11) && (p_m_method_1_2 == 'W'));
	ensures ((p_m_method_1_1.Length == 5 && (-22.82 < p_m_method_1_1[0] < -22.62) && (2.57 < p_m_method_1_1[1] < 2.77) && (-7.16 < p_m_method_1_1[2] < -6.96) && (4.25 < p_m_method_1_1[3] < 4.45) && (19.91 < p_m_method_1_1[4] < 20.11) && (p_m_method_1_2 == 'W')) ==> ((ret_1 == 's') && (ret_2 == 3) && (ret_3 == 2)));
{
	var v_bool_2: bool := false;
	var v_DT_1_1_1: DT_1<int, int> := DT_1_1;
	var v_DT_1_1_2: DT_1<int, int> := v_DT_1_1_1;
	var v_int_7: int := 9;
	var v_int_8: int := 2;
	var v_seq_3: seq<bool> := m_method_2(v_bool_2, v_DT_1_1_2, v_int_7, v_int_8);
	var v_seq_4: seq<bool> := v_seq_3;
	var v_int_9: int := -17;
	var v_seq_27: seq<bool> := v_seq_4;
	var v_int_46: int := v_int_9;
	var v_int_47: int := safe_index_seq(v_seq_27, v_int_46);
	v_int_9 := v_int_47;
	var v_seq_5: seq<bool> := v_seq_3;
	var v_int_10: int := 24;
	var v_seq_28: seq<bool> := v_seq_5;
	var v_int_48: int := v_int_10;
	var v_int_49: int := safe_index_seq(v_seq_28, v_int_48);
	v_int_10 := v_int_49;
	var v_char_3: char := 'b';
	var v_char_4: char := 'E';
	var v_char_5: char := 'o';
	var v_char_6: char := 'j';
	var v_bool_3: bool := m_method_3(v_char_3, v_char_4, v_char_5, v_char_6);
	var v_char_7: char := 'Q';
	var v_char_8: char := 'H';
	var v_char_9: char := 'n';
	var v_char_10: char := 'a';
	var v_bool_4: bool := m_method_3(v_char_7, v_char_8, v_char_9, v_char_10);
	var v_bool_bool_int_1: (bool, bool, int) := (false, false, 10);
	var v_multiset_bool_bool_int_int_1: (multiset<real>, (bool, bool, int), int) := (multiset{-21.08}, v_bool_bool_int_1, 9);
	var v_bool_bool_int_2: (bool, bool, int) := (false, false, 26);
	var v_multiset_bool_bool_int_int_2: (multiset<real>, (bool, bool, int), int) := (multiset{-11.69}, v_bool_bool_int_2, 5);
	var v_map_1: map<char, (multiset<real>, (bool, bool, int), int)> := (map['s' := v_multiset_bool_bool_int_int_1, 'J' := v_multiset_bool_bool_int_int_2] - ({'l'} * {'r', 'G'}));
	var v_char_11: char := v_char_6;
	var v_map_2: map<char, multiset<char>> := map['X' := multiset({'J'}), 'H' := multiset{'F', 'P'}, 'C' := multiset{'Y'}, 'a' := multiset({'q', 'd'})];
	var v_char_12: char := 'W';
	var v_array_1: array<real> := new real[3] [21.29, -25.72, -12.99];
	var v_int_array_map_1: (int, array<real>, map<real, bool>) := (5, v_array_1, map[-26.03 := true, -5.04 := false, 5.37 := true]);
	var v_array_2: array<real> := new real[5] [-16.70, -29.70, -18.16, -5.68, 26.04];
	var v_int_array_map_2: (int, array<real>, map<real, bool>) := (20, v_array_2, map[3.31 := true, 19.70 := false, 0.41 := false, -6.44 := true, -14.91 := true]);
	var v_array_3: array<real> := new real[3] [-7.21, 24.72, -8.94];
	var v_int_array_map_3: (int, array<real>, map<real, bool>) := (26, v_array_3, map[-11.30 := false, 20.60 := true]);
	var v_array_4: array<real> := new real[5] [-11.00, -1.76, -7.65, -18.49, -19.29];
	var v_int_array_map_4: (int, array<real>, map<real, bool>) := (18, v_array_4, map[-2.26 := true, -5.51 := false, -10.34 := true, -7.39 := true, 20.14 := true]);
	var v_array_5: array<real> := new real[3] [-9.35, 7.32, 5.07];
	var v_int_array_map_5: (int, array<real>, map<real, bool>) := (22, v_array_5, map[-20.16 := true]);
	var v_array_6: array<real> := new real[3] [24.65, -27.01, 24.15];
	var v_int_array_map_6: (int, array<real>, map<real, bool>) := (13, v_array_6, map[11.45 := true, 12.32 := true, 4.61 := false]);
	var v_array_7: array<real> := new real[3] [-6.98, -26.12, 28.31];
	var v_int_array_map_7: (int, array<real>, map<real, bool>) := (21, v_array_7, map[17.11 := true, 28.93 := false, -27.97 := false]);
	var v_seq_6: seq<map<char, (int, array<real>, map<real, bool>)>> := [map['w' := v_int_array_map_1, 'r' := v_int_array_map_2, 'G' := v_int_array_map_3], map['b' := v_int_array_map_4, 'A' := v_int_array_map_6, 'H' := v_int_array_map_7]];
	var v_int_11: int := -28;
	var v_seq_26: seq<map<char, (int, array<real>, map<real, bool>)>> := v_seq_6;
	var v_int_44: int := v_int_11;
	var v_int_45: int := safe_index_seq(v_seq_26, v_int_44);
	v_int_11 := v_int_45;
	var v_array_8: array<real> := new real[3] [-2.41, 14.68, -0.49];
	var v_int_array_map_8: (int, array<real>, map<real, bool>) := (5, v_array_8, map[13.17 := false, 7.44 := false, -29.65 := false]);
	var v_array_9: array<real> := new real[5] [4.68, 7.22, -1.35, 26.26, 12.18];
	var v_int_array_map_9: (int, array<real>, map<real, bool>) := (24, v_array_9, map[-3.42 := true, 2.91 := true, -7.36 := false]);
	var v_array_10: array<real> := new real[5];
	v_array_10[0] := 17.70;
	v_array_10[1] := 18.89;
	v_array_10[2] := 0.67;
	v_array_10[3] := 1.82;
	v_array_10[4] := 7.38;
	var v_int_array_map_10: (int, array<real>, map<real, bool>) := (17, v_array_10, map[28.41 := true, -8.97 := true]);
	var v_array_11: array<real> := new real[5] [24.02, -29.70, -28.52, 25.29, -11.51];
	var v_int_array_map_11: (int, array<real>, map<real, bool>) := (1, v_array_11, map[-17.83 := true, -3.75 := true, -23.42 := true]);
	var v_array_12: array<real> := new real[5] [-28.07, -20.92, 25.07, 29.49, -11.44];
	var v_int_array_map_12: (int, array<real>, map<real, bool>) := (20, v_array_12, map[-7.48 := false, 11.04 := true, -6.67 := false]);
	var v_array_13: array<real> := new real[3] [-18.90, 22.43, 21.16];
	var v_int_array_map_13: (int, array<real>, map<real, bool>) := (27, v_array_13, map[21.04 := false]);
	var v_array_14: array<real> := new real[5] [-14.05, -13.34, -29.23, 15.65, 21.93];
	var v_int_array_map_14: (int, array<real>, map<real, bool>) := (0, v_array_14, map[22.17 := false, -19.65 := true, 12.28 := false]);
	var v_array_15: array<real> := new real[3] [-5.85, -22.72, -28.04];
	var v_int_array_map_15: (int, array<real>, map<real, bool>) := (26, v_array_15, map[29.41 := true, -5.77 := true, 13.98 := false]);
	var v_map_3: map<char, (int, array<real>, map<real, bool>)> := ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_11]) else (map['S' := v_int_array_map_8, 'U' := v_int_array_map_9, 'W' := v_int_array_map_10, 'E' := v_int_array_map_11, 'm' := v_int_array_map_12])) + map['G' := v_int_array_map_13, 'e' := v_int_array_map_14]['J' := v_int_array_map_15]);
	var v_char_13: char := (match 'z' {
		case 'K' => 'e'
		case _ => 'e'
	});
	var v_char_14: char := v_char_10;
	var v_char_15: char := m_method_4(v_char_13, v_char_14);
	var v_char_16: char := v_char_15;
	var v_bool_5: bool, v_multiset_bool_bool_int_int_3: (multiset<real>, (bool, bool, int), int), v_multiset_1: multiset<char>, v_int_array_map_16: (int, array<real>, map<real, bool>), v_char_17: char := (if ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_9]) else (v_bool_2))) then ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_10]) else (v_bool_3))) else ((if (v_bool_4) then (v_bool_2) else (v_bool_4)))), (if ((v_char_11 in v_map_1)) then (v_map_1[v_char_11]) else (v_multiset_bool_bool_int_int_2)), (match 'I' {
		case 'Q' => multiset{}
		case _ => ((multiset({'r', 'H'}) - multiset({'n', 'P', 't', 't'})) - (if ((v_char_12 in v_map_2)) then (v_map_2[v_char_12]) else (multiset{'j', 'N', 'D', 'y'})))
	}), (if ((v_char_16 in v_map_3)) then (v_map_3[v_char_16]) else (v_int_array_map_7)), v_char_15;
	var v_map_4: map<char, char> := (map['Z' := 'h', 'a' := 'V', 'H' := 'x', 'Q' := 'O']['k' := 'X'] + (map['R' := 'T', 'u' := 'd', 'K' := 'h', 'v' := 'R', 'x' := 'J'] - {'N', 'U', 'L'}));
	var v_char_18: char := 'w';
	var v_char_19: char := 'z';
	var v_char_20: char := m_method_4(v_char_18, v_char_19);
	var v_char_21: char := (if ((false && true)) then (v_char_20) else ((match 'm' {
		case 'k' => 'V'
		case 'r' => 'L'
		case _ => 'S'
	})));
	var v_int_13: int := (if (true) then (18) else (0));
	var v_int_14: int := v_int_array_map_5.0;
	var v_int_15: int := safe_modulus(v_int_13, v_int_14);
	var v_int_array_map_17: (int, array<real>, map<real, bool>) := (0, v_array_14, map[12.28 := false, 22.17 := false, -19.65 := true]);
	var v_int_array_map_18: (int, array<real>, map<real, bool>) := (27, v_array_13, map[21.04 := false]);
	var v_int_array_map_19: (int, array<real>, map<real, bool>) := (21, v_array_7, map[17.11 := true, 28.93 := false, -27.97 := false]);
	var v_int_array_map_20: (int, array<real>, map<real, bool>) := (26, v_array_15, map[13.98 := false, -5.77 := true, 29.41 := true]);
	var v_int_array_map_21: (int, array<real>, map<real, bool>) := (17, v_array_10, map[-8.97 := true, 28.41 := true]);
	var v_int_array_map_22: (int, array<real>, map<real, bool>) := (20, v_array_12, map[-6.67 := false, -7.48 := false, 11.04 := true]);
	var v_int_array_map_23: (int, array<real>, map<real, bool>) := (1, v_array_11, map[-17.83 := true, -3.75 := true, -23.42 := true]);
	var v_bool_bool_int_3: (bool, bool, int) := (false, false, 26);
	var v_multiset_bool_bool_int_int_4: (multiset<real>, (bool, bool, int), int) := (multiset{-11.69}, v_bool_bool_int_3, 5);
	var v_bool_bool_int_4: (bool, bool, int) := (false, false, 10);
	var v_multiset_bool_bool_int_int_5: (multiset<real>, (bool, bool, int), int) := (multiset{-21.08}, v_bool_bool_int_4, 9);
	var v_bool_bool_int_5: (bool, bool, int) := (false, false, 26);
	var v_multiset_bool_bool_int_int_6: (multiset<real>, (bool, bool, int), int) := (multiset{-11.69}, v_bool_bool_int_5, 5);
	var v_bool_bool_int_6: (bool, bool, int) := (false, false, 10);
	var v_multiset_bool_bool_int_int_7: (multiset<real>, (bool, bool, int), int) := (multiset{-21.08}, v_bool_bool_int_6, 9);
	var v_bool_bool_int_7: (bool, bool, int) := (false, false, 26);
	var v_multiset_bool_bool_int_int_8: (multiset<real>, (bool, bool, int), int) := (multiset{-11.69}, v_bool_bool_int_7, 5);
	var v_int_array_map_24: (int, array<real>, map<real, bool>) := (20, v_array_2, map[19.70 := false, -14.91 := true, -6.44 := true, 0.41 := false, 3.31 := true]);
	var v_int_array_map_25: (int, array<real>, map<real, bool>) := (0, v_array_14, map[12.28 := false, 22.17 := false, -19.65 := true]);
	var v_int_array_map_26: (int, array<real>, map<real, bool>) := (5, v_array_1, map[-26.03 := true, 5.37 := true, -5.04 := false]);
	var v_int_array_map_27: (int, array<real>, map<real, bool>) := (27, v_array_13, map[21.04 := false]);
	var v_int_array_map_28: (int, array<real>, map<real, bool>) := (26, v_array_15, map[13.98 := false, -5.77 := true, 29.41 := true]);
	var v_int_array_map_29: (int, array<real>, map<real, bool>) := (5, v_array_1, map[-26.03 := true, 5.37 := true, -5.04 := false]);
	var v_int_array_map_30: (int, array<real>, map<real, bool>) := (24, v_array_9, map[2.91 := true, -3.42 := true, -7.36 := false]);
	var v_int_array_map_31: (int, array<real>, map<real, bool>) := (5, v_array_8, map[13.17 := false, -29.65 := false, 7.44 := false]);
	var v_int_array_map_32: (int, array<real>, map<real, bool>) := (21, v_array_7, map[17.11 := true, 28.93 := false, -27.97 := false]);
	var v_int_array_map_33: (int, array<real>, map<real, bool>) := (13, v_array_6, map[12.32 := true, 11.45 := true, 4.61 := false]);
	var v_int_array_map_34: (int, array<real>, map<real, bool>) := (22, v_array_5, map[-20.16 := true]);
	var v_int_array_map_35: (int, array<real>, map<real, bool>) := (18, v_array_4, map[-5.51 := false, -10.34 := true, 20.14 := true, -7.39 := true, -2.26 := true]);
	var v_int_array_map_36: (int, array<real>, map<real, bool>) := (26, v_array_3, map[-11.30 := false, 20.60 := true]);
	var v_int_array_map_37: (int, array<real>, map<real, bool>) := (20, v_array_2, map[19.70 := false, -14.91 := true, -6.44 := true, 0.41 := false, 3.31 := true]);
	var v_int_array_map_38: (int, array<real>, map<real, bool>) := (20, v_array_2, map[19.70 := false, -14.91 := true, -6.44 := true, 0.41 := false, 3.31 := true]);
	var v_int_array_map_39: (int, array<real>, map<real, bool>) := (5, v_array_1, map[-26.03 := true, 5.37 := true, -5.04 := false]);
	var v_int_array_map_40: (int, array<real>, map<real, bool>) := (26, v_array_3, map[-11.30 := false, 20.60 := true]);
	var v_int_array_map_41: (int, array<real>, map<real, bool>) := (13, v_array_6, map[12.32 := true, 11.45 := true, 4.61 := false]);
	var v_int_array_map_42: (int, array<real>, map<real, bool>) := (18, v_array_4, map[-5.51 := false, -10.34 := true, 20.14 := true, -7.39 := true, -2.26 := true]);
	var v_int_array_map_43: (int, array<real>, map<real, bool>) := (21, v_array_7, map[17.11 := true, 28.93 := false, -27.97 := false]);
	print "v_array_14[1]", " ", (v_array_14[1] == -13.34), " ", "v_array_3[0]", " ", (v_array_3[0] == -7.21), " ", "v_array_9[0]", " ", (v_array_9[0] == 4.68), " ", "v_array_2[3]", " ", (v_array_2[3] == -5.68), " ", "v_multiset_bool_bool_int_int_2.0", " ", (v_multiset_bool_bool_int_int_2.0 == multiset{-11.69}), " ", "v_bool_bool_int_2", " ", v_bool_bool_int_2, " ", "v_bool_bool_int_1", " ", v_bool_bool_int_1, " ", "v_array_14[0]", " ", (v_array_14[0] == -14.05), " ", "v_int_array_map_8.2", " ", (v_int_array_map_8.2 == map[13.17 := false, -29.65 := false, 7.44 := false]), " ", "v_multiset_bool_bool_int_int_2.1", " ", v_multiset_bool_bool_int_int_2.1, " ", "v_int_array_map_8.1", " ", (v_int_array_map_8.1 == v_array_8), " ", "v_multiset_bool_bool_int_int_2.2", " ", v_multiset_bool_bool_int_int_2.2, " ", "v_int_array_map_8.0", " ", v_int_array_map_8.0, " ", "v_int_array_map_14", " ", (v_int_array_map_14 == v_int_array_map_17), " ", "v_int_array_map_15.1", " ", (v_int_array_map_15.1 == v_array_15), " ", "v_int_array_map_13", " ", (v_int_array_map_13 == v_int_array_map_18), " ", "v_int_array_map_15.0", " ", v_int_array_map_15.0, " ", "v_int_array_map_16", " ", (v_int_array_map_16 == v_int_array_map_19), " ", "v_int_array_map_15", " ", (v_int_array_map_15 == v_int_array_map_20), " ", "v_int_array_map_15.2", " ", (v_int_array_map_15.2 == map[13.98 := false, -5.77 := true, 29.41 := true]), " ", "v_int_array_map_10", " ", (v_int_array_map_10 == v_int_array_map_21), " ", "v_int_array_map_12", " ", (v_int_array_map_12 == v_int_array_map_22), " ", "v_int_array_map_11", " ", (v_int_array_map_11 == v_int_array_map_23), " ", "v_array_2[4]", " ", (v_array_2[4] == 26.04), " ", "v_array_8[2]", " ", (v_array_8[2] == -0.49), " ", "v_array_3[1]", " ", (v_array_3[1] == 24.72), " ", "v_array_14[3]", " ", (v_array_14[3] == 15.65), " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_array_15[0]", " ", (v_array_15[0] == -5.85), " ", "v_array_2[1]", " ", (v_array_2[1] == -29.70), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_array_8[1]", " ", (v_array_8[1] == 14.68), " ", "v_int_array_map_1.2", " ", (v_int_array_map_1.2 == map[-26.03 := true, 5.37 := true, -5.04 := false]), " ", "v_int_array_map_1.1", " ", (v_int_array_map_1.1 == v_array_1), " ", "v_int_array_map_1.0", " ", v_int_array_map_1.0, " ", "v_array_14[2]", " ", (v_array_14[2] == -29.23), " ", "v_int_array_map_9.2", " ", (v_int_array_map_9.2 == map[2.91 := true, -3.42 := true, -7.36 := false]), " ", "v_int_array_map_9.1", " ", (v_int_array_map_9.1 == v_array_9), " ", "v_int_array_map_9.0", " ", v_int_array_map_9.0, " ", "v_array_2[2]", " ", (v_array_2[2] == -18.16), " ", "v_array_8[0]", " ", (v_array_8[0] == -2.41), " ", "v_array_15[2]", " ", (v_array_15[2] == -28.04), " ", "v_array_10[1]", " ", (v_array_10[1] == 18.89), " ", "v_array_9[4]", " ", (v_array_9[4] == 12.18), " ", "v_array_4[1]", " ", (v_array_4[1] == -1.76), " ", "v_array_14[4]", " ", (v_array_14[4] == 21.93), " ", "v_int_array_map_2.2", " ", (v_int_array_map_2.2 == map[19.70 := false, -14.91 := true, -6.44 := true, 0.41 := false, 3.31 := true]), " ", "v_int_array_map_2.1", " ", (v_int_array_map_2.1 == v_array_2), " ", "v_int_array_map_2.0", " ", v_int_array_map_2.0, " ", "v_array_15[1]", " ", (v_array_15[1] == -22.72), " ", "v_array_10[0]", " ", (v_array_10[0] == 17.70), " ", "v_array_9[3]", " ", (v_array_9[3] == 26.26), " ", "v_array_4[2]", " ", (v_array_4[2] == -7.65), " ", "v_char_18", " ", (v_char_18 == 'w'), " ", "v_char_17", " ", (v_char_17 == 's'), " ", "v_bool_3", " ", v_bool_3, " ", "v_char_16", " ", (v_char_16 == 's'), " ", "v_bool_2", " ", v_bool_2, " ", "v_char_15", " ", (v_char_15 == 's'), " ", "v_char_14", " ", (v_char_14 == 'a'), " ", "v_char_13", " ", (v_char_13 == 'e'), " ", "v_char_11", " ", (v_char_11 == 'j'), " ", "v_array_10[3]", " ", (v_array_10[3] == 1.82), " ", "v_array_11[0]", " ", (v_array_11[0] == 24.02), " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_char_19", " ", (v_char_19 == 'z'), " ", "v_int_9", " ", v_int_9, " ", "v_char_21", " ", (v_char_21 == 'S'), " ", "v_char_20", " ", (v_char_20 == 's'), " ", "v_array_9[2]", " ", (v_array_9[2] == -1.35), " ", "v_array_3[2]", " ", (v_array_3[2] == -8.94), " ", "v_multiset_bool_bool_int_int_1.0", " ", (v_multiset_bool_bool_int_int_1.0 == multiset{-21.08}), " ", "v_multiset_bool_bool_int_int_1.1", " ", v_multiset_bool_bool_int_int_1.1, " ", "v_int_array_map_3.2", " ", (v_int_array_map_3.2 == map[-11.30 := false, 20.60 := true]), " ", "v_int_array_map_3.1", " ", (v_int_array_map_3.1 == v_array_3), " ", "v_int_array_map_3.0", " ", v_int_array_map_3.0, " ", "v_int_8", " ", v_int_8, " ", "v_array_10[2]", " ", (v_array_10[2] == 0.67), " ", "v_int_7", " ", v_int_7, " ", "v_multiset_bool_bool_int_int_1.2", " ", v_multiset_bool_bool_int_int_1.2, " ", "v_int_13", " ", v_int_13, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_char_10", " ", (v_char_10 == 'a'), " ", "v_int_array_map_10.0", " ", v_int_array_map_10.0, " ", "v_int_array_map_10.2", " ", (v_int_array_map_10.2 == map[-8.97 := true, 28.41 := true]), " ", "v_array_4[0]", " ", (v_array_4[0] == -11.00), " ", "v_array_9[1]", " ", (v_array_9[1] == 7.22), " ", "v_int_array_map_10.1", " ", (v_int_array_map_10.1 == v_array_10), " ", "p_m_method_1_1[2]", " ", (p_m_method_1_1[2] == -7.06), " ", "v_array_11[2]", " ", (v_array_11[2] == -28.52), " ", "v_bool_bool_int_2.0", " ", v_bool_bool_int_2.0, " ", "v_bool_bool_int_2.2", " ", v_bool_bool_int_2.2, " ", "v_bool_bool_int_2.1", " ", v_bool_bool_int_2.1, " ", "v_array_5[2]", " ", (v_array_5[2] == 5.07), " ", "v_int_array_map_4.2", " ", (v_int_array_map_4.2 == map[-5.51 := false, -10.34 := true, 20.14 := true, -7.39 := true, -2.26 := true]), " ", "v_int_array_map_4.1", " ", (v_int_array_map_4.1 == v_array_4), " ", "v_int_array_map_4.0", " ", v_int_array_map_4.0, " ", "v_array_10[4]", " ", (v_array_10[4] == 7.38), " ", "v_array_11[1]", " ", (v_array_11[1] == -29.70), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{'r', 'H'}), " ", "v_int_array_map_11.1", " ", (v_int_array_map_11.1 == v_array_11), " ", "v_int_array_map_11.0", " ", v_int_array_map_11.0, " ", "v_array_6[0]", " ", (v_array_6[0] == 24.65), " ", "v_int_array_map_11.2", " ", (v_int_array_map_11.2 == map[-17.83 := true, -3.75 := true, -23.42 := true]), " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_4[4]", " ", (v_array_4[4] == -19.29), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_array_11[4]", " ", (v_array_11[4] == -11.51), " ", "v_array_12[1]", " ", (v_array_12[1] == -20.92), " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_multiset_bool_bool_int_int_3", " ", (v_multiset_bool_bool_int_int_3 == v_multiset_bool_bool_int_int_4), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "v_multiset_bool_bool_int_int_1", " ", (v_multiset_bool_bool_int_int_1 == v_multiset_bool_bool_int_int_5), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_multiset_bool_bool_int_int_2", " ", (v_multiset_bool_bool_int_int_2 == v_multiset_bool_bool_int_int_6), " ", "v_array_6", " ", (v_array_6 == v_array_6), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_5[0]", " ", (v_array_5[0] == -9.35), " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_array_4[3]", " ", (v_array_4[3] == -18.49), " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_int_array_map_5.2", " ", (v_int_array_map_5.2 == map[-20.16 := true]), " ", "v_int_array_map_5.1", " ", (v_int_array_map_5.1 == v_array_5), " ", "v_map_4", " ", (v_map_4 == map['a' := 'V', 'Q' := 'O', 'R' := 'T', 'u' := 'd', 'v' := 'R', 'H' := 'x', 'x' := 'J', 'Z' := 'h', 'k' := 'X', 'K' := 'h']), " ", "v_char_3", " ", (v_char_3 == 'b'), " ", "v_int_array_map_5.0", " ", v_int_array_map_5.0, " ", "v_char_5", " ", (v_char_5 == 'o'), " ", "v_char_4", " ", (v_char_4 == 'E'), " ", "v_char_7", " ", (v_char_7 == 'Q'), " ", "v_char_6", " ", (v_char_6 == 'j'), " ", "v_array_11[3]", " ", (v_array_11[3] == 25.29), " ", "v_char_9", " ", (v_char_9 == 'n'), " ", "v_char_8", " ", (v_char_8 == 'H'), " ", "v_array_12[0]", " ", (v_array_12[0] == -28.07), " ", "v_map_1", " ", (v_map_1 == map['s' := v_multiset_bool_bool_int_int_7, 'J' := v_multiset_bool_bool_int_int_8]), " ", "v_map_3", " ", (v_map_3 == map['r' := v_int_array_map_24, 'e' := v_int_array_map_25, 'w' := v_int_array_map_26, 'G' := v_int_array_map_27, 'J' := v_int_array_map_28]), " ", "v_int_array_map_12.0", " ", v_int_array_map_12.0, " ", "v_int_array_map_12.2", " ", (v_int_array_map_12.2 == map[-6.67 := false, -7.48 := false, 11.04 := true]), " ", "v_array_5[1]", " ", (v_array_5[1] == 7.32), " ", "v_int_array_map_12.1", " ", (v_int_array_map_12.1 == v_array_12), " ", "v_array_7[1]", " ", (v_array_7[1] == -26.12), " ", "v_array_12[3]", " ", (v_array_12[3] == 29.49), " ", "v_array_13[0]", " ", (v_array_13[0] == -18.90), " ", "v_array_1[2]", " ", (v_array_1[2] == -12.99), " ", "v_array_7[0]", " ", (v_array_7[0] == -6.98), " ", "v_int_array_map_6.1", " ", (v_int_array_map_6.1 == v_array_6), " ", "v_int_array_map_6.0", " ", v_int_array_map_6.0, " ", "v_array_7[2]", " ", (v_array_7[2] == 28.31), " ", "v_array_12[2]", " ", (v_array_12[2] == 25.07), " ", "v_int_array_map_6.2", " ", (v_int_array_map_6.2 == map[12.32 := true, 11.45 := true, 4.61 := false]), " ", "v_int_array_map_13.2", " ", (v_int_array_map_13.2 == map[21.04 := false]), " ", "v_array_2[0]", " ", (v_array_2[0] == -16.70), " ", "v_int_array_map_13.1", " ", (v_int_array_map_13.1 == v_array_13), " ", "v_int_array_map_13.0", " ", v_int_array_map_13.0, " ", "v_array_6[2]", " ", (v_array_6[2] == 24.15), " ", "p_m_method_1_1[0]", " ", (p_m_method_1_1[0] == -22.72), " ", "v_array_13[2]", " ", (v_array_13[2] == 21.16), " ", "v_int_array_map_1", " ", (v_int_array_map_1 == v_int_array_map_29), " ", "v_int_array_map_9", " ", (v_int_array_map_9 == v_int_array_map_30), " ", "v_int_array_map_8", " ", (v_int_array_map_8 == v_int_array_map_31), " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 'W'), " ", "v_bool_bool_int_1.1", " ", v_bool_bool_int_1.1, " ", "v_int_array_map_7", " ", (v_int_array_map_7 == v_int_array_map_32), " ", "p_m_method_1_1", " ", "v_bool_bool_int_1.0", " ", v_bool_bool_int_1.0, " ", "v_int_array_map_6", " ", (v_int_array_map_6 == v_int_array_map_33), " ", "v_int_array_map_5", " ", (v_int_array_map_5 == v_int_array_map_34), " ", "v_bool_bool_int_1.2", " ", v_bool_bool_int_1.2, " ", "v_int_array_map_4", " ", (v_int_array_map_4 == v_int_array_map_35), " ", "v_int_array_map_3", " ", (v_int_array_map_3 == v_int_array_map_36), " ", "v_int_array_map_2", " ", (v_int_array_map_2 == v_int_array_map_37), " ", "v_array_1[0]", " ", (v_array_1[0] == 21.29), " ", "v_array_6[1]", " ", (v_array_6[1] == -27.01), " ", "v_int_array_map_7.0", " ", v_int_array_map_7.0, " ", "v_array_13[1]", " ", (v_array_13[1] == 22.43), " ", "p_m_method_1_1[1]", " ", (p_m_method_1_1[1] == 2.67), " ", "v_array_12[4]", " ", (v_array_12[4] == -11.44), " ", "v_int_array_map_7.2", " ", (v_int_array_map_7.2 == map[17.11 := true, 28.93 := false, -27.97 := false]), " ", "v_int_array_map_7.1", " ", (v_int_array_map_7.1 == v_array_7), " ", "v_int_array_map_14.2", " ", (v_int_array_map_14.2 == map[12.28 := false, 22.17 := false, -19.65 := true]), " ", "v_int_array_map_14.1", " ", (v_int_array_map_14.1 == v_array_14), " ", "v_seq_6", " ", (v_seq_6 == [map['r' := v_int_array_map_38, 'w' := v_int_array_map_39, 'G' := v_int_array_map_40], map['A' := v_int_array_map_41, 'b' := v_int_array_map_42, 'H' := v_int_array_map_43]]), " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_array_1[1]", " ", (v_array_1[1] == -25.72), " ", "v_int_array_map_14.0", " ", v_int_array_map_14.0, "\n";
	return (if ((v_char_21 in v_map_4)) then (v_map_4[v_char_21]) else (v_char_16)), (v_int_15 % (match 'X' {
		case 'E' => |{'x', 'f', 'N'}|
		case _ => v_int_array_map_1.0
	})), v_int_8;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_array_16: array<real> := new real[5] [-22.72, 2.67, -7.06, 4.35, 20.01];
	var v_array_17: array<real> := new real[5] [16.65, 12.16, -10.55, 29.30, 25.76];
	var v_seq_8: seq<array<real>> := [v_array_16, v_array_17];
	var v_seq_21: seq<array<real>> := v_seq_8;
	var v_int_32: int := -3;
	var v_int_33: int := 29;
	var v_int_34: int, v_int_35: int := safe_subsequence(v_seq_21, v_int_32, v_int_33);
	var v_int_30: int, v_int_31: int := v_int_34, v_int_35;
	var v_array_18: array<real> := new real[3] [-29.45, -13.39, 28.47];
	var v_array_19: array<real> := new real[3] [-29.08, -21.01, -20.29];
	var v_array_20: array<real> := new real[3] [20.55, 10.33, 13.76];
	var v_array_21: array<real> := new real[4] [5.81, -25.56, -9.61, 20.32];
	var v_array_22: array<real> := new real[4] [8.39, 25.70, 15.62, 9.62];
	var v_array_23: array<real> := new real[4];
	v_array_23[0] := 26.24;
	v_array_23[1] := -17.38;
	v_array_23[2] := -25.75;
	v_array_23[3] := -25.08;
	var v_array_24: array<real> := new real[3] [2.38, -4.36, -9.58];
	var v_map_5: map<char, seq<array<real>>> := map['A' := [v_array_18, v_array_19, v_array_20], 'F' := [v_array_21, v_array_22, v_array_23, v_array_24], 'G' := []];
	var v_char_22: char := 'O';
	var v_array_25: array<real> := new real[5] [-16.81, -6.24, 8.53, -5.76, -2.71];
	var v_array_26: array<real> := new real[3] [-23.08, 26.23, 3.50];
	var v_seq_11: seq<array<real>> := (if ((if (false) then (false) else (true))) then ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_30..v_int_31]) else (v_seq_8))) else ((if ((v_char_22 in v_map_5)) then (v_map_5[v_char_22]) else ([v_array_25, v_array_26]))));
	var v_seq_10: seq<char> := (if (false) then (['T', 'G', 'x']) else (['l', 'M']));
	var v_seq_9: seq<int> := [2, 5, 12];
	var v_int_16: int := 28;
	var v_seq_22: seq<int> := v_seq_9;
	var v_int_36: int := v_int_16;
	var v_int_37: int := safe_index_seq(v_seq_22, v_int_36);
	v_int_16 := v_int_37;
	var v_int_17: int := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_16]) else (21));
	var v_int_18: int := safe_index_seq(v_seq_10, v_int_17);
	var v_int_19: int := v_int_18;
	var v_seq_12: seq<array<real>> := v_seq_8;
	var v_map_6: map<char, int> := map['U' := 2, 'q' := 12, 't' := 9];
	var v_char_23: char := 'T';
	var v_int_20: int := (if ((v_char_23 in v_map_6)) then (v_map_6[v_char_23]) else (23));
	var v_seq_23: seq<array<real>> := v_seq_12;
	var v_int_38: int := v_int_20;
	var v_int_39: int := safe_index_seq(v_seq_23, v_int_38);
	v_int_20 := v_int_39;
	var v_array_27: array<real> := new real[4] [-12.84, 10.62, -24.58, -25.50];
	var v_array_28: array<real> := new real[4] [7.91, 22.74, -26.50, 5.75];
	var v_map_7: map<char, array<real>> := map['t' := v_array_27, 'k' := v_array_28];
	var v_char_24: char := 'W';
	var v_array_29: array<real> := new real[3] [-16.83, -25.69, 16.68];
	var v_array_30: array<real> := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_19]) else ((if ((|v_seq_12| > 0)) then (v_seq_12[v_int_20]) else ((if ((v_char_24 in v_map_7)) then (v_map_7[v_char_24]) else (v_array_29))))));
	var v_seq_13: seq<char> := ['I', 'W', 'r', 'U'];
	var v_int_21: int := 6;
	var v_seq_24: seq<char> := v_seq_13;
	var v_int_40: int := v_int_21;
	var v_int_41: int := safe_index_seq(v_seq_24, v_int_40);
	v_int_21 := v_int_41;
	var v_char_29: char := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_21]) else ('u'));
	var v_map_8: map<char, char> := map['x' := 'H'];
	var v_char_25: char := 'a';
	var v_char_30: char := (if ((v_char_25 in v_map_8)) then (v_map_8[v_char_25]) else ('U'));
	var v_char_31: char := (if (true) then ('H') else ('B'));
	var v_char_26: char := 'Q';
	var v_char_27: char := 'B';
	var v_char_28: char := m_method_4(v_char_26, v_char_27);
	var v_char_32: char := v_char_28;
	var v_bool_6: bool := m_method_3(v_char_29, v_char_30, v_char_31, v_char_32);
	var v_map_9: map<char, char> := map['f' := 'Q', 'y' := 'y', 'W' := 'E'];
	var v_char_33: char := 'j';
	var v_char_34: char := (if (v_bool_6) then (v_char_24) else ((match 'l' {
		case _ => v_char_28
	})));
	var v_char_35: char, v_int_22: int, v_int_23: int := m_method_1(v_array_30, v_char_34);
	v_char_25, v_int_21, v_int_17 := v_char_35, v_int_22, v_int_23;
	var v_seq_14: seq<map<char, char>> := [map['B' := 'A']];
	var v_int_24: int := -22;
	var v_seq_29: seq<map<char, char>> := v_seq_14;
	var v_int_50: int := v_int_24;
	var v_int_51: int := safe_index_seq(v_seq_29, v_int_50);
	v_int_24 := v_int_51;
	var v_map_12: map<char, char> := (match 'W' {
		case 'q' => (if (true) then (map['Z' := 'B', 'v' := 't', 'h' := 'y', 'W' := 'N']) else (map['I' := 'u', 'k' := 'a']))
		case 'R' => v_map_8
		case _ => (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_24]) else (map['p' := 'g']))
	});
	var v_seq_15: seq<char> := [];
	var v_int_25: int := 19;
	var v_char_38: char := (match 'K' {
		case 'F' => v_char_30
		case _ => (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_25]) else ('W'))
	});
	var v_map_10: map<char, map<char, char>> := map['X' := map['l' := 'D'], 'F' := map['k' := 'W', 'j' := 'Z', 'O' := 'T', 'v' := 'a', 'Z' := 'P'], 'V' := map['Z' := 'x', 'n' := 'r', 'r' := 'l', 'R' := 'j', 'X' := 'k'], 'S' := map['a' := 'i', 'm' := 'H', 'p' := 'u']];
	var v_char_36: char := 'a';
	var v_map_11: map<char, char> := (if ((v_char_36 in v_map_10)) then (v_map_10[v_char_36]) else (map['T' := 'O', 'P' := 'Y', 'h' := 'p', 'L' := 'b', 'F' := 'Z']));
	var v_seq_16: seq<char> := [];
	var v_int_26: int := 13;
	var v_char_37: char := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_26]) else ('S'));
	var v_seq_18: seq<char> := (['V', 'g'] + ['B', 'H', 'X']);
	var v_seq_31: seq<char> := v_seq_18;
	var v_seq_17: seq<int> := [8, 28, 27];
	var v_int_27: int := 7;
	var v_seq_30: seq<int> := v_seq_17;
	var v_int_52: int := v_int_27;
	var v_int_53: int := safe_index_seq(v_seq_30, v_int_52);
	v_int_27 := v_int_53;
	var v_int_56: int := (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_27]) else (22));
	var v_int_57: int := v_int_20;
	var v_int_58: int, v_int_59: int := safe_subsequence(v_seq_31, v_int_56, v_int_57);
	var v_int_54: int, v_int_55: int := v_int_58, v_int_59;
	var v_seq_20: seq<char> := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_54..v_int_55]) else (v_seq_18));
	var v_seq_19: seq<map<char, int>> := [map['R' := -20, 'O' := 27, 'U' := 17], map['C' := 28, 'U' := 16, 'E' := 14], map['y' := 26, 'o' := 29, 'a' := -26, 'd' := 21, 'E' := 17]];
	var v_int_28: int := 13;
	var v_seq_32: seq<map<char, int>> := v_seq_19;
	var v_int_60: int := v_int_28;
	var v_int_61: int := safe_index_seq(v_seq_32, v_int_60);
	v_int_28 := v_int_61;
	var v_map_13: map<char, int> := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_28]) else (map['W' := 5, 'K' := 4, 'o' := 3]));
	var v_char_39: char := (match 'W' {
		case 'Q' => 'J'
		case 'S' => 'p'
		case _ => 'a'
	});
	var v_int_29: int := (if ((v_char_39 in v_map_13)) then (v_map_13[v_char_39]) else ((13 * 9)));
	var v_map_15: map<char, char> := (match 'I' {
		case 'p' => map['W' := 'W', 'V' := 'M', 'j' := 'z', 'e' := 'b', 'b' := 'e']
		case 'L' => map['f' := 'w', 'l' := 'm', 'K' := 'x', 'N' := 'n', 'I' := 'l']
		case _ => map['V' := 'd', 'f' := 'j', 'C' := 'P', 'v' := 'n']
	});
	var v_map_14: map<char, char> := map['O' := 'V'];
	var v_char_40: char := 'j';
	var v_char_41: char := (if ((v_char_40 in v_map_14)) then (v_map_14[v_char_40]) else ('E'));
	v_char_24, v_char_30, v_char_34, v_char_22 := v_char_28, (if ((v_char_38 in v_map_12)) then (v_map_12[v_char_38]) else ((if ((v_char_37 in v_map_11)) then (v_map_11[v_char_37]) else (v_char_23)))), (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_29]) else ((if ((true && false)) then (v_char_31) else (v_char_32)))), (match 's' {
		case 'b' => (match 'n' {
			case _ => v_char_38
		})
		case _ => (if ((v_char_41 in v_map_15)) then (v_map_15[v_char_41]) else ((match 'o' {
			case 'u' => 'S'
			case 'I' => 't'
			case _ => 'J'
		})))
	});
	print "v_char_39", " ", (v_char_39 == 'a'), " ", "v_array_16[3]", " ", (v_array_16[3] == 4.35), " ", "v_char_38", " ", (v_char_38 == 'W'), " ", "v_char_37", " ", (v_char_37 == 'S'), " ", "v_char_36", " ", (v_char_36 == 'a'), " ", "v_array_20[1]", " ", (v_array_20[1] == 10.33), " ", "v_char_35", " ", (v_char_35 == 's'), " ", "v_char_34", " ", (v_char_34 == 's'), " ", "v_array_17[0]", " ", (v_array_17[0] == 16.65), " ", "v_map_13", " ", (v_map_13 == map['R' := -20, 'U' := 17, 'O' := 27]), " ", "v_array_22[3]", " ", (v_array_22[3] == 9.62), " ", "v_map_11", " ", (v_map_11 == map['P' := 'Y', 'T' := 'O', 'F' := 'Z', 'h' := 'p', 'L' := 'b']), " ", "v_map_12", " ", (v_map_12 == map['B' := 'A']), " ", "v_map_10", " ", (v_map_10 == map['S' := map['p' := 'u', 'a' := 'i', 'm' := 'H'], 'F' := map['v' := 'a', 'j' := 'Z', 'Z' := 'P', 'k' := 'W', 'O' := 'T'], 'V' := map['r' := 'l', 'R' := 'j', 'X' := 'k', 'Z' := 'x', 'n' := 'r'], 'X' := map['l' := 'D']]), " ", "v_array_25[3]", " ", (v_array_25[3] == -5.76), " ", "v_array_28[2]", " ", (v_array_28[2] == -26.50), " ", "v_array_26[0]", " ", (v_array_26[0] == -23.08), " ", "v_array_23[1]", " ", (v_array_23[1] == -17.38), " ", "v_array_19[2]", " ", (v_array_19[2] == -20.29), " ", "v_char_29", " ", (v_char_29 == 'I'), " ", "v_array_16[2]", " ", (v_array_16[2] == -7.06), " ", "v_char_28", " ", (v_char_28 == 's'), " ", "v_char_27", " ", (v_char_27 == 'B'), " ", "v_char_26", " ", (v_char_26 == 'Q'), " ", "v_array_20[0]", " ", (v_array_20[0] == 20.55), " ", "v_char_25", " ", (v_char_25 == 's'), " ", "v_array_19[1]", " ", (v_array_19[1] == -21.01), " ", "v_char_24", " ", (v_char_24 == 's'), " ", "v_char_23", " ", (v_char_23 == 'T'), " ", "v_char_22", " ", (v_char_22 == 'J'), " ", "v_array_22[2]", " ", (v_array_22[2] == 15.62), " ", "v_int_29", " ", v_int_29, " ", "v_array_29[0]", " ", (v_array_29[0] == -16.83), " ", "v_array_28[3]", " ", (v_array_28[3] == 5.75), " ", "v_array_25[4]", " ", (v_array_25[4] == -2.71), " ", "v_array_26[1]", " ", (v_array_26[1] == 26.23), " ", "v_array_23[2]", " ", (v_array_23[2] == -25.75), " ", "v_char_32", " ", (v_char_32 == 's'), " ", "v_char_31", " ", (v_char_31 == 'H'), " ", "v_char_30", " ", (v_char_30 == 'T'), " ", "v_seq_20", " ", (v_seq_20 == []), " ", "v_array_17[2]", " ", (v_array_17[2] == -10.55), " ", "v_array_21[0]", " ", (v_array_21[0] == 5.81), " ", "v_array_28[0]", " ", (v_array_28[0] == 7.91), " ", "v_array_27[3]", " ", (v_array_27[3] == -25.50), " ", "v_array_25[1]", " ", (v_array_25[1] == -6.24), " ", "v_array_19", " ", (v_array_19 == v_array_19), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_map_5", " ", (v_map_5 == map['A' := [v_array_18, v_array_19, v_array_20], 'F' := [v_array_21, v_array_22, v_array_23, v_array_24], 'G' := []]), " ", "v_map_7", " ", (v_map_7 == map['t' := v_array_27, 'k' := v_array_28]), " ", "v_array_16[4]", " ", (v_array_16[4] == 20.01), " ", "v_map_6", " ", (v_map_6 == map['q' := 12, 't' := 9, 'U' := 2]), " ", "v_map_8", " ", (v_map_8 == map['x' := 'H']), " ", "v_array_17[1]", " ", (v_array_17[1] == 12.16), " ", "v_array_20[2]", " ", (v_array_20[2] == 13.76), " ", "v_array_28[1]", " ", (v_array_28[1] == 22.74), " ", "v_array_25[2]", " ", (v_array_25[2] == 8.53), " ", "v_array_23[0]", " ", (v_array_23[0] == 26.24), " ", "v_array_30", " ", (v_array_30 == v_array_16), " ", "v_array_18[1]", " ", (v_array_18[1] == -13.39), " ", "v_array_21[2]", " ", (v_array_21[2] == -9.61), " ", "v_array_27[1]", " ", (v_array_27[1] == 10.62), " ", "v_array_24[2]", " ", (v_array_24[2] == -9.58), " ", "v_array_17[4]", " ", (v_array_17[4] == 25.76), " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_17[3]", " ", (v_array_17[3] == 29.30), " ", "v_array_18[0]", " ", (v_array_18[0] == -29.45), " ", "v_array_21[1]", " ", (v_array_21[1] == -25.56), " ", "v_array_27[2]", " ", (v_array_27[2] == -24.58), " ", "v_array_25[0]", " ", (v_array_25[0] == -16.81), " ", "v_array_29", " ", (v_array_29 == v_array_29), " ", "v_array_28", " ", (v_array_28 == v_array_28), " ", "v_array_27", " ", (v_array_27 == v_array_27), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_array_16[1]", " ", (v_array_16[1] == 2.67), " ", "v_array_19[0]", " ", (v_array_19[0] == -29.08), " ", "v_array_22[1]", " ", (v_array_22[1] == 25.70), " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_seq_18", " ", (v_seq_18 == ['V', 'g', 'B', 'H', 'X']), " ", "v_seq_19", " ", (v_seq_19 == [map['R' := -20, 'U' := 17, 'O' := 27], map['C' := 28, 'U' := 16, 'E' := 14], map['a' := -26, 'd' := 21, 'E' := 17, 'y' := 26, 'o' := 29]]), " ", "v_bool_6", " ", v_bool_6, " ", "v_int_23", " ", v_int_23, " ", "v_array_26[2]", " ", (v_array_26[2] == 3.50), " ", "v_array_29[1]", " ", (v_array_29[1] == -25.69), " ", "v_int_22", " ", v_int_22, " ", "v_seq_16", " ", (v_seq_16 == []), " ", "v_int_21", " ", v_int_21, " ", "v_seq_17", " ", v_seq_17, " ", "v_seq_10", " ", (v_seq_10 == ['l', 'M']), " ", "v_int_28", " ", v_int_28, " ", "v_array_23[3]", " ", (v_array_23[3] == -25.08), " ", "v_seq_11", " ", (v_seq_11 == []), " ", "v_int_27", " ", v_int_27, " ", "v_seq_12", " ", (v_seq_12 == [v_array_16, v_array_17]), " ", "v_int_26", " ", v_int_26, " ", "v_array_24[0]", " ", (v_array_24[0] == 2.38), " ", "v_seq_13", " ", (v_seq_13 == ['I', 'W', 'r', 'U']), " ", "v_int_20", " ", v_int_20, " ", "v_array_18[2]", " ", (v_array_18[2] == 28.47), " ", "v_array_22[0]", " ", (v_array_22[0] == 8.39), " ", "v_array_16[0]", " ", (v_array_16[0] == -22.72), " ", "v_array_21[3]", " ", (v_array_21[3] == 20.32), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", (v_seq_8 == [v_array_16, v_array_17]), " ", "v_array_29[2]", " ", (v_array_29[2] == 16.68), " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_array_24[1]", " ", (v_array_24[1] == -4.36), " ", "v_array_27[0]", " ", (v_array_27[0] == -12.84), "\n";
}
