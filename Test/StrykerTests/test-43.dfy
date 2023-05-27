// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
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

method m_method_8(p_m_method_8_1: char, p_m_method_8_2: char, p_m_method_8_3: char) returns (ret_1: map<bool, int>)
	requires ((p_m_method_8_2 == 'O') && (p_m_method_8_1 == 'w') && (p_m_method_8_3 == 'C'));
	ensures (((p_m_method_8_2 == 'O') && (p_m_method_8_1 == 'w') && (p_m_method_8_3 == 'C')) ==> ((ret_1 == map[false := 14, true := 17])));
{
	if true {
		
	} else {
		if true {
			return map[false := -17, false := 15, false := 6, false := -23, true := 4];
		}
		var v_char_60: char, v_char_61: char, v_char_62: char, v_char_63: char := 'G', 'q', 'Q', 'o';
		v_char_60, v_char_62, v_char_63, v_char_61 := 'T', 'R', 'U', 'b';
		if true {
			return map[true := 24];
		} else {
			return map[false := 18];
		}
	}
	if false {
		var v_int_94: int, v_int_95: int := 20, -25;
		for v_int_93 := v_int_94 to v_int_95 
			invariant (v_int_95 - v_int_93 >= 0)
		{
			return map[false := 17, false := 1, true := 13];
		}
	} else {
		assert ((p_m_method_8_2 == 'O') && (p_m_method_8_3 == 'C'));
		expect ((p_m_method_8_2 == 'O') && (p_m_method_8_3 == 'C'));
		var v_char_64: char := 'W';
		print "v_char_64", " ", (v_char_64 == 'W'), " ", "p_m_method_8_1", " ", (p_m_method_8_1 == 'w'), " ", "p_m_method_8_3", " ", (p_m_method_8_3 == 'C'), " ", "p_m_method_8_2", " ", (p_m_method_8_2 == 'O'), "\n";
		return map[true := 17, false := 14];
	}
	return map[false := 23];
}

method m_method_7(p_m_method_7_1: char, p_m_method_7_2: char) returns (ret_1: array<char>)
	requires ((p_m_method_7_2 == 'H') && (p_m_method_7_1 == 's')) || ((p_m_method_7_2 == 'M') && (p_m_method_7_1 == 'p'));
	ensures (((p_m_method_7_2 == 'H') && (p_m_method_7_1 == 's')) ==> (ret_1.Length == 5 && (ret_1[0] == 'W') && (ret_1[1] == 'g') && (ret_1[2] == 'f') && (ret_1[3] == 'j') && (ret_1[4] == 'h'))) && (((p_m_method_7_2 == 'M') && (p_m_method_7_1 == 'p')) ==> (ret_1.Length == 5 && (ret_1[0] == 'W') && (ret_1[1] == 'g') && (ret_1[2] == 'f') && (ret_1[3] == 'j') && (ret_1[4] == 'h')));
{
	var v_array_5: array<char> := new char[5] ['W', 'g', 'f', 'j', 'h'];
	print "v_array_5[4]", " ", (v_array_5[4] == 'h'), " ", "v_array_5[3]", " ", (v_array_5[3] == 'j'), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "p_m_method_7_2", " ", (p_m_method_7_2 == 'M'), " ", "p_m_method_7_1", " ", (p_m_method_7_1 == 'p'), " ", "v_array_5[0]", " ", (v_array_5[0] == 'W'), " ", "v_array_5[2]", " ", (v_array_5[2] == 'f'), " ", "v_array_5[1]", " ", (v_array_5[1] == 'g'), "\n";
	return v_array_5;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: char) returns (ret_1: (int, bool))
	requires ((p_m_method_6_1 == 'p'));
	ensures (((p_m_method_6_1 == 'p')) ==> (((ret_1).0 == 5) && ((ret_1).1 == false)));
{
	var v_int_bool_1: (int, bool) := (5, false);
	print "v_int_bool_1.0", " ", v_int_bool_1.0, " ", "p_m_method_6_1", " ", (p_m_method_6_1 == 'p'), " ", "v_int_bool_1", " ", v_int_bool_1, " ", "v_int_bool_1.1", " ", v_int_bool_1.1, "\n";
	return v_int_bool_1;
}

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: char, p_m_method_5_3: char, p_m_method_5_4: char) returns (ret_1: (int, bool))
	requires ((p_m_method_5_4 == 'I') && (p_m_method_5_1 == 'i') && (p_m_method_5_3 == 'O') && (p_m_method_5_2 == 'O'));
	ensures (((p_m_method_5_4 == 'I') && (p_m_method_5_1 == 'i') && (p_m_method_5_3 == 'O') && (p_m_method_5_2 == 'O')) ==> (((ret_1).0 == 5) && ((ret_1).1 == false)));
{
	var v_char_10: char := 'p';
	var v_int_bool_2: (int, bool) := m_method_6(v_char_10);
	print "p_m_method_5_4", " ", (p_m_method_5_4 == 'I'), " ", "v_char_10", " ", (v_char_10 == 'p'), " ", "p_m_method_5_3", " ", (p_m_method_5_3 == 'O'), " ", "v_int_bool_2", " ", v_int_bool_2, " ", "p_m_method_5_2", " ", (p_m_method_5_2 == 'O'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'i'), "\n";
	return v_int_bool_2;
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char, p_m_method_4_3: char) returns (ret_1: char)
	requires ((p_m_method_4_2 == 't') && (p_m_method_4_1 == 'g') && (p_m_method_4_3 == 'q')) || ((p_m_method_4_2 == 'i') && (p_m_method_4_1 == 'h') && (p_m_method_4_3 == 'e')) || ((p_m_method_4_2 == 'h') && (p_m_method_4_1 == 'T') && (p_m_method_4_3 == 'i'));
	ensures (((p_m_method_4_2 == 'h') && (p_m_method_4_1 == 'T') && (p_m_method_4_3 == 'i')) ==> ((ret_1 == 'e'))) && (((p_m_method_4_2 == 't') && (p_m_method_4_1 == 'g') && (p_m_method_4_3 == 'q')) ==> ((ret_1 == 'e'))) && (((p_m_method_4_2 == 'i') && (p_m_method_4_1 == 'h') && (p_m_method_4_3 == 'e')) ==> ((ret_1 == 'e')));
{
	print "p_m_method_4_1", " ", (p_m_method_4_1 == 'g'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'q'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 't'), "\n";
	return 'e';
}

method m_method_3(p_m_method_3_1: (int, bool)) returns (ret_1: int)
	requires (((p_m_method_3_1).0 == 5) && ((p_m_method_3_1).1 == false)) || (((p_m_method_3_1).0 == 17) && ((p_m_method_3_1).1 == false));
	ensures ((((p_m_method_3_1).0 == 17) && ((p_m_method_3_1).1 == false)) ==> ((ret_1 == 2))) && ((((p_m_method_3_1).0 == 5) && ((p_m_method_3_1).1 == false)) ==> ((ret_1 == 2)));
{
	var v_char_1: char := 'T';
	var v_char_2: char := 'h';
	var v_char_3: char := 'i';
	var v_char_4: char := m_method_4(v_char_1, v_char_2, v_char_3);
	var v_char_5: char := (match 'C' {
		case 'R' => 'h'
		case _ => 'h'
	});
	var v_char_6: char := v_char_3;
	var v_char_7: char := v_char_4;
	var v_char_8: char := m_method_4(v_char_5, v_char_6, v_char_7);
	v_char_5, v_char_8 := (if ((false <==> false)) then ((match 'o' {
		case 'M' => 'G'
		case 'V' => 'G'
		case _ => 'W'
	})) else (v_char_4)), v_char_8;
	var v_map_2: map<char, seq<char>> := map['h' := ['b', 'I'], 'A' := ['b', 'Q', 'E']];
	var v_char_9: char := 'b';
	var v_seq_4: seq<char> := (if ((v_char_9 in v_map_2)) then (v_map_2[v_char_9]) else (['K', 'D', 'd', 'n']));
	var v_int_13: int := (17 % 3);
	var v_int_14: int := safe_index_seq(v_seq_4, v_int_13);
	print "v_char_1", " ", (v_char_1 == 'T'), " ", "v_char_3", " ", (v_char_3 == 'i'), " ", "v_char_2", " ", (v_char_2 == 'h'), " ", "v_char_5", " ", (v_char_5 == 'W'), " ", "v_char_4", " ", (v_char_4 == 'e'), " ", "v_char_7", " ", (v_char_7 == 'e'), " ", "v_char_6", " ", (v_char_6 == 'i'), " ", "v_char_9", " ", (v_char_9 == 'b'), " ", "v_char_8", " ", (v_char_8 == 'e'), " ", "p_m_method_3_1.0", " ", p_m_method_3_1.0, " ", "p_m_method_3_1.1", " ", p_m_method_3_1.1, " ", "v_map_2", " ", (v_map_2 == map['A' := ['b', 'Q', 'E'], 'h' := ['b', 'I']]), " ", "v_int_13", " ", v_int_13, " ", "v_seq_4", " ", (v_seq_4 == ['K', 'D', 'd', 'n']), " ", "v_int_14", " ", v_int_14, " ", "p_m_method_3_1", " ", p_m_method_3_1, "\n";
	return v_int_14;
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

method m_method_2(p_m_method_2_1: (int, bool, int), p_m_method_2_2: array<int>, p_m_method_2_3: bool) returns (ret_1: (seq<real>, map<int, int>))
	requires (p_m_method_2_2.Length == 5 && (p_m_method_2_2[0] == 10) && (p_m_method_2_2[1] == 4) && (p_m_method_2_2[2] == 10) && (p_m_method_2_2[3] == 1) && (p_m_method_2_2[4] == 3) && ((p_m_method_2_1).0 == 11) && ((p_m_method_2_1).1 == false) && ((p_m_method_2_1).2 == 18) && (p_m_method_2_3 == false));
	ensures ((p_m_method_2_2.Length == 5 && (p_m_method_2_2[0] == 10) && (p_m_method_2_2[1] == 4) && (p_m_method_2_2[2] == 10) && (p_m_method_2_2[3] == 1) && (p_m_method_2_2[4] == 3) && ((p_m_method_2_1).0 == 11) && ((p_m_method_2_1).1 == false) && ((p_m_method_2_1).2 == 18) && (p_m_method_2_3 == false)) ==> (|(ret_1).0| == 4 && (27.79 < (ret_1).0[0] < 27.99) && (9.60 < (ret_1).0[1] < 9.80) && (-0.12 < (ret_1).0[2] < 0.08) && (24.61 < (ret_1).0[3] < 24.81) && ((ret_1).1 == map[26 := 5, 29 := 11])));
{
	var v_seq_map_11: (seq<real>, map<int, int>) := ([27.89, 9.70, -0.02, 24.71], map[26 := 5, 29 := 11]);
	var v_seq_map_14: (seq<real>, map<int, int>) := ([27.89, 9.70, -0.02, 24.71], map[26 := 5, 29 := 11]);
	print "v_seq_map_11.1", " ", (v_seq_map_11.1 == map[26 := 5, 29 := 11]), " ", "p_m_method_2_1.0", " ", p_m_method_2_1.0, " ", "v_seq_map_11.0", " ", (v_seq_map_11.0 == [27.89, 9.70, -0.02, 24.71]), " ", "p_m_method_2_1.1", " ", p_m_method_2_1.1, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_seq_map_11", " ", (v_seq_map_11 == v_seq_map_14), " ", "p_m_method_2_1.2", " ", p_m_method_2_1.2, " ", "p_m_method_2_2[2]", " ", p_m_method_2_2[2], " ", "p_m_method_2_2[1]", " ", p_m_method_2_2[1], " ", "p_m_method_2_2[0]", " ", p_m_method_2_2[0], " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", "\n";
	return v_seq_map_11;
}

method m_method_1(p_m_method_1_1: map<bool, int>, p_m_method_1_2: array<real>, p_m_method_1_3: bool) returns (ret_1: char, ret_2: int, ret_3: map<bool, bool>, ret_4: int)
	requires ((p_m_method_1_1 == map[false := 10, true := 17]) && (p_m_method_1_3 == false) && p_m_method_1_2.Length == 4 && (-10.52 < p_m_method_1_2[0] < -10.32) && (-24.33 < p_m_method_1_2[1] < -24.13) && (-11.89 < p_m_method_1_2[2] < -11.69) && (8.86 < p_m_method_1_2[3] < 9.06));
	ensures (((p_m_method_1_1 == map[false := 10, true := 17]) && (p_m_method_1_3 == false) && p_m_method_1_2.Length == 4 && (-10.52 < p_m_method_1_2[0] < -10.32) && (-24.33 < p_m_method_1_2[1] < -24.13) && (-11.89 < p_m_method_1_2[2] < -11.69) && (8.86 < p_m_method_1_2[3] < 9.06)) ==> ((ret_1 == 'O') && (ret_2 == 5) && (ret_3 == map[false := true, true := true]) && (ret_4 == 10)));
{
	assert true;
	expect true;
	var v_seq_map_1: (seq<real>, map<int, int>) := ([-1.30, -5.61, -29.93, -25.69], map[17 := 29, -14 := 1, 22 := 3]);
	var v_seq_map_2: (seq<real>, map<int, int>) := ([], map[20 := 16, 5 := 21, 29 := 6]);
	var v_seq_map_3: (seq<real>, map<int, int>) := ([8.49, -2.40], map[25 := 10, 19 := 14]);
	var v_seq_map_4: (seq<real>, map<int, int>) := ([-0.75], map[26 := 23, 10 := 15]);
	var v_seq_map_5: (seq<real>, map<int, int>) := ([2.98, -3.59], map[7 := 9, 25 := 0, -1 := 16, -26 := 18, 17 := 19]);
	var v_seq_map_6: (seq<real>, map<int, int>) := ([-18.61, 20.72, 14.75, 3.72], map[-4 := 24, 5 := 26, 26 := 22, 25 := 28, 27 := 25]);
	var v_seq_map_7: (seq<real>, map<int, int>) := ([], map[15 := 19]);
	var v_seq_map_8: (seq<real>, map<int, int>) := ([29.49, -9.59, -9.55, 20.88], map[-24 := 7, 18 := -26, 25 := -14, 29 := 27]);
	var v_seq_map_9: (seq<real>, map<int, int>) := ([-21.26, -9.48, 23.01, 10.78], map[21 := 28, 22 := 16]);
	var v_seq_map_10: (seq<real>, map<int, int>) := ([-22.97, -28.97, 20.34, 27.04], map[2 := 15]);
	var v_map_1: map<(seq<real>, map<int, int>), set<map<set<real>, char>>> := (match 21 {
		case 27 => map[v_seq_map_1 := {map[{21.43, -23.77, -24.75} := 'J', {8.16, -12.04} := 'N', {-20.57, -1.33} := 'o', {6.64, 15.83} := 'd', {-1.02, -1.22, 8.46} := 'I'], map[{2.81, -27.15, -18.53} := 'S', {} := 's', {-9.56} := 'I', {1.81, 1.77, -9.40, -22.74} := 'x'], map[{-28.16, -14.71} := 'P', {-16.24, -6.62} := 'V', {-14.62, -0.59, -10.97, -2.09} := 's']}, v_seq_map_2 := {}, v_seq_map_3 := {map[{} := 'k', {-28.33, 28.79, 21.70} := 'L', {-1.72, 12.66, 0.24} := 'T'], map[{26.23, -19.18, -7.16, -4.33} := 'k', {17.11, 26.62, -19.74, 28.74} := 'E', {} := 'g'], map[{} := 'a', {-24.17, -6.08} := 'o']}, v_seq_map_4 := {map[{-24.82, -9.63} := 'U', {-29.37, -29.08, 17.47} := 'T', {-6.93, 9.83} := 'E'], map[{-0.75, 25.39, -19.28, -5.57} := 'D', {} := 'R']}, v_seq_map_5 := {map[{10.85, 8.21} := 'q', {} := 'o', {29.26, -16.99, -8.41, -9.59} := 'r', {} := 'u', {10.89, 5.85, 23.77, -4.06} := 'x'], map[{-26.21, -12.24, 4.81, 6.17} := 'R', {-6.03, -13.74} := 'N', {} := 'H', {-7.37} := 'N', {20.14} := 'h'], map[{} := 'k', {-5.96, -14.13} := 'E'], map[{16.14} := 'v', {-22.24} := 'V']}]
		case _ => map[v_seq_map_6 := {map[{-8.76, -26.81} := 'p', {-17.27, -6.02} := 'd', {21.33} := 'N', {} := 'c']}, v_seq_map_7 := {}, v_seq_map_8 := {}, v_seq_map_9 := {map[{28.99, 5.47, 13.11} := 't', {-19.73} := 'd', {28.27} := 'D', {} := 'h', {23.75} := 'R']}, v_seq_map_10 := {}]
	});
	var v_int_bool_int_1: (int, bool, int) := (11, false, 18);
	var v_int_bool_int_2: (int, bool, int) := v_int_bool_int_1;
	var v_array_2: array<int> := new int[5] [10, 4, 10, 1, 3];
	var v_array_3: array<int> := v_array_2;
	var v_bool_1: bool := false;
	var v_seq_map_12: (seq<real>, map<int, int>) := m_method_2(v_int_bool_int_2, v_array_3, v_bool_1);
	var v_seq_map_13: (seq<real>, map<int, int>) := v_seq_map_12;
	var v_seq_3: seq<set<map<set<real>, char>>> := [{map[{} := 'o', {25.99, 1.05, 29.87, -0.88} := 'D', {-21.16, -22.72} := 'N']}, {map[{1.00, -0.21, 28.32} := 'v', {-22.64, 9.44} := 'k', {4.43, 4.73, -29.12, -5.56} := 'k', {19.91, 10.66} := 'f'], map[{-27.69, -12.96} := 'X', {-5.80, -20.68, 2.37, -17.55} := 'y'], map[{-2.50} := 'k', {-25.36, -27.30, 12.79, 24.68} := 'P']}, {map[{-0.63, 27.63} := 'J', {} := 'g', {-12.70, -12.30, -11.16, -10.52} := 'l']}, {map[{15.48} := 'x', {-7.92, -27.64, 10.04, -21.52} := 'A', {28.94, 5.70, -9.87} := 'j'], map[{26.54, 16.59, 0.16, -4.49} := 'x', {5.32, -29.04, 12.25} := 'F', {-7.99, 13.77, 5.51, -7.24} := 'X']}];
	var v_int_12: int := 26;
	var v_seq_159: seq<set<map<set<real>, char>>> := v_seq_3;
	var v_int_213: int := v_int_12;
	var v_int_214: int := safe_index_seq(v_seq_159, v_int_213);
	v_int_12 := v_int_214;
	var v_map_3: map<char, char> := map['T' := 'p', 'G' := 'c', 'N' := 'G'];
	var v_char_11: char := 'O';
	var v_char_12: char := (if ((v_char_11 in v_map_3)) then (v_map_3[v_char_11]) else ('i'));
	var v_char_13: char := v_char_11;
	var v_char_14: char := v_char_11;
	var v_seq_5: seq<char> := ['I', 'Z', 'H', 'c'];
	var v_int_15: int := 21;
	var v_seq_158: seq<char> := v_seq_5;
	var v_int_211: int := v_int_15;
	var v_int_212: int := safe_index_seq(v_seq_158, v_int_211);
	v_int_15 := v_int_212;
	var v_char_15: char := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_15]) else ('i'));
	var v_int_bool_3: (int, bool) := m_method_5(v_char_12, v_char_13, v_char_14, v_char_15);
	var v_int_bool_4: (int, bool) := v_int_bool_3;
	var v_int_16: int := m_method_3(v_int_bool_4);
	var v_int_19: int, v_int_20: int := |(if ((v_seq_map_13 in v_map_1)) then (v_map_1[v_seq_map_13]) else ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_12]) else ({map[{14.87, 28.14, -4.84} := 'w', {-1.29, 7.05, -4.36, 8.53} := 'o'], map[{13.71, -28.77} := 'p', {26.17, 11.29} := 'R', {-1.86, 27.54, -10.53} := 'j', {-21.12, -3.91} := 'Y'], map[{15.03, -16.83} := 'c']}))))|, v_int_16;
	for v_int_11 := v_int_19 to v_int_20 
		invariant (v_int_20 - v_int_11 >= 0)
	{
		var v_seq_map_15: (seq<real>, map<int, int>) := ([27.89, 9.70, -0.02, 24.71], map[26 := 5, 29 := 11]);
		assert ((p_m_method_1_3 == false) && (v_seq_map_12 == v_seq_map_15) && (v_int_bool_int_1.2 == 18) && (v_char_11 == 'O'));
		expect ((p_m_method_1_3 == false) && (v_seq_map_12 == v_seq_map_15) && (v_int_bool_int_1.2 == 18) && (v_char_11 == 'O'));
		var v_map_4: map<char, int> := (map['F' := 12, 'S' := 27, 'z' := 0, 'M' := 13] - {'M'});
		var v_char_16: char := v_char_14;
		var v_int_bool_5: (int, bool) := (17, false);
		var v_int_bool_6: (int, bool) := v_int_bool_5;
		var v_int_17: int := m_method_3(v_int_bool_6);
		if ((if ((v_char_16 in v_map_4)) then (v_map_4[v_char_16]) else ((-14 / 6))) >= (if ((if (true) then (true) else (true))) then (v_int_17) else (v_array_2[4]))) {
			var v_map_5: map<char, int> := map['D' := 28, 'v' := 22, 'r' := 12];
			var v_char_17: char := 'm';
			var v_array_4: array<char> := new char[3] ['G', 'v', 'l'];
			var v_map_6: map<char, map<bool, bool>> := (map['T' := map[false := true, false := true], 'x' := map[false := true], 'M' := map[false := false, true := false, false := true], 'O' := map[false := true, true := false, true := true, false := true]]['c' := map[true := false, true := false, false := false, true := false]] + map['p' := map[false := true, false := true], 'W' := map[true := false, false := false, false := false], 'w' := map[false := true, false := false, false := false, false := true]]['J' := map[false := true, false := false, false := false, false := false, true := true]]);
			var v_char_18: char := v_char_15;
			return v_char_14, (v_array_2[0] - ((if ((v_char_17 in v_map_5)) then (v_map_5[v_char_17]) else (7)) * v_array_4.Length)), (if ((v_char_18 in v_map_6)) then (v_map_6[v_char_18]) else (map[false := true][false := true][(multiset({'w', 'J', 'a', 'Q'}) >= multiset{'m'}) := (multiset{'h', 'v', 'K'} !! multiset{'y'})])), |((if (false) then ({}) else ({'O', 'c', 'Z'})) * (if (true) then ({'x', 'V', 'w', 'x'}) else ({'G', 'l', 'Y', 'e'})))|;
		} else {
			var v_char_19: char := 'p';
			var v_char_20: char := 'M';
			var v_array_6: array<char> := m_method_7(v_char_19, v_char_20);
			var v_char_21: char := 's';
			var v_char_22: char := 'H';
			var v_array_7: array<char> := m_method_7(v_char_21, v_char_22);
			var v_seq_6: seq<bool> := [false, true, false, true];
			var v_seq_160: seq<bool> := v_seq_6;
			var v_int_217: int := 20;
			var v_int_218: int := 0;
			var v_int_219: int, v_int_220: int := safe_subsequence(v_seq_160, v_int_217, v_int_218);
			var v_int_215: int, v_int_216: int := v_int_219, v_int_220;
			var v_seq_7: seq<bool> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_215..v_int_216]) else (v_seq_6));
			var v_int_18: int := v_array_2[2];
			var v_map_7: map<char, bool> := map['G' := false];
			var v_char_23: char := 'h';
			var v_seq_map_16: (seq<real>, map<int, int>) := ([29.49, -9.59, -9.55, 20.88], map[18 := -26, -24 := 7, 25 := -14, 29 := 27]);
			var v_seq_map_17: (seq<real>, map<int, int>) := ([-18.61, 20.72, 14.75, 3.72], map[-4 := 24, 5 := 26, 25 := 28, 26 := 22, 27 := 25]);
			var v_seq_map_18: (seq<real>, map<int, int>) := ([], map[15 := 19]);
			var v_seq_map_19: (seq<real>, map<int, int>) := ([-21.26, -9.48, 23.01, 10.78], map[21 := 28, 22 := 16]);
			var v_seq_map_20: (seq<real>, map<int, int>) := ([-22.97, -28.97, 20.34, 27.04], map[2 := 15]);
			var v_seq_map_21: (seq<real>, map<int, int>) := ([27.89, 9.70, -0.02, 24.71], map[26 := 5, 29 := 11]);
			var v_seq_map_22: (seq<real>, map<int, int>) := ([27.89, 9.70, -0.02, 24.71], map[26 := 5, 29 := 11]);
			print "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_map_7", " ", (v_map_7 == map['G' := false]), " ", "v_array_6", " ", "v_char_23", " ", (v_char_23 == 'h'), " ", "v_char_22", " ", (v_char_22 == 'H'), " ", "v_char_21", " ", (v_char_21 == 's'), " ", "v_char_20", " ", (v_char_20 == 'M'), " ", "v_int_18", " ", v_int_18, " ", "v_array_7", " ", "v_char_19", " ", (v_char_19 == 'p'), " ", "v_map_4", " ", (v_map_4 == map['S' := 27, 'F' := 12, 'z' := 0]), " ", "v_int_bool_6", " ", v_int_bool_6, " ", "v_int_11", " ", v_int_11, " ", "v_char_16", " ", (v_char_16 == 'O'), " ", "v_int_bool_5", " ", v_int_bool_5, " ", "v_int_17", " ", v_int_17, " ", "v_int_bool_5.1", " ", v_int_bool_5.1, " ", "v_int_bool_5.0", " ", v_int_bool_5.0, " ", "v_bool_1", " ", v_bool_1, " ", "v_char_15", " ", (v_char_15 == 'I'), " ", "v_char_14", " ", (v_char_14 == 'O'), " ", "p_m_method_1_2[1]", " ", (p_m_method_1_2[1] == -24.23), " ", "v_char_13", " ", (v_char_13 == 'O'), " ", "v_char_12", " ", (v_char_12 == 'i'), " ", "v_char_11", " ", (v_char_11 == 'O'), " ", "v_array_3", " ", (v_array_3 == v_array_2), " ", "p_m_method_1_2", " ", "p_m_method_1_1", " ", (p_m_method_1_1 == map[false := 10, true := 17]), " ", "v_int_bool_4", " ", v_int_bool_4, " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_array_2[1]", " ", v_array_2[1], " ", "p_m_method_1_2[2]", " ", (p_m_method_1_2[2] == -11.79), " ", "v_int_bool_3", " ", v_int_bool_3, " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_int_bool_int_1.0", " ", v_int_bool_int_1.0, " ", "p_m_method_1_2[0]", " ", (p_m_method_1_2[0] == -10.42), " ", "v_int_bool_int_2", " ", v_int_bool_int_2, " ", "v_int_bool_int_1", " ", v_int_bool_int_1, " ", "v_int_bool_int_1.2", " ", v_int_bool_int_1.2, " ", "v_map_1", " ", (v_map_1 == map[v_seq_map_16 := {}, v_seq_map_17 := {map[{-26.81, -8.76} := 'p', {} := 'c', {21.33} := 'N', {-6.02, -17.27} := 'd']}, v_seq_map_18 := {}, v_seq_map_19 := {map[{} := 'h', {-19.73} := 'd', {23.75} := 'R', {28.27} := 'D', {28.99, 5.47, 13.11} := 't']}, v_seq_map_20 := {}]), " ", "v_int_bool_int_1.1", " ", v_int_bool_int_1.1, " ", "v_map_3", " ", (v_map_3 == map['T' := 'p', 'G' := 'c', 'N' := 'G']), " ", "v_seq_map_13", " ", (v_seq_map_13 == v_seq_map_21), " ", "v_int_12", " ", v_int_12, " ", "v_seq_map_12", " ", (v_seq_map_12 == v_seq_map_22), " ", "v_seq_5", " ", (v_seq_5 == ['I', 'Z', 'H', 'c']), " ", "v_seq_3", " ", (v_seq_3 == [{map[{} := 'o', {-21.16, -22.72} := 'N', {25.99, 1.05, -0.88, 29.87} := 'D']}, {map[{-12.96, -27.69} := 'X', {-20.68, 2.37, -5.80, -17.55} := 'y'], map[{-22.64, 9.44} := 'k', {4.43, -5.56, 4.73, -29.12} := 'k', {19.91, 10.66} := 'f', {-0.21, 1.00, 28.32} := 'v'], map[{-2.50} := 'k', {-25.36, 12.79, 24.68, -27.30} := 'P']}, {map[{} := 'g', {-0.63, 27.63} := 'J', {-11.16, -12.30, -10.52, -12.70} := 'l']}, {map[{5.32, 12.25, -29.04} := 'F', {-7.24, 13.77, -7.99, 5.51} := 'X', {26.54, 0.16, 16.59, -4.49} := 'x'], map[{15.48} := 'x', {10.04, -7.92, -27.64, -21.52} := 'A', {-9.87, 28.94, 5.70} := 'j']}]), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_2[4]", " ", v_array_2[4], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
			return v_char_11, (if (v_int_bool_int_1.1) then (v_array_6) else (v_array_7)).Length, ((if (false) then (map[true := true, false := true, true := false]) else (map[true := true, false := true])) + (map[true := false] + map[true := true]))[(if ((|v_seq_7| > 0)) then (v_seq_7[v_int_18]) else (v_int_bool_int_1.1)) := ((if ((v_char_23 in v_map_7)) then (v_map_7[v_char_23]) else (true)) || v_bool_1)], v_array_2[2];
		}
	}
	var v_map_8: map<char, char> := v_map_3;
	var v_seq_8: seq<char> := ['E', 'Q'];
	var v_seq_9: seq<char> := v_seq_8;
	var v_int_21: int := 24;
	var v_int_22: int := safe_index_seq(v_seq_9, v_int_21);
	var v_int_23: int := v_int_22;
	var v_seq_10: seq<char> := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_23 := 'r']) else (v_seq_8));
	var v_int_24: int := (6 % 6);
	var v_char_24: char := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_24]) else ((match 'M' {
		case _ => 'e'
	})));
	var v_seq_11: seq<char> := v_seq_9;
	var v_int_25: int := (if (false) then (19) else (6));
	match (if ((v_char_24 in v_map_8)) then (v_map_8[v_char_24]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_25]) else (v_char_15)))) {
		case _ => {
			var v_map_20: map<char, map<char, map<char, int>>> := map['W' := map['R' := map['r' := 27, 'p' := 26]], 'F' := map['k' := map['Z' := 13]], 'f' := map['l' := map['W' := 9], 'm' := map['v' := 22, 'x' := 11, 'g' := 26, 'l' := 9], 'a' := map['d' := 13, 'P' := 24], 'y' := map['G' := 10], 'K' := map['q' := -20, 'A' := 17]], 'I' := map['H' := map['W' := 2, 'p' := 7], 'K' := map['t' := 8, 'y' := 15], 'X' := map['O' := 10]]];
			var v_char_36: char := 'w';
			var v_map_21: map<char, map<char, int>> := (if ((v_char_36 in v_map_20)) then (v_map_20[v_char_36]) else (map['u' := map['A' := 11, 'e' := 18, 'y' := 20, 'c' := 11, 'v' := 15], 'b' := map['I' := 0, 'k' := 11, 'O' := 0, 'c' := 10], 'H' := map['A' := 16, 'b' := 0, 'Y' := 17], 'd' := map['l' := -15, 'Z' := 24, 'L' := 6]]));
			var v_char_37: char := v_char_15;
			var v_map_23: map<char, int> := (if ((v_char_37 in v_map_21)) then (v_map_21[v_char_37]) else ((map['W' := -4, 'L' := 1, 'Y' := 27, 'E' := 24, 't' := 20] - {'D', 'r', 'U'})));
			var v_seq_27: seq<char> := v_seq_10;
			var v_int_42: int := (if (true) then (25) else (19));
			var v_char_39: char := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_42]) else (v_char_11));
			var v_map_22: map<char, int> := map['S' := -17, 'O' := 7, 'F' := 20];
			var v_char_38: char := 'i';
			var v_int_46: int, v_int_47: int := (if ((v_char_39 in v_map_23)) then (v_map_23[v_char_39]) else ((if ((if (false) then (true) else (true))) then ((if ((v_char_38 in v_map_22)) then (v_map_22[v_char_38]) else (13))) else ((if (true) then (3) else (-22)))))), v_int_15;
			for v_int_41 := v_int_46 to v_int_47 
				invariant (v_int_47 - v_int_41 >= 0)
			{
				var v_seq_28: seq<char> := ['Q', 'N'];
				var v_int_43: int := 14;
				var v_map_24: map<char, map<bool, bool>> := map['j' := map[true := false, false := true], 'e' := map[true := false]];
				var v_char_40: char := 'x';
				var v_seq_29: seq<map<bool, bool>> := [map[false := false, false := false, true := true, false := true], map[false := true, false := false, false := true, false := false, false := false]];
				var v_int_44: int := 15;
				var v_map_25: map<char, seq<map<bool, bool>>> := map['g' := [], 'v' := [map[true := false, true := false, true := false]], 'i' := [map[false := false, false := false], map[false := false]], 'r' := [map[false := false, true := false, false := false], map[true := false, false := true, true := false], map[true := true, true := true]], 'S' := []];
				var v_char_41: char := 'K';
				var v_seq_30: seq<map<bool, bool>> := (if ((v_char_41 in v_map_25)) then (v_map_25[v_char_41]) else ([map[true := true, true := true, false := false], map[true := true], map[true := true, false := true, false := true, true := false, true := false], map[false := true, false := true]]));
				var v_map_26: map<char, int> := map['l' := 11];
				var v_char_42: char := 'p';
				var v_int_45: int := (if ((v_char_42 in v_map_26)) then (v_map_26[v_char_42]) else (28));
				return (match 't' {
					case _ => (match 'T' {
						case _ => (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_43]) else ('c'))
					})
				}), v_int_16, ((match 'B' {
					case _ => (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_44]) else (map[false := false, false := true]))
				}) + (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_45]) else (map[false := true][false := false]))), v_int_23;
			}
			var v_map_27: map<char, char> := v_map_3;
			var v_seq_31: seq<char> := v_seq_9;
			var v_int_48: int := v_int_22;
			var v_char_43: char := (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_48]) else (v_char_24));
			var v_seq_32: seq<char> := ['k', 'v', 'B', 'f'];
			var v_seq_34: seq<char> := (if ((|v_seq_32| > 0)) then (v_seq_32[17..0]) else (v_seq_32));
			var v_seq_33: seq<int> := [6, 5];
			var v_int_49: int := -10;
			var v_seq_38: seq<char> := (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_15..(if ((|v_seq_33| > 0)) then (v_seq_33[v_int_49]) else (27))]) else (v_seq_34));
			var v_seq_35: seq<int> := [28, 15, 26, 6];
			var v_seq_36: seq<int> := v_seq_35;
			var v_int_50: int := 18;
			var v_int_51: int := safe_index_seq(v_seq_36, v_int_50);
			var v_int_52: int := v_int_51;
			var v_seq_37: seq<int> := (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_52 := 1]) else (v_seq_35));
			var v_int_53: int := (match 'D' {
				case _ => 8
			});
			var v_int_54: int := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_53]) else ((if (true) then (7) else (29))));
			var v_seq_39: seq<char> := ['V', 'p', 'U', 'J'];
			var v_seq_40: seq<char> := v_seq_39;
			var v_int_55: int := 14;
			var v_int_56: int := safe_index_seq(v_seq_40, v_int_55);
			var v_int_57: int := v_int_56;
			var v_seq_41: seq<char> := (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_57 := 'v']) else (v_seq_39));
			var v_map_28: map<char, int> := map['z' := -4, 'a' := 20, 'z' := 10];
			var v_char_44: char := 'a';
			var v_int_58: int := (if ((v_char_44 in v_map_28)) then (v_map_28[v_char_44]) else (-11));
			v_char_12, v_char_44, v_char_24, v_char_14 := (if ((v_char_43 in v_map_27)) then (v_map_27[v_char_43]) else (v_char_37)), v_char_13, (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_54]) else ((if ((|v_seq_41| > 0)) then (v_seq_41[v_int_58]) else (v_char_36)))), v_char_37;
			assert true;
			expect true;
			var v_seq_42: seq<int> := [14, 9];
			var v_int_60: int := 22;
			var v_int_78: int, v_int_79: int := v_int_57, ((match 'r' {
				case _ => (if (true) then (-16) else (0))
			}) + ((6.59).Floor - (if ((|v_seq_42| > 0)) then (v_seq_42[v_int_60]) else (3))));
			for v_int_59 := v_int_78 to v_int_79 
				invariant (v_int_79 - v_int_59 >= 0)
			{
				var v_seq_43: seq<bool> := [false, false, true, true];
				var v_int_61: int := -5;
				var v_seq_44: seq<char> := ['t'];
				var v_seq_45: seq<char> := v_seq_44;
				var v_int_62: int := 27;
				var v_int_63: int := safe_index_seq(v_seq_45, v_int_62);
				var v_int_64: int := v_int_63;
				var v_seq_46: seq<char> := (if ((|v_seq_44| > 0)) then (v_seq_44[v_int_64 := 'l']) else (v_seq_44));
				var v_int_65: int := (match 'W' {
					case _ => 29
				});
				var v_seq_47: seq<char> := [];
				var v_int_66: int := 16;
				var v_seq_49: seq<int> := (match 'y' {
					case _ => [25, 22, 13, 10]
				});
				var v_seq_48: seq<int> := [];
				var v_int_67: int := 5;
				var v_seq_50: seq<int> := (if ((|v_seq_49| > 0)) then (v_seq_49[(if ((|v_seq_48| > 0)) then (v_seq_48[v_int_67]) else (28))..(4.45).Floor]) else (v_seq_49));
				var v_int_68: int := v_int_66;
				var v_seq_51: seq<multiset<char>> := [multiset{'A'}, multiset({'N', 'H', 'D', 'Y'})];
				var v_int_69: int := 0;
				var v_seq_52: seq<map<bool, bool>> := [map[false := false], map[false := false, true := true, true := true], map[true := false, false := true, true := true]];
				var v_seq_54: seq<map<bool, bool>> := (if ((|v_seq_52| > 0)) then (v_seq_52[4..0]) else (v_seq_52));
				var v_seq_53: seq<int> := [22, 15, -28, -26];
				var v_int_70: int := 26;
				var v_seq_55: seq<map<bool, bool>> := (if ((|v_seq_54| > 0)) then (v_seq_54[(if ((|v_seq_53| > 0)) then (v_seq_53[v_int_70]) else (5))..(if (false) then (8) else (25))]) else (v_seq_54));
				var v_int_71: int := (match 'B' {
					case _ => (-9 + 7)
				});
				var v_map_29: map<char, bool> := map['p' := false];
				var v_char_45: char := 'm';
				var v_map_30: map<char, bool> := map['i' := false, 'W' := true];
				var v_char_46: char := 'j';
				var v_seq_56: seq<bool> := [true, true, false];
				var v_int_72: int := 6;
				var v_array_8: array<char> := new char[4] ['z', 'b', 'F', 'g'];
				var v_array_9: array<char> := new char[3] ['J', 'n', 'X'];
				var v_seq_57: seq<int> := [22, 26, 22];
				var v_seq_58: seq<int> := v_seq_57;
				var v_int_73: int := 0;
				var v_int_74: int := safe_index_seq(v_seq_58, v_int_73);
				var v_int_75: int := v_int_74;
				var v_seq_59: seq<int> := (if ((|v_seq_57| > 0)) then (v_seq_57[v_int_75 := 3]) else (v_seq_57));
				var v_map_31: map<char, int> := map['t' := 26, 'F' := 14, 'z' := 18, 'U' := 22, 'k' := 16];
				var v_char_47: char := 'g';
				var v_int_76: int := (if ((v_char_47 in v_map_31)) then (v_map_31[v_char_47]) else (-7));
				var v_seq_60: seq<int> := [];
				var v_int_77: int := 21;
				return (if ((if ((if (false) then (false) else (false))) then ((if ((|v_seq_43| > 0)) then (v_seq_43[v_int_61]) else (true))) else ((if (true) then (false) else (false))))) then ((match 'K' {
					case _ => v_char_44
				})) else ((if ((|v_seq_46| > 0)) then (v_seq_46[v_int_65]) else ((if ((|v_seq_47| > 0)) then (v_seq_47[v_int_66]) else ('c')))))), (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_68]) else (|(if ((|v_seq_51| > 0)) then (v_seq_51[v_int_69]) else (multiset{'R', 'N', 'l', 'y'}))|)), (if ((|v_seq_55| > 0)) then (v_seq_55[v_int_71]) else (map[true := true, true := false, false := true, true := false][true := false][(if ((v_char_45 in v_map_29)) then (v_map_29[v_char_45]) else (true)) := v_int_bool_int_1.1])), (if ((if (v_bool_1) then ((if ((v_char_46 in v_map_30)) then (v_map_30[v_char_46]) else (true))) else ((if ((|v_seq_56| > 0)) then (v_seq_56[v_int_72]) else (true))))) then ((if (false) then (v_array_8) else (v_array_9)).Length) else ((if ((|v_seq_59| > 0)) then (v_seq_59[v_int_76]) else ((if ((|v_seq_60| > 0)) then (v_seq_60[v_int_77]) else (16))))));
			}
		}
		
	}
	
	var v_seq_61: seq<bool> := [false, false];
	var v_seq_62: seq<bool> := v_seq_61;
	var v_int_80: int := 8;
	var v_int_81: int := safe_index_seq(v_seq_62, v_int_80);
	var v_int_82: int := v_int_81;
	var v_seq_63: seq<bool> := (if ((|v_seq_61| > 0)) then (v_seq_61[v_int_82 := false]) else (v_seq_61));
	var v_int_83: int := (26 - 15);
	var v_map_32: map<char, char> := map['w' := 'A', 'e' := 'w', 'e' := 'K', 'Q' := 'i']['J' := 'u'];
	var v_char_48: char := (if (true) then ('H') else ('F'));
	var v_seq_64: seq<char> := ['m', 'Z', 'w', 'P'];
	var v_int_84: int := 10;
	var v_map_34: map<char, char> := (if (true) then (map['w' := 'q', 'T' := 'g', 'e' := 'h']) else (map['c' := 'Q', 'h' := 'l', 'Z' := 'h']));
	var v_char_50: char := v_char_14;
	var v_map_33: map<char, char> := map['S' := 'D', 'O' := 'G', 'z' := 'k', 'j' := 'L', 'U' := 'q'];
	var v_char_49: char := 'z';
	var v_seq_65: seq<char> := ['q'];
	var v_seq_67: seq<char> := (if ((|v_seq_65| > 0)) then (v_seq_65[20..2]) else (v_seq_65));
	var v_seq_68: seq<char> := v_seq_67;
	var v_seq_66: seq<int> := [-11, -5, 23, 3];
	var v_int_85: int := -3;
	var v_int_86: int := (if ((|v_seq_66| > 0)) then (v_seq_66[v_int_85]) else (23));
	var v_int_87: int := safe_index_seq(v_seq_68, v_int_86);
	var v_int_88: int := v_int_87;
	var v_seq_69: seq<char> := (if ((|v_seq_67| > 0)) then (v_seq_67[v_int_88 := (if (false) then ('y') else ('M'))]) else (v_seq_67));
	var v_int_89: int := (if ((true && false)) then ((-17 - -6)) else ((match 'E' {
		case _ => 22
	})));
	var v_map_35: map<char, char> := map['m' := 'R', 's' := 'i', 'k' := 'N', 'H' := 'E'];
	var v_char_51: char := 'A';
	var v_seq_70: seq<char> := ['D', 'x', 'A'];
	var v_int_90: int := 16;
	var v_map_36: map<char, seq<map<char, char>>> := map['C' := [map['l' := 'x']], 'E' := []];
	var v_char_52: char := 'b';
	var v_seq_71: seq<map<char, char>> := (if ((v_char_52 in v_map_36)) then (v_map_36[v_char_52]) else ([map['e' := 'f', 'n' := 'q', 'B' := 'R'], map['N' := 'o', 'y' := 'P'], map['f' := 'F', 'J' := 'c', 'Y' := 'S', 'd' := 'Q', 'a' := 'G'], map['U' := 'U', 'E' := 'w']]));
	var v_int_91: int := (if (true) then (9) else (1));
	var v_map_40: map<char, char> := (if ((|v_seq_71| > 0)) then (v_seq_71[v_int_91]) else ((match 'U' {
		case _ => map['J' := 'w', 'N' := 'k', 'd' := 'Q', 'g' := 'F', 'G' := 'q']
	})));
	var v_map_37: map<char, char> := map['L' := 'x', 'R' := 'w'];
	var v_char_53: char := 'j';
	var v_map_38: map<char, char> := map['X' := 'm', 'S' := 'X', 'R' := 't', 'v' := 'l'];
	var v_char_54: char := 'P';
	var v_char_56: char := (match 'u' {
		case _ => (if ((v_char_54 in v_map_38)) then (v_map_38[v_char_54]) else ('h'))
	});
	var v_map_39: map<char, char> := map['g' := 'm', 'r' := 'y']['L' := 'G'];
	var v_char_55: char := v_char_48;
	v_char_55, v_char_15, v_char_50 := (if ((if ((|v_seq_63| > 0)) then (v_seq_63[v_int_83]) else ((match 'L' {
		case _ => false
	})))) then ((if ((v_char_48 in v_map_32)) then (v_map_32[v_char_48]) else ((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_84]) else ('X'))))) else ((if ((v_char_50 in v_map_34)) then (v_map_34[v_char_50]) else ((if ((v_char_49 in v_map_33)) then (v_map_33[v_char_49]) else ('R')))))), (if ((|v_seq_69| > 0)) then (v_seq_69[v_int_89]) else ((match 'a' {
		case _ => (if ((|v_seq_70| > 0)) then (v_seq_70[v_int_90]) else ('R'))
	}))), (if ((v_char_56 in v_map_40)) then (v_map_40[v_char_56]) else ((if ((v_char_55 in v_map_39)) then (v_map_39[v_char_55]) else (v_char_14))));
	var v_seq_72: seq<char> := [];
	var v_seq_73: seq<char> := (if ((|v_seq_72| > 0)) then (v_seq_72[-18..0]) else (v_seq_72));
	var v_map_41: map<char, int> := map['w' := -28, 'K' := 15, 'm' := 13];
	var v_char_57: char := 'x';
	var v_int_92: int := (if ((v_char_57 in v_map_41)) then (v_map_41[v_char_57]) else (2));
	var v_map_42: map<char, char> := (map['P' := 'D', 'j' := 'u', 'F' := 'b', 'Z' := 'H'] + map['h' := 'H', 'y' := 'I', 'Y' := 'Q']);
	var v_char_58: char := v_char_11;
	var v_map_43: map<char, bool> := map['u' := true];
	var v_char_59: char := 'f';
	return (match 'R' {
		case _ => (if ((v_char_58 in v_map_42)) then (v_map_42[v_char_58]) else ((if (true) then ('X') else ('i'))))
	}), (p_m_method_1_2[2]).Floor, ((if (v_bool_1) then (map[true := false, false := true][false := true]) else (map[false := false, true := true, false := false][false := true])) + map[false := false][false := true][(if ((v_char_59 in v_map_43)) then (v_map_43[v_char_59]) else (true)) := (if (false) then (true) else (false))]), v_int_91;
}

method Main() returns ()
{
	var v_int_8: int := 27;
	var v_int_real_real_1: (int, real, real) := (10, 7.37, -27.15);
	var v_int_real_real_2: (int, real, real) := (20, 23.32, -14.86);
	var v_int_real_real_3: (int, real, real) := (10, -5.13, -28.00);
	var v_int_real_real_4: (int, real, real) := (24, -23.26, 15.63);
	var v_int_real_real_5: (int, real, real) := (27, -10.11, -14.40);
	var v_int_real_real_6: (int, real, real) := (18, 23.59, -18.47);
	var v_int_real_real_7: (int, real, real) := (29, -16.28, -27.43);
	var v_int_real_real_8: (int, real, real) := (19, 23.76, 17.29);
	var v_int_real_real_9: (int, real, real) := (25, -29.01, -17.40);
	var v_int_real_real_10: (int, real, real) := (23, -3.34, -24.46);
	var v_array_1: array<map<(int, real, real), multiset<bool>>> := new map<(int, real, real), multiset<bool>>[5] [map[v_int_real_real_1 := multiset{}], map[v_int_real_real_2 := multiset({}), v_int_real_real_3 := multiset{}, v_int_real_real_4 := multiset{}, v_int_real_real_5 := multiset({true, true, false})], map[v_int_real_real_6 := multiset{}], map[v_int_real_real_7 := multiset{false, true, true, false}, v_int_real_real_8 := multiset{}], map[v_int_real_real_9 := multiset({true}), v_int_real_real_10 := multiset({false, true, false, false})]];
	var v_int_9: int := v_array_1.Length;
	var v_int_10: int := safe_division(v_int_8, v_int_9);
	var v_int_103: int, v_int_104: int := v_int_10, v_int_real_real_2.0;
	for v_int_7 := v_int_103 to v_int_104 
		invariant (v_int_104 - v_int_7 >= 0) && ((((v_int_7 == 11)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 12)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 13)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 14)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 10)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 19)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 15)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 16)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 9)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 17)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 8)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 18)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 7)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 6)) ==> ((((v_int_8 == 5))))) && (((v_int_7 == 5)) ==> ((((v_int_8 == 27))))))
	{
		var v_char_65: char := 'w';
		var v_char_66: char := 'O';
		var v_char_67: char := 'C';
		var v_map_44: map<bool, int> := m_method_8(v_char_65, v_char_66, v_char_67);
		var v_map_50: map<bool, int> := (match 't' {
			case 'o' => (match 'R' {
				case _ => map[false := 16]
			})
			case _ => v_map_44
		})[(({'z'} - {'U', 'I'}) > (map['x' := 'p', 'n' := 'P', 'M' := 'j', 'h' := 'U', 'o' := 'm']).Values) := v_int_real_real_1.0];
		var v_array_10: array<real> := new real[3] [-1.42, -19.15, 3.96];
		var v_array_11: array<real> := new real[3] [3.33, 11.45, -17.02];
		var v_array_12: array<real> := new real[5] [-0.19, -25.16, 28.37, 15.21, 10.24];
		var v_array_13: array<real> := new real[5] [5.97, 21.04, -20.36, 19.54, -18.81];
		var v_array_14: array<real> := new real[4] [-4.51, -20.83, 1.36, 0.57];
		var v_array_15: array<real> := new real[3] [-27.22, -15.81, -6.06];
		var v_seq_74: seq<char> := ['k', 'a'];
		var v_int_96: int := 27;
		var v_seq_154: seq<char> := v_seq_74;
		var v_int_199: int := v_int_96;
		var v_int_200: int := safe_index_seq(v_seq_154, v_int_199);
		v_int_96 := v_int_200;
		var v_array_16: array<real> := new real[3] [-19.69, 6.95, -15.76];
		var v_array_17: array<real> := new real[5] [20.22, -21.12, -16.13, 29.88, -7.61];
		var v_array_18: array<real> := new real[3] [-19.33, -7.15, 26.16];
		var v_map_45: map<char, array<real>> := map['r' := v_array_16, 'x' := v_array_17, 't' := v_array_18];
		var v_char_68: char := 'v';
		var v_array_19: array<real> := new real[5] [-3.62, 15.20, 16.12, -3.03, -3.07];
		var v_map_47: map<char, array<real>> := (map['t' := v_array_10] + map['Q' := v_array_11, 'q' := v_array_12, 'K' := v_array_13, 'f' := v_array_14, 'k' := v_array_15])[(if ((|v_seq_74| > 0)) then (v_seq_74[v_int_96]) else ('k')) := (if ((v_char_68 in v_map_45)) then (v_map_45[v_char_68]) else (v_array_19))];
		var v_seq_75: seq<map<char, char>> := [map['L' := 's', 'c' := 'f', 'f' := 't', 'J' := 'w'], map['M' := 'j']];
		var v_int_97: int := -29;
		var v_seq_155: seq<map<char, char>> := v_seq_75;
		var v_int_201: int := v_int_97;
		var v_int_202: int := safe_index_seq(v_seq_155, v_int_201);
		v_int_97 := v_int_202;
		var v_map_46: map<char, char> := (if ((|v_seq_75| > 0)) then (v_seq_75[v_int_97]) else (map['A' := 'G', 'A' := 'C', 'f' := 'I']));
		var v_char_69: char := 'g';
		var v_char_70: char := 't';
		var v_char_71: char := 'q';
		var v_char_72: char := m_method_4(v_char_69, v_char_70, v_char_71);
		var v_char_73: char := v_char_72;
		var v_char_74: char := (if ((v_char_73 in v_map_46)) then (v_map_46[v_char_73]) else ((match 'a' {
			case 'B' => 'a'
			case 't' => 'c'
			case _ => 'R'
		})));
		var v_array_20: array<real> := new real[5] [-6.37, 25.66, 7.80, -21.70, 14.04];
		var v_array_21: array<real> := new real[5] [21.17, 2.81, -3.54, 9.74, 18.97];
		var v_array_22: array<real> := new real[5] [28.28, -24.81, 4.77, 24.47, 10.94];
		var v_array_23: array<real> := new real[5] [28.69, -18.63, -13.89, -18.22, 11.39];
		var v_seq_76: seq<array<real>> := [v_array_20, v_array_21, v_array_22, v_array_23];
		var v_seq_156: seq<array<real>> := v_seq_76;
		var v_int_205: int := 12;
		var v_int_206: int := 27;
		var v_int_207: int, v_int_208: int := safe_subsequence(v_seq_156, v_int_205, v_int_206);
		var v_int_203: int, v_int_204: int := v_int_207, v_int_208;
		var v_seq_77: seq<array<real>> := (if ((|v_seq_76| > 0)) then (v_seq_76[v_int_203..v_int_204]) else (v_seq_76));
		var v_int_98: int := (if (true) then (5) else (18));
		var v_array_24: array<real> := new real[4];
		v_array_24[0] := -10.42;
		v_array_24[1] := -24.23;
		v_array_24[2] := -11.79;
		v_array_24[3] := 8.96;
		var v_array_25: array<real> := new real[5] [-7.24, -29.74, 23.86, 2.48, -24.14];
		var v_array_26: array<real> := new real[3] [-2.60, -28.95, -21.18];
		var v_seq_78: seq<array<real>> := [v_array_24, v_array_25, v_array_26];
		var v_int_99: int := 13;
		var v_seq_157: seq<array<real>> := v_seq_78;
		var v_int_209: int := v_int_99;
		var v_int_210: int := safe_index_seq(v_seq_157, v_int_209);
		v_int_99 := v_int_210;
		var v_array_27: array<real> := new real[3] [7.00, 24.09, 4.45];
		var v_array_28: array<real> := (if ((v_char_74 in v_map_47)) then (v_map_47[v_char_74]) else ((if ((|v_seq_77| > 0)) then (v_seq_77[v_int_98]) else ((if ((|v_seq_78| > 0)) then (v_seq_78[v_int_99]) else (v_array_27))))));
		var v_map_49: map<char, bool> := ((if (false) then (map['h' := false, 'i' := true]) else (map['X' := true, 'L' := true])) - ({} - {'T', 'M', 'x'}));
		var v_seq_79: seq<char> := [];
		var v_int_100: int := 28;
		var v_map_48: map<char, char> := map['t' := 'D', 'A' := 'd', 'L' := 'W'];
		var v_char_75: char := 'u';
		var v_char_76: char := (match 'g' {
			case 'Y' => (if ((|v_seq_79| > 0)) then (v_seq_79[v_int_100]) else ('q'))
			case _ => (if ((v_char_75 in v_map_48)) then (v_map_48[v_char_75]) else ('Z'))
		});
		var v_bool_2: bool := (if ((v_char_76 in v_map_49)) then (v_map_49[v_char_76]) else ((match 'E' {
			case 'Q' => (if (false) then (false) else (false))
			case _ => ('m' in map['t' := 'I'])
		})));
		var v_char_77: char, v_int_101: int, v_map_51: map<bool, bool>, v_int_102: int := m_method_1(v_map_50, v_array_28, v_bool_2);
		v_char_74, v_int_8, v_map_51, v_int_102 := v_char_77, v_int_101, v_map_51, v_int_102;
		var v_int_real_real_11: (int, real, real) := (19, 23.76, 17.29);
		var v_int_real_real_12: (int, real, real) := (29, -16.28, -27.43);
		var v_int_real_real_13: (int, real, real) := (18, 23.59, -18.47);
		var v_int_real_real_14: (int, real, real) := (27, -10.11, -14.40);
		var v_int_real_real_15: (int, real, real) := (24, -23.26, 15.63);
		var v_int_real_real_16: (int, real, real) := (10, -5.13, -28.00);
		var v_int_real_real_17: (int, real, real) := (20, 23.32, -14.86);
		var v_int_real_real_18: (int, real, real) := (10, 7.37, -27.15);
		var v_int_real_real_19: (int, real, real) := (18, 23.59, -18.47);
		var v_int_real_real_20: (int, real, real) := (23, -3.34, -24.46);
		var v_int_real_real_21: (int, real, real) := (19, 23.76, 17.29);
		var v_int_real_real_22: (int, real, real) := (29, -16.28, -27.43);
		var v_int_real_real_23: (int, real, real) := (10, 7.37, -27.15);
		var v_int_real_real_24: (int, real, real) := (23, -3.34, -24.46);
		var v_int_real_real_25: (int, real, real) := (25, -29.01, -17.40);
		var v_int_real_real_26: (int, real, real) := (25, -29.01, -17.40);
		var v_int_real_real_27: (int, real, real) := (24, -23.26, 15.63);
		var v_int_real_real_28: (int, real, real) := (27, -10.11, -14.40);
		var v_int_real_real_29: (int, real, real) := (10, -5.13, -28.00);
		var v_int_real_real_30: (int, real, real) := (20, 23.32, -14.86);
		print "v_array_13[4]", " ", (v_array_13[4] == -18.81), " ", "v_array_20[1]", " ", (v_array_20[1] == 25.66), " ", "v_array_11[2]", " ", (v_array_11[2] == -17.02), " ", "v_array_14[1]", " ", (v_array_14[1] == -20.83), " ", "v_array_17[0]", " ", (v_array_17[0] == 20.22), " ", "v_array_22[3]", " ", (v_array_22[3] == 24.47), " ", "v_array_25[3]", " ", (v_array_25[3] == 2.48), " ", "v_array_26[0]", " ", (v_array_26[0] == -2.60), " ", "v_int_101", " ", v_int_101, " ", "v_int_102", " ", v_int_102, " ", "v_array_23[1]", " ", (v_array_23[1] == -18.63), " ", "v_array_19[2]", " ", (v_array_19[2] == 16.12), " ", "v_array_16[2]", " ", (v_array_16[2] == -15.76), " ", "v_array_14[0]", " ", (v_array_14[0] == -4.51), " ", "v_array_20[0]", " ", (v_array_20[0] == -6.37), " ", "v_array_19[1]", " ", (v_array_19[1] == 15.20), " ", "v_array_13[3]", " ", (v_array_13[3] == 19.54), " ", "v_array_22[2]", " ", (v_array_22[2] == 4.77), " ", "v_array_11[1]", " ", (v_array_11[1] == 11.45), " ", "v_array_25[4]", " ", (v_array_25[4] == -24.14), " ", "v_array_26[1]", " ", (v_array_26[1] == -28.95), " ", "v_array_23[2]", " ", (v_array_23[2] == -13.89), " ", "v_array_11", " ", (v_array_11 == v_array_11), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "v_array_14[3]", " ", (v_array_14[3] == 0.57), " ", "v_array_17[2]", " ", (v_array_17[2] == -16.13), " ", "v_array_21[0]", " ", (v_array_21[0] == 21.17), " ", "v_array_12[1]", " ", (v_array_12[1] == -25.16), " ", "v_array_15[0]", " ", (v_array_15[0] == -27.22), " ", "v_array_20[3]", " ", (v_array_20[3] == -21.70), " ", "v_array_25[1]", " ", (v_array_25[1] == -29.74), " ", "v_array_19", " ", (v_array_19 == v_array_19), " ", "v_array_19[4]", " ", (v_array_19[4] == -3.07), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_array_12", " ", (v_array_12 == v_array_12), " ", "v_array_14[2]", " ", (v_array_14[2] == 1.36), " ", "v_array_17[1]", " ", (v_array_17[1] == -21.12), " ", "v_array_20[2]", " ", (v_array_20[2] == 7.80), " ", "v_array_12[0]", " ", (v_array_12[0] == -0.19), " ", "v_array_22[4]", " ", (v_array_22[4] == 10.94), " ", "v_array_25[2]", " ", (v_array_25[2] == 23.86), " ", "v_array_23[0]", " ", (v_array_23[0] == 28.69), " ", "v_array_19[3]", " ", (v_array_19[3] == -3.03), " ", "v_array_15[2]", " ", (v_array_15[2] == -6.06), " ", "v_map_50", " ", (v_map_50 == map[false := 10, true := 17]), " ", "v_array_12[3]", " ", (v_array_12[3] == 15.21), " ", "v_array_13[0]", " ", (v_array_13[0] == 5.97), " ", "v_array_18[1]", " ", (v_array_18[1] == -7.15), " ", "v_array_21[2]", " ", (v_array_21[2] == -3.54), " ", "v_char_77", " ", (v_char_77 == 'O'), " ", "v_array_10[1]", " ", (v_array_10[1] == -19.15), " ", "v_map_51", " ", (v_map_51 == map[false := true, true := true]), " ", "v_array_27[1]", " ", (v_array_27[1] == 24.09), " ", "v_seq_76", " ", (v_seq_76 == [v_array_20, v_array_21, v_array_22, v_array_23]), " ", "v_seq_77", " ", (v_seq_77 == []), " ", "v_array_24[2]", " ", (v_array_24[2] == -11.79), " ", "v_seq_78", " ", (v_seq_78 == [v_array_24, v_array_25, v_array_26]), " ", "v_seq_74", " ", (v_seq_74 == ['k', 'a']), " ", "v_array_17[4]", " ", (v_array_17[4] == -7.61), " ", "v_seq_75", " ", (v_seq_75 == [map['c' := 'f', 'f' := 't', 'J' := 'w', 'L' := 's'], map['M' := 'j']]), " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_array_20", " ", (v_array_20 == v_array_20), " ", "v_array_17[3]", " ", (v_array_17[3] == 29.88), " ", "v_char_69", " ", (v_char_69 == 'g'), " ", "v_char_68", " ", (v_char_68 == 'v'), " ", "v_array_18[0]", " ", (v_array_18[0] == -19.33), " ", "v_array_21[1]", " ", (v_array_21[1] == 2.81), " ", "v_array_12[2]", " ", (v_array_12[2] == 28.37), " ", "v_array_15[1]", " ", (v_array_15[1] == -15.81), " ", "v_array_20[4]", " ", (v_array_20[4] == 14.04), " ", "v_array_10[0]", " ", (v_array_10[0] == -1.42), " ", "v_array_27[2]", " ", (v_array_27[2] == 4.45), " ", "v_array_24[3]", " ", (v_array_24[3] == 8.96), " ", "v_array_25[0]", " ", (v_array_25[0] == -7.24), " ", "v_char_76", " ", (v_char_76 == 'Z'), " ", "v_char_74", " ", (v_char_74 == 'O'), " ", "v_array_28", " ", (v_array_28 == v_array_24), " ", "v_char_73", " ", (v_char_73 == 'e'), " ", "v_array_27", " ", (v_array_27 == v_array_27), " ", "v_char_72", " ", (v_char_72 == 'e'), " ", "v_array_26", " ", (v_array_26 == v_array_26), " ", "v_char_71", " ", (v_char_71 == 'q'), " ", "v_array_25", " ", (v_array_25 == v_array_25), " ", "v_char_70", " ", (v_char_70 == 't'), " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_array_16[1]", " ", (v_array_16[1] == 6.95), " ", "v_bool_2", " ", v_bool_2, " ", "v_array_19[0]", " ", (v_array_19[0] == -3.62), " ", "v_array_13[2]", " ", (v_array_13[2] == -20.36), " ", "v_array_22[1]", " ", (v_array_22[1] == -24.81), " ", "v_array_11[0]", " ", (v_array_11[0] == 3.33), " ", "v_array_21[4]", " ", (v_array_21[4] == 18.97), " ", "v_array_26[2]", " ", (v_array_26[2] == -21.18), " ", "v_array_23[3]", " ", (v_array_23[3] == -18.22), " ", "v_array_24[0]", " ", (v_array_24[0] == -10.42), " ", "v_array_13[1]", " ", (v_array_13[1] == 21.04), " ", "v_array_18[2]", " ", (v_array_18[2] == 26.16), " ", "v_array_12[4]", " ", (v_array_12[4] == 10.24), " ", "v_array_22[0]", " ", (v_array_22[0] == 28.28), " ", "v_array_16[0]", " ", (v_array_16[0] == -19.69), " ", "v_array_10[2]", " ", (v_array_10[2] == 3.96), " ", "v_map_46", " ", (v_map_46 == map['c' := 'f', 'f' := 't', 'J' := 'w', 'L' := 's']), " ", "v_array_21[3]", " ", (v_array_21[3] == 9.74), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_47", " ", (v_map_47 == map['Q' := v_array_11, 'q' := v_array_12, 't' := v_array_10, 'f' := v_array_14, 'K' := v_array_13, 'k' := v_array_19]), " ", "v_map_45", " ", (v_map_45 == map['r' := v_array_16, 't' := v_array_18, 'x' := v_array_17]), " ", "v_int_99", " ", v_int_99, " ", "v_int_98", " ", v_int_98, " ", "v_array_23[4]", " ", (v_array_23[4] == 11.39), " ", "v_array_24[1]", " ", (v_array_24[1] == -24.23), " ", "v_array_27[0]", " ", (v_array_27[0] == 7.00), " ", "v_map_49", " ", (v_map_49 == map['X' := true, 'L' := true]), " ", "v_int_97", " ", v_int_97, " ", "v_int_96", " ", v_int_96, " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -23.26), " ", "v_int_real_real_8", " ", (v_int_real_real_8 == v_int_real_real_11), " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == 15.63), " ", "v_int_real_real_6.0", " ", v_int_real_real_6.0, " ", "v_int_real_real_7", " ", (v_int_real_real_7 == v_int_real_real_12), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 23.32), " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_13), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == -14.86), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_14), " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_15), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_16), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_17), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_18), " ", "v_array_1[2]", " ", (v_array_1[2] == map[v_int_real_real_19 := multiset{}]), " ", "v_int_real_real_10.2", " ", (v_int_real_real_10.2 == -24.46), " ", "v_int_real_real_10.0", " ", v_int_real_real_10.0, " ", "v_int_real_real_10.1", " ", (v_int_real_real_10.1 == -3.34), " ", "v_int_real_real_9.2", " ", (v_int_real_real_9.2 == -17.40), " ", "v_int_real_real_7.2", " ", (v_int_real_real_7.2 == -27.43), " ", "v_int_real_real_9.0", " ", v_int_real_real_9.0, " ", "v_int_real_real_9.1", " ", (v_int_real_real_9.1 == -29.01), " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == -14.40), " ", "v_int_real_real_7.0", " ", v_int_real_real_7.0, " ", "v_int_real_real_7.1", " ", (v_int_real_real_7.1 == -16.28), " ", "v_int_real_real_10", " ", (v_int_real_real_10 == v_int_real_real_20), " ", "v_array_1[3]", " ", (v_array_1[3] == map[v_int_real_real_21 := multiset{}, v_int_real_real_22 := multiset{false, false, true, true}]), " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == -28.00), " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == -10.11), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == -27.15), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == -5.13), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == 7.37), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[0]", " ", (v_array_1[0] == map[v_int_real_real_23 := multiset{}]), " ", "v_array_1[4]", " ", (v_array_1[4] == map[v_int_real_real_24 := multiset{false, true}, v_int_real_real_25 := multiset{true}]), " ", "v_int_8", " ", v_int_8, " ", "v_int_10", " ", v_int_10, " ", "v_int_real_real_8.1", " ", (v_int_real_real_8.1 == 23.76), " ", "v_int_real_real_8.2", " ", (v_int_real_real_8.2 == 17.29), " ", "v_int_real_real_6.1", " ", (v_int_real_real_6.1 == 23.59), " ", "v_int_real_real_6.2", " ", (v_int_real_real_6.2 == -18.47), " ", "v_int_real_real_8.0", " ", v_int_real_real_8.0, " ", "v_int_real_real_9", " ", (v_int_real_real_9 == v_int_real_real_26), " ", "v_array_1[1]", " ", (v_array_1[1] == map[v_int_real_real_27 := multiset{}, v_int_real_real_28 := multiset{false, true}, v_int_real_real_29 := multiset{}, v_int_real_real_30 := multiset{}]), "\n";
	}
	var v_map_54: map<char, char> := (map['B' := 'F', 'd' := 'H'] - {'S', 'j'})[(if (true) then ('D') else ('d')) := (if (true) then ('y') else ('H'))];
	var v_map_52: map<char, char> := map['Z' := 't', 'q' := 'G', 'M' := 'I', 'H' := 'R'];
	var v_char_78: char := 'b';
	var v_char_80: char := (if ((match 'S' {
		case 'C' => true
		case _ => false
	})) then ((if ((v_char_78 in v_map_52)) then (v_map_52[v_char_78]) else ('B'))) else ((match 'I' {
		case 'K' => 'E'
		case _ => 'G'
	})));
	var v_map_53: map<char, bool> := map['j' := true, 'o' := true, 'n' := false, 'D' := true, 'u' := true];
	var v_char_79: char := 'I';
	var v_seq_80: seq<char> := ['i', 'h', 'f'];
	var v_seq_81: seq<char> := v_seq_80;
	var v_int_105: int := 25;
	var v_int_106: int := safe_index_seq(v_seq_81, v_int_105);
	var v_int_107: int := v_int_106;
	var v_seq_82: seq<char> := (if ((|v_seq_80| > 0)) then (v_seq_80[v_int_107 := 'J']) else (v_seq_80));
	var v_int_108: int := (28 / 11);
	var v_map_55: map<char, char> := map['d' := 'm', 'a' := 'w', 'n' := 'S', 'J' := 'Y']['q' := 'V'];
	var v_char_81: char := v_char_78;
	var v_seq_83: seq<char> := ['a', 'F', 'g'];
	var v_int_109: int := 5;
	var v_seq_161: seq<char> := v_seq_83;
	var v_int_221: int := v_int_109;
	var v_int_222: int := safe_index_seq(v_seq_161, v_int_221);
	v_int_109 := v_int_222;
	v_char_80, v_char_78 := (if ((v_char_80 in v_map_54)) then (v_map_54[v_char_80]) else ((if ((if ((v_char_79 in v_map_53)) then (v_map_53[v_char_79]) else (true))) then ((match 'R' {
		case 'H' => 'r'
		case _ => 'o'
	})) else (v_char_79)))), (match 'w' {
		case 'Y' => (if ((|v_seq_82| > 0)) then (v_seq_82[v_int_108]) else ((match 'P' {
			case _ => 'b'
		})))
		case _ => (if ((v_char_81 in v_map_55)) then (v_map_55[v_char_81]) else ((if ((|v_seq_83| > 0)) then (v_seq_83[v_int_109]) else ('H'))))
	});
	var v_seq_84: seq<char> := ['s', 'M', 'x', 'S'];
	var v_seq_85: seq<char> := v_seq_84;
	var v_int_110: int := 2;
	var v_int_111: int := safe_index_seq(v_seq_85, v_int_110);
	var v_int_112: int := v_int_111;
	var v_seq_87: seq<char> := (if ((|v_seq_84| > 0)) then (v_seq_84[v_int_112 := 'd']) else (v_seq_84));
	var v_seq_88: seq<char> := v_seq_87;
	var v_seq_86: seq<int> := [0, 2, 6, 29];
	var v_int_113: int := 0;
	var v_int_114: int := (if ((|v_seq_86| > 0)) then (v_seq_86[v_int_113]) else (11));
	var v_int_115: int := safe_index_seq(v_seq_88, v_int_114);
	var v_int_116: int := v_int_115;
	var v_seq_91: seq<char> := (if ((|v_seq_87| > 0)) then (v_seq_87[v_int_116 := v_char_80]) else (v_seq_87));
	var v_seq_89: seq<int> := [];
	var v_seq_90: seq<int> := (if ((|v_seq_89| > 0)) then (v_seq_89[1..7]) else (v_seq_89));
	var v_map_56: map<char, int> := map['i' := 27, 'd' := 0, 'F' := 21];
	var v_char_82: char := 'L';
	var v_int_117: int := (if ((v_char_82 in v_map_56)) then (v_map_56[v_char_82]) else (18));
	var v_map_57: map<char, int> := map['u' := 3, 's' := 3, 'e' := 26, 'E' := 22];
	var v_char_83: char := 'w';
	var v_int_118: int := (if ((|v_seq_90| > 0)) then (v_seq_90[v_int_117]) else ((if ((v_char_83 in v_map_57)) then (v_map_57[v_char_83]) else (8))));
	var v_seq_163: seq<char> := v_seq_91;
	var v_int_225: int := v_int_118;
	var v_int_226: int := safe_index_seq(v_seq_163, v_int_225);
	v_int_118 := v_int_226;
	var v_seq_92: seq<char> := [];
	var v_int_119: int := 5;
	var v_seq_93: seq<bool> := [false, false];
	var v_int_120: int := 29;
	var v_seq_94: seq<char> := ['W', 'R', 'M'];
	var v_int_121: int := 20;
	var v_seq_162: seq<char> := v_seq_94;
	var v_int_223: int := v_int_121;
	var v_int_224: int := safe_index_seq(v_seq_162, v_int_223);
	v_int_121 := v_int_224;
	var v_map_58: map<char, char> := (match 'r' {
		case 'Y' => map['Z' := 'V', 'm' := 'f', 'y' := 'I']
		case 'v' => map['U' := 'B']
		case _ => map['p' := 'j']
	})[(if ((|v_seq_94| > 0)) then (v_seq_94[v_int_121]) else ('W')) := (if (true) then ('I') else ('f'))];
	var v_char_84: char := v_char_82;
	v_char_84, v_char_83, v_char_82, v_char_78 := v_char_80, (if ((|v_seq_91| > 0)) then (v_seq_91[v_int_118]) else ((match 'w' {
		case _ => (match 'G' {
			case _ => 'f'
		})
	}))), (match 'Z' {
		case 'm' => (if ((if ((|v_seq_93| > 0)) then (v_seq_93[v_int_120]) else (true))) then ((match 'E' {
			case _ => 'o'
		})) else ((match 'E' {
			case _ => 'T'
		})))
		case _ => (match 'p' {
			case 'u' => (match 'e' {
				case _ => 'n'
			})
			case _ => (match 'Y' {
				case 'P' => 'E'
				case _ => 'f'
			})
		})
	}), (if ((v_char_84 in v_map_58)) then (v_map_58[v_char_84]) else (v_char_83));
	var v_seq_95: seq<int> := [24, 24];
	var v_seq_164: seq<int> := v_seq_95;
	var v_int_229: int := -19;
	var v_int_230: int := 28;
	var v_int_231: int, v_int_232: int := safe_subsequence(v_seq_164, v_int_229, v_int_230);
	var v_int_227: int, v_int_228: int := v_int_231, v_int_232;
	var v_seq_96: seq<int> := [];
	var v_seq_97: seq<int> := v_seq_96;
	var v_int_124: int := -7;
	var v_int_125: int := safe_index_seq(v_seq_97, v_int_124);
	var v_int_126: int := v_int_125;
	var v_seq_98: seq<int> := ((if ((|v_seq_95| > 0)) then (v_seq_95[v_int_227..v_int_228]) else (v_seq_95)) + (if ((|v_seq_96| > 0)) then (v_seq_96[v_int_126 := 13]) else (v_seq_96)));
	var v_map_59: map<char, bool> := map['u' := true];
	var v_char_85: char := 'p';
	var v_int_127: int := (if ((if ((v_char_85 in v_map_59)) then (v_map_59[v_char_85]) else (true))) then ((-22 - 26)) else (v_int_121));
	var v_map_60: map<char, int> := map['V' := 9, 'u' := 11, 'F' := 4, 'L' := 12, 'e' := 20];
	var v_char_86: char := 'e';
	var v_int_122: int := (if ((|v_seq_98| > 0)) then (v_seq_98[v_int_127]) else ((v_int_126 * (if ((v_char_86 in v_map_60)) then (v_map_60[v_char_86]) else (5)))));
	var v_map_62: map<char, real> := (match 'B' {
		case 'E' => map['n' := -23.36, 'w' := -5.05, 'a' := -28.94, 'C' := 10.41]
		case _ => map['l' := -0.56, 'X' := -12.03, 'c' := 27.67, 'N' := 2.53]
	});
	var v_map_61: map<char, char> := map['f' := 'k', 'r' := 'J', 'J' := 'B'];
	var v_char_87: char := 'M';
	var v_char_88: char := (if ((v_char_87 in v_map_61)) then (v_map_61[v_char_87]) else ('Q'));
	var v_seq_99: seq<real> := [29.12];
	var v_int_128: int := 3;
	var v_seq_165: seq<real> := v_seq_99;
	var v_int_233: int := v_int_128;
	var v_int_234: int := safe_index_seq(v_seq_165, v_int_233);
	v_int_128 := v_int_234;
	var v_int_123: int := ((if ((v_char_88 in v_map_62)) then (v_map_62[v_char_88]) else ((if ((|v_seq_99| > 0)) then (v_seq_99[v_int_128]) else (-0.76))))).Floor;
	while (v_int_122 < v_int_123) 
		decreases v_int_123 - v_int_122;
		invariant (v_int_122 <= v_int_123) && ((((v_int_122 == 0)) ==> ((((v_char_79 == 'I')) && ((v_char_78 == 'w')) && ((v_char_86 == 'e')) && ((v_char_84 == 'o'))))));
	{
		v_int_122 := (v_int_122 + 1);
		var v_int_real_real_31: (int, real, real) := (25, -29.01, -17.40);
		var v_int_real_real_32: (int, real, real) := (18, 23.59, -18.47);
		assert ((v_seq_98 == []) && (v_int_real_real_9 == v_int_real_real_31) && (v_int_real_real_9.0 == 25) && (v_int_real_real_6 == v_int_real_real_32));
		expect ((v_seq_98 == []) && (v_int_real_real_9 == v_int_real_real_31) && (v_int_real_real_9.0 == 25) && (v_int_real_real_6 == v_int_real_real_32));
		var v_map_65: map<char, bool> := map['M' := true]['l' := false][(match 'N' {
			case 'N' => 'B'
			case _ => 'b'
		}) := (if (false) then (false) else (false))];
		var v_seq_100: seq<char> := [];
		var v_seq_101: seq<char> := v_seq_100;
		var v_int_129: int := 25;
		var v_int_130: int := safe_index_seq(v_seq_101, v_int_129);
		var v_int_131: int := v_int_130;
		var v_seq_102: seq<char> := (if ((|v_seq_100| > 0)) then (v_seq_100[v_int_131 := 'l']) else (v_seq_100));
		var v_int_132: int := v_int_116;
		var v_seq_103: seq<char> := ['R', 'V'];
		var v_int_133: int := 18;
		var v_seq_166: seq<char> := v_seq_103;
		var v_int_235: int := v_int_133;
		var v_int_236: int := safe_index_seq(v_seq_166, v_int_235);
		v_int_133 := v_int_236;
		var v_char_91: char := (if ((|v_seq_102| > 0)) then (v_seq_102[v_int_132]) else ((if ((|v_seq_103| > 0)) then (v_seq_103[v_int_133]) else ('b'))));
		var v_map_63: map<char, bool> := map['G' := false, 'i' := true, 'L' := true, 'l' := false];
		var v_char_89: char := 'z';
		var v_map_64: map<char, bool> := map['J' := false, 'D' := false, 'R' := true, 'e' := true];
		var v_char_90: char := 'A';
		if (if ((v_char_91 in v_map_65)) then (v_map_65[v_char_91]) else ((if ((if ((v_char_89 in v_map_63)) then (v_map_63[v_char_89]) else (true))) then ((if ((v_char_90 in v_map_64)) then (v_map_64[v_char_90]) else (false))) else ((match 'X' {
			case _ => true
		}))))) {
			var v_int_134: int := v_int_real_real_3.0;
			var v_int_135: int := v_int_121;
			while (v_int_134 < v_int_135) 
				decreases v_int_135 - v_int_134;
				invariant (v_int_134 <= v_int_135);
			{
				v_int_134 := (v_int_134 + 1);
				var v_map_67: map<char, int> := map['Z' := 14]['f' := 11][(if (false) then ('a') else ('M')) := v_int_116];
				var v_map_66: map<char, char> := map['Y' := 'I', 'U' := 'g', 'u' := 'Z', 'P' := 'T']['z' := 'G'];
				var v_seq_104: seq<char> := ['i', 'f', 'B'];
				var v_int_137: int := 10;
				var v_char_92: char := (if ((|v_seq_104| > 0)) then (v_seq_104[v_int_137]) else ('k'));
				var v_seq_105: seq<char> := ['X', 'r'];
				var v_int_138: int := 10;
				var v_char_93: char := (if ((v_char_92 in v_map_66)) then (v_map_66[v_char_92]) else ((if ((|v_seq_105| > 0)) then (v_seq_105[v_int_138]) else ('k'))));
				var v_int_139: int, v_int_140: int := (if ((v_char_93 in v_map_67)) then (v_map_67[v_char_93]) else ((if ((if (true) then (false) else (true))) then (v_int_9) else ((if (true) then (18) else (17)))))), v_int_real_real_10.0;
				for v_int_136 := v_int_139 to v_int_140 
					invariant (v_int_140 - v_int_136 >= 0)
				{
					return ;
				}
				return ;
			}
			var v_seq_106: seq<char> := v_seq_84;
			var v_int_141: int := v_int_real_real_1.0;
			var v_map_68: map<char, char> := map['K' := 'q', 'o' := 'K', 'h' := 'o', 'Q' := 'G', 'X' := 'Z'];
			var v_char_94: char := 'Q';
			var v_map_69: map<char, char> := map['q' := 'r', 'm' := 'L', 'Q' := 'U', 'm' := 'O', 'C' := 'a'];
			var v_char_95: char := 'I';
			v_char_86 := (if ((|v_seq_106| > 0)) then (v_seq_106[v_int_141]) else ((match 'X' {
				case _ => (if ((v_char_95 in v_map_69)) then (v_map_69[v_char_95]) else ('i'))
			})));
			var v_seq_107: seq<char> := ['n', 'b'];
			var v_seq_108: seq<char> := v_seq_107;
			var v_int_142: int := -21;
			var v_int_143: int := safe_index_seq(v_seq_108, v_int_142);
			var v_int_144: int := v_int_143;
			var v_seq_109: seq<char> := (if ((|v_seq_107| > 0)) then (v_seq_107[v_int_144 := 'p']) else (v_seq_107));
			var v_seq_110: seq<char> := v_seq_109;
			var v_int_145: int := v_int_9;
			var v_int_146: int := safe_index_seq(v_seq_110, v_int_145);
			var v_int_147: int := v_int_146;
			var v_map_70: map<char, char> := map['f' := 'D', 'y' := 'w', 'd' := 'T', 'r' := 't'];
			var v_char_96: char := 'z';
			var v_seq_111: seq<char> := (if ((|v_seq_109| > 0)) then (v_seq_109[v_int_147 := (if ((v_char_96 in v_map_70)) then (v_map_70[v_char_96]) else ('q'))]) else (v_seq_109));
			var v_int_148: int := (match 'v' {
				case _ => (match 't' {
					case _ => 16
				})
			});
			var v_seq_112: seq<char> := ['l', 'u', 'M', 'A'];
			var v_seq_113: seq<char> := v_seq_112;
			var v_int_149: int := 21;
			var v_int_150: int := safe_index_seq(v_seq_113, v_int_149);
			var v_int_151: int := v_int_150;
			var v_seq_114: seq<char> := (if ((|v_seq_112| > 0)) then (v_seq_112[v_int_151 := 'b']) else (v_seq_112));
			var v_array_29: array<char> := new char[4] ['X', 'f', 'v', 'd'];
			var v_int_152: int := v_array_29.Length;
			match (if ((|v_seq_111| > 0)) then (v_seq_111[v_int_148]) else ((if ((|v_seq_114| > 0)) then (v_seq_114[v_int_152]) else (v_char_89)))) {
				case _ => {
					var v_seq_115: seq<char> := ['z'];
					var v_int_153: int := 8;
					var v_seq_116: seq<multiset<char>> := [multiset{'W', 'i', 'v'}, multiset{'y', 'a', 'U'}, multiset{'M', 'Z'}];
					var v_int_154: int := 25;
					var v_seq_117: seq<char> := [];
					var v_seq_118: seq<char> := (if ((|v_seq_117| > 0)) then (v_seq_117[8..0]) else (v_seq_117));
					var v_int_155: int := (match 'T' {
						case _ => 12
					});
					var v_map_74: map<char, char> := map['W' := 'b', 'm' := 'h', 'h' := 'r']['U' := 'l'][(if (true) then ('y') else ('b')) := v_char_91];
					var v_map_71: map<char, bool> := map['X' := false, 'A' := true, 'S' := false, 'z' := false];
					var v_char_97: char := 'R';
					var v_char_100: char := (if ((if ((v_char_97 in v_map_71)) then (v_map_71[v_char_97]) else (true))) then ((match 'o' {
						case _ => 'c'
					})) else ((if (false) then ('r') else ('r'))));
					var v_map_73: map<char, char> := map['O' := 'n', 'g' := 'h', 'b' := 'j', 'G' := 'n', 'Q' := 'h']['S' := 'e'];
					var v_char_99: char := (match 'C' {
						case _ => 'd'
					});
					var v_map_72: map<char, char> := map['I' := 'r', 'q' := 'r', 'F' := 'X', 'b' := 'W', 'p' := 'T'];
					var v_char_98: char := 'Z';
					var v_seq_119: seq<char> := ['h', 'S'];
					var v_seq_120: seq<char> := v_seq_119;
					var v_int_156: int := 7;
					var v_int_157: int := safe_index_seq(v_seq_120, v_int_156);
					var v_int_158: int := v_int_157;
					var v_seq_122: seq<char> := (if ((|v_seq_119| > 0)) then (v_seq_119[v_int_158 := 'k']) else (v_seq_119));
					var v_seq_121: seq<int> := [7, 22];
					var v_int_159: int := -24;
					var v_seq_123: seq<char> := (if ((|v_seq_122| > 0)) then (v_seq_122[(if ((|v_seq_121| > 0)) then (v_seq_121[v_int_159]) else (10))..(5.53).Floor]) else (v_seq_122));
					var v_int_160: int := (match 'o' {
						case _ => (if (true) then (7) else (25))
					});
					var v_seq_124: seq<char> := ['J', 'F'];
					var v_seq_125: seq<char> := v_seq_124;
					var v_int_161: int := 19;
					var v_int_162: int := safe_index_seq(v_seq_125, v_int_161);
					var v_int_163: int := v_int_162;
					var v_seq_126: seq<char> := (if ((|v_seq_124| > 0)) then (v_seq_124[v_int_163 := 'm']) else (v_seq_124));
					var v_int_164: int := (16 / 11);
					v_char_89, v_char_78, v_char_86, v_char_79 := (if (((if ((|v_seq_115| > 0)) then (v_seq_115[v_int_153]) else ('N')) !in (if ((|v_seq_116| > 0)) then (v_seq_116[v_int_154]) else (multiset{'o', 'G', 'S', 'f'})))) then ((if ((|v_seq_118| > 0)) then (v_seq_118[v_int_155]) else ((if (false) then ('b') else ('B'))))) else (v_array_29[3])), v_char_91, (if ((v_char_100 in v_map_74)) then (v_map_74[v_char_100]) else ((if ((v_char_99 in v_map_73)) then (v_map_73[v_char_99]) else ((if ((v_char_98 in v_map_72)) then (v_map_72[v_char_98]) else ('I')))))), (if ((|v_seq_123| > 0)) then (v_seq_123[v_int_160]) else ((if ((|v_seq_126| > 0)) then (v_seq_126[v_int_164]) else ((match 'E' {
						case _ => 'Y'
					})))));
					var v_map_75: map<char, int> := v_map_60;
					var v_char_101: char := (if (true) then ('j') else ('S'));
					var v_seq_127: seq<bool> := [false, true, false];
					var v_int_166: int := -21;
					var v_map_76: map<char, int> := map['q' := 9, 'w' := 11, 'I' := 19, 'L' := 16, 'f' := 1];
					var v_char_102: char := 'R';
					var v_array_30: array<char> := new char[5] ['J', 'q', 'w', 'Q', 'h'];
					var v_array_31: array<char> := new char[5] ['V', 'W', 'Z', 'V', 'u'];
					var v_array_32: array<char> := new char[4];
					v_array_32[0] := 'H';
					v_array_32[1] := 'P';
					v_array_32[2] := 'c';
					v_array_32[3] := 'f';
					var v_seq_128: seq<array<char>> := [v_array_30, v_array_31, v_array_32];
					var v_int_167: int := 28;
					var v_array_33: array<char> := new char[3];
					v_array_33[0] := 'V';
					v_array_33[1] := 'Z';
					v_array_33[2] := 'x';
					var v_int_168: int, v_int_169: int := (v_int_146 / (if ((v_char_101 in v_map_75)) then (v_map_75[v_char_101]) else (v_int_117))), (match 'e' {
						case _ => (if ((|v_seq_128| > 0)) then (v_seq_128[v_int_167]) else (v_array_33)).Length
					});
					for v_int_165 := v_int_168 to v_int_169 
						invariant (v_int_169 - v_int_165 >= 0)
					{
						return ;
					}
				}
				
			}
			
			continue;
		} else {
			var v_seq_129: seq<map<char, bool>> := [map['T' := false, 'H' := true, 'N' := true, 'G' := false, 'Q' := false]];
			var v_int_170: int := 24;
			var v_seq_167: seq<map<char, bool>> := v_seq_129;
			var v_int_237: int := v_int_170;
			var v_int_238: int := safe_index_seq(v_seq_167, v_int_237);
			v_int_170 := v_int_238;
			var v_map_77: map<char, bool> := (if ((|v_seq_129| > 0)) then (v_seq_129[v_int_170]) else (map['f' := true]));
			var v_char_103: char := (if (true) then ('M') else ('p'));
			var v_seq_130: seq<char> := ['J', 'N', 'f'];
			var v_seq_131: seq<char> := v_seq_130;
			var v_int_171: int := 14;
			var v_int_172: int := safe_index_seq(v_seq_131, v_int_171);
			var v_int_173: int := v_int_172;
			var v_seq_132: seq<char> := (if ((|v_seq_130| > 0)) then (v_seq_130[v_int_173 := 'J']) else (v_seq_130));
			var v_int_174: int := (4 * 10);
			var v_map_78: map<char, char> := map['t' := 'W', 'p' := 'T', 'B' := 'T', 'T' := 'b'];
			var v_char_104: char := 'v';
			var v_seq_133: seq<char> := ['F'];
			var v_seq_168: seq<char> := v_seq_133;
			var v_int_241: int := 3;
			var v_int_242: int := 0;
			var v_int_243: int, v_int_244: int := safe_subsequence(v_seq_168, v_int_241, v_int_242);
			var v_int_239: int, v_int_240: int := v_int_243, v_int_244;
			var v_seq_134: seq<char> := (if ((|v_seq_133| > 0)) then (v_seq_133[v_int_239..v_int_240]) else (v_seq_133));
			var v_int_175: int := (if (true) then (0) else (16));
			var v_map_79: map<char, char> := map['u' := 'n', 'L' := 'v', 'k' := 'M', 'G' := 'x'];
			var v_char_105: char := 'q';
			v_char_103, v_char_86 := v_char_86, (if ((if ((v_char_103 in v_map_77)) then (v_map_77[v_char_103]) else ((match 'n' {
				case 'T' => true
				case _ => false
			})))) then ((if ((|v_seq_132| > 0)) then (v_seq_132[v_int_174]) else ((if ((v_char_104 in v_map_78)) then (v_map_78[v_char_104]) else ('f'))))) else ((if ((|v_seq_134| > 0)) then (v_seq_134[v_int_175]) else ((if ((v_char_105 in v_map_79)) then (v_map_79[v_char_105]) else ('S'))))));
			var v_seq_135: seq<char> := [];
			var v_int_176: int := 0;
			var v_seq_136: seq<char> := [];
			var v_int_177: int := 0;
			var v_seq_137: seq<char> := ['W', 'D'];
			var v_int_178: int := 21;
			var v_map_80: map<char, char> := map['d' := 'D', 'y' := 'V', 'o' := 'o', 's' := 't', 'M' := 'c'];
			var v_char_106: char := 'i';
			var v_map_81: map<char, char> := map['n' := 'Q'];
			var v_char_107: char := 'p';
			var v_map_83: map<char, char> := (match 'v' {
				case 'h' => map['U' := 'y', 'c' := 'O', 'i' := 'Y', 'a' := 'C']['G' := 'E']
				case _ => map['Z' := 'L', 'D' := 'u', 'h' := 'z', 'j' := 'i', 'g' := 'v']['U' := 'P']
			});
			var v_seq_138: seq<char> := ['t', 'I', 'Q'];
			var v_seq_139: seq<char> := v_seq_138;
			var v_int_179: int := 8;
			var v_int_180: int := safe_index_seq(v_seq_139, v_int_179);
			var v_int_181: int := v_int_180;
			var v_seq_140: seq<char> := (if ((|v_seq_138| > 0)) then (v_seq_138[v_int_181 := 't']) else (v_seq_138));
			var v_int_182: int := (if (false) then (25) else (-6));
			var v_seq_169: seq<char> := v_seq_140;
			var v_int_245: int := v_int_182;
			var v_int_246: int := safe_index_seq(v_seq_169, v_int_245);
			v_int_182 := v_int_246;
			var v_char_109: char := (if ((|v_seq_140| > 0)) then (v_seq_140[v_int_182]) else (v_char_79));
			var v_map_82: map<char, char> := map['A' := 'T', 'x' := 'g', 'H' := 'w', 'R' := 'B', 'f' := 'Y']['c' := 'o'];
			var v_char_108: char := (if (false) then ('K') else ('t'));
			var v_seq_141: seq<char> := ['b', 'F', 'f', 'V'];
			var v_int_183: int := 7;
			var v_seq_170: seq<char> := v_seq_141;
			var v_int_247: int := v_int_183;
			var v_int_248: int := safe_index_seq(v_seq_170, v_int_247);
			v_int_183 := v_int_248;
			var v_map_84: map<char, char> := map['p' := 'v'];
			var v_char_110: char := 'W';
			var v_map_86: map<char, char> := (if (true) then (map['t' := 'a']) else (map['O' := 'b']))[(if ((|v_seq_141| > 0)) then (v_seq_141[v_int_183]) else ('j')) := (if ((v_char_110 in v_map_84)) then (v_map_84[v_char_110]) else ('l'))];
			var v_map_85: map<char, char> := map['V' := 'x', 'D' := 'O'];
			var v_char_111: char := 'n';
			var v_char_112: char := (if ((multiset{'Q', 'p', 'Y', 'x'} !! multiset{'U', 'A', 'd'})) then ((if ((v_char_111 in v_map_85)) then (v_map_85[v_char_111]) else ('U'))) else ((match 'n' {
				case _ => 'Z'
			})));
			var v_seq_142: seq<char> := [];
			var v_seq_143: seq<char> := (if ((|v_seq_142| > 0)) then (v_seq_142[0..5]) else (v_seq_142));
			var v_int_184: int := (if (false) then (8) else (12));
			v_char_109, v_char_79, v_char_104 := (match 'a' {
				case 'E' => (match 'B' {
					case _ => (if ((|v_seq_137| > 0)) then (v_seq_137[v_int_178]) else ('b'))
				})
				case 'W' => (match 'R' {
					case _ => (if (true) then ('a') else ('O'))
				})
				case _ => (if ((if (false) then (false) else (true))) then ((if ((v_char_106 in v_map_80)) then (v_map_80[v_char_106]) else ('H'))) else ((if ((v_char_107 in v_map_81)) then (v_map_81[v_char_107]) else ('d'))))
			}), (if ((v_char_109 in v_map_83)) then (v_map_83[v_char_109]) else ((if ((v_char_108 in v_map_82)) then (v_map_82[v_char_108]) else ((match 'a' {
				case 'M' => 'r'
				case 'N' => 'F'
				case _ => 'k'
			}))))), (if ((v_char_112 in v_map_86)) then (v_map_86[v_char_112]) else ((if ((|v_seq_143| > 0)) then (v_seq_143[v_int_184]) else (v_char_90))));
			var v_seq_144: seq<int> := [];
			var v_seq_145: seq<int> := (if ((|v_seq_144| > 0)) then (v_seq_144[19..22]) else (v_seq_144));
			var v_int_186: int := v_int_125;
			var v_map_87: map<char, int> := map['N' := -7, 'J' := 4, 'k' := 12];
			var v_char_113: char := 'r';
			var v_seq_146: seq<int> := [29, 23, 22];
			var v_seq_147: seq<int> := v_seq_146;
			var v_int_187: int := -9;
			var v_int_188: int := safe_index_seq(v_seq_147, v_int_187);
			var v_int_189: int := v_int_188;
			var v_seq_148: seq<int> := (if ((|v_seq_146| > 0)) then (v_seq_146[v_int_189 := 22]) else (v_seq_146));
			var v_int_190: int := (match 'B' {
				case 'z' => 4
				case 'i' => 0
				case _ => 11
			});
			var v_seq_171: seq<int> := v_seq_148;
			var v_int_249: int := v_int_190;
			var v_int_250: int := safe_index_seq(v_seq_171, v_int_249);
			v_int_190 := v_int_250;
			var v_seq_149: seq<int> := [2, 27];
			var v_int_191: int := 6;
			var v_seq_150: seq<int> := [24, 5];
			var v_int_192: int := 15;
			var v_int_193: int, v_int_194: int := ((if ((|v_seq_145| > 0)) then (v_seq_145[v_int_186]) else ((match 's' {
				case 'S' => 5
				case 'K' => 21
				case _ => 16
			}))) / (match 'd' {
				case 't' => (if (true) then (25) else (16))
				case 'w' => (5 + 24)
				case _ => (if ((v_char_113 in v_map_87)) then (v_map_87[v_char_113]) else (28))
			})), (if ((match 'M' {
				case 'j' => (false ==> true)
				case _ => (if (true) then (true) else (true))
			})) then ((if ((|v_seq_148| > 0)) then (v_seq_148[v_int_190]) else ((if ((|v_seq_149| > 0)) then (v_seq_149[v_int_191]) else (15))))) else ((match 'z' {
				case _ => (if (false) then (8) else (15))
			})));
			for v_int_185 := v_int_193 to v_int_194 
				invariant (v_int_194 - v_int_185 >= 0)
			{
				var v_int_real_real_33: (int, real, real) := (19, 23.76, 17.29);
				var v_int_real_real_34: (int, real, real) := (29, -16.28, -27.43);
				var v_int_real_real_35: (int, real, real) := (18, 23.59, -18.47);
				var v_int_real_real_36: (int, real, real) := (27, -10.11, -14.40);
				var v_int_real_real_37: (int, real, real) := (24, -23.26, 15.63);
				var v_int_real_real_38: (int, real, real) := (10, -5.13, -28.00);
				var v_int_real_real_39: (int, real, real) := (20, 23.32, -14.86);
				var v_int_real_real_40: (int, real, real) := (10, 7.37, -27.15);
				var v_int_real_real_41: (int, real, real) := (23, -3.34, -24.46);
				var v_int_real_real_42: (int, real, real) := (23, -3.34, -24.46);
				var v_int_real_real_43: (int, real, real) := (25, -29.01, -17.40);
				var v_int_real_real_44: (int, real, real) := (18, 23.59, -18.47);
				var v_int_real_real_45: (int, real, real) := (19, 23.76, 17.29);
				var v_int_real_real_46: (int, real, real) := (29, -16.28, -27.43);
				var v_int_real_real_47: (int, real, real) := (10, 7.37, -27.15);
				var v_int_real_real_48: (int, real, real) := (25, -29.01, -17.40);
				var v_int_real_real_49: (int, real, real) := (24, -23.26, 15.63);
				var v_int_real_real_50: (int, real, real) := (27, -10.11, -14.40);
				var v_int_real_real_51: (int, real, real) := (10, -5.13, -28.00);
				var v_int_real_real_52: (int, real, real) := (20, 23.32, -14.86);
				print "v_int_185", " ", v_int_185, " ", "v_seq_141", " ", (v_seq_141 == ['b', 'F', 'f', 'V']), " ", "v_seq_140", " ", (v_seq_140 == ['t', 'I', 'Q']), " ", "v_seq_143", " ", (v_seq_143 == []), " ", "v_seq_142", " ", (v_seq_142 == []), " ", "v_char_110", " ", (v_char_110 == 'W'), " ", "v_char_111", " ", (v_char_111 == 'n'), " ", "v_char_79", " ", (v_char_79 == 'k'), " ", "v_char_112", " ", (v_char_112 == 'U'), " ", "v_seq_149", " ", v_seq_149, " ", "v_seq_148", " ", v_seq_148, " ", "v_seq_145", " ", v_seq_145, " ", "v_seq_144", " ", v_seq_144, " ", "v_seq_147", " ", v_seq_147, " ", "v_seq_146", " ", v_seq_146, " ", "v_int_188", " ", v_int_188, " ", "v_int_189", " ", v_int_189, " ", "v_int_184", " ", v_int_184, " ", "v_char_86", " ", (v_char_86 == 'S'), " ", "v_int_186", " ", v_int_186, " ", "v_int_187", " ", v_int_187, " ", "v_int_180", " ", v_int_180, " ", "v_int_181", " ", v_int_181, " ", "v_int_182", " ", v_int_182, " ", "v_int_183", " ", v_int_183, " ", "v_int_190", " ", v_int_190, " ", "v_int_191", " ", v_int_191, " ", "v_map_79", " ", (v_map_79 == map['u' := 'n', 'G' := 'x', 'k' := 'M', 'L' := 'v']), " ", "v_seq_129", " ", (v_seq_129 == [map['Q' := false, 'T' := false, 'G' := false, 'H' := true, 'N' := true]]), " ", "v_map_77", " ", (v_map_77 == map['Q' := false, 'T' := false, 'G' := false, 'H' := true, 'N' := true]), " ", "v_map_78", " ", (v_map_78 == map['p' := 'T', 'B' := 'T', 't' := 'W', 'T' := 'b']), " ", "v_char_103", " ", (v_char_103 == 'e'), " ", "v_seq_130", " ", (v_seq_130 == ['J', 'N', 'f']), " ", "v_map_82", " ", (v_map_82 == map['A' := 'T', 'R' := 'B', 'c' := 'o', 'f' := 'Y', 'x' := 'g', 'H' := 'w']), " ", "v_char_104", " ", (v_char_104 == 'A'), " ", "v_map_83", " ", (v_map_83 == map['D' := 'u', 'U' := 'P', 'g' := 'v', 'h' := 'z', 'Z' := 'L', 'j' := 'i']), " ", "v_seq_132", " ", (v_seq_132 == ['J', 'N', 'f']), " ", "v_char_105", " ", (v_char_105 == 'q'), " ", "v_seq_131", " ", (v_seq_131 == ['J', 'N', 'f']), " ", "v_seq_138", " ", (v_seq_138 == ['t', 'I', 'Q']), " ", "v_seq_139", " ", (v_seq_139 == ['t', 'I', 'Q']), " ", "v_seq_134", " ", (v_seq_134 == []), " ", "v_map_86", " ", (v_map_86 == map['b' := 'l', 't' := 'a']), " ", "v_seq_133", " ", (v_seq_133 == ['F']), " ", "v_char_108", " ", (v_char_108 == 't'), " ", "v_char_109", " ", (v_char_109 == 'H'), " ", "v_map_84", " ", (v_map_84 == map['p' := 'v']), " ", "v_map_85", " ", (v_map_85 == map['D' := 'O', 'V' := 'x']), " ", "v_int_179", " ", v_int_179, " ", "v_int_173", " ", v_int_173, " ", "v_int_174", " ", v_int_174, " ", "v_int_175", " ", v_int_175, " ", "v_int_170", " ", v_int_170, " ", "v_int_171", " ", v_int_171, " ", "v_int_172", " ", v_int_172, " ", "v_char_89", " ", (v_char_89 == 'z'), " ", "v_seq_101", " ", (v_seq_101 == []), " ", "v_map_64", " ", (v_map_64 == map['R' := true, 'D' := false, 'e' := true, 'J' := false]), " ", "v_seq_100", " ", (v_seq_100 == []), " ", "v_map_65", " ", (v_map_65 == map['B' := false, 'l' := false, 'M' := true]), " ", "v_seq_103", " ", (v_seq_103 == ['R', 'V']), " ", "v_seq_102", " ", (v_seq_102 == []), " ", "v_map_63", " ", (v_map_63 == map['G' := false, 'i' := true, 'L' := true, 'l' := false]), " ", "v_char_90", " ", (v_char_90 == 'A'), " ", "v_int_129", " ", v_int_129, " ", "v_int_133", " ", v_int_133, " ", "v_int_130", " ", v_int_130, " ", "v_int_131", " ", v_int_131, " ", "v_int_132", " ", v_int_132, " ", "v_char_91", " ", (v_char_91 == 'R'), " ", "v_int_real_real_8", " ", (v_int_real_real_8 == v_int_real_real_33), " ", "v_int_real_real_6.0", " ", v_int_real_real_6.0, " ", "v_int_real_real_7", " ", (v_int_real_real_7 == v_int_real_real_34), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 23.32), " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_35), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == -14.86), " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_36), " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_37), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_38), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_39), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_40), " ", "v_int_104", " ", v_int_104, " ", "v_int_103", " ", v_int_103, " ", "v_int_115", " ", v_int_115, " ", "v_int_116", " ", v_int_116, " ", "v_int_117", " ", v_int_117, " ", "v_int_118", " ", v_int_118, " ", "v_int_real_real_7.2", " ", (v_int_real_real_7.2 == -27.43), " ", "v_int_111", " ", v_int_111, " ", "v_int_112", " ", v_int_112, " ", "v_int_real_real_7.0", " ", v_int_real_real_7.0, " ", "v_int_113", " ", v_int_113, " ", "v_int_real_real_7.1", " ", (v_int_real_real_7.1 == -16.28), " ", "v_int_114", " ", v_int_114, " ", "v_int_real_real_10", " ", (v_int_real_real_10 == v_int_real_real_41), " ", "v_int_110", " ", v_int_110, " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == -28.00), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == -5.13), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_1[4]", " ", (v_array_1[4] == map[v_int_real_real_42 := multiset{false, true}, v_int_real_real_43 := multiset{true}]), " ", "v_int_real_real_8.1", " ", (v_int_real_real_8.1 == 23.76), " ", "v_int_real_real_8.2", " ", (v_int_real_real_8.2 == 17.29), " ", "v_int_real_real_8.0", " ", v_int_real_real_8.0, " ", "v_char_79", " ", (v_char_79 == 'k'), " ", "v_char_78", " ", (v_char_78 == 'w'), " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -23.26), " ", "v_map_57", " ", (v_map_57 == map['s' := 3, 'u' := 3, 'e' := 26, 'E' := 22]), " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == 15.63), " ", "v_map_58", " ", (v_map_58 == map['p' := 'j', 'W' := 'I']), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_map_56", " ", (v_map_56 == map['d' := 0, 'F' := 21, 'i' := 27]), " ", "v_map_53", " ", (v_map_53 == map['D' := true, 'u' := true, 'j' := true, 'n' := false, 'o' := true]), " ", "v_map_54", " ", (v_map_54 == map['B' := 'F', 'd' := 'H', 'D' := 'y']), " ", "v_map_52", " ", (v_map_52 == map['q' := 'G', 'H' := 'R', 'Z' := 't', 'M' := 'I']), " ", "v_map_59", " ", (v_map_59 == map['u' := true]), " ", "v_char_87", " ", (v_char_87 == 'M'), " ", "v_array_1[2]", " ", (v_array_1[2] == map[v_int_real_real_44 := multiset{}]), " ", "v_char_86", " ", (v_char_86 == 'S'), " ", "v_char_85", " ", (v_char_85 == 'p'), " ", "v_char_84", " ", (v_char_84 == 'o'), " ", "v_char_83", " ", (v_char_83 == 'o'), " ", "v_char_82", " ", (v_char_82 == 'f'), " ", "v_char_80", " ", (v_char_80 == 'o'), " ", "v_map_60", " ", (v_map_60 == map['u' := 11, 'e' := 20, 'V' := 9, 'F' := 4, 'L' := 12]), " ", "v_map_61", " ", (v_map_61 == map['r' := 'J', 'f' := 'k', 'J' := 'B']), " ", "v_int_real_real_10.2", " ", (v_int_real_real_10.2 == -24.46), " ", "v_int_real_real_10.0", " ", v_int_real_real_10.0, " ", "v_int_real_real_10.1", " ", (v_int_real_real_10.1 == -3.34), " ", "v_map_62", " ", (v_map_62 == map['c' := 27.67, 'X' := -12.03, 'l' := -0.56, 'N' := 2.53]), " ", "v_int_real_real_9.2", " ", (v_int_real_real_9.2 == -17.40), " ", "v_int_real_real_9.0", " ", v_int_real_real_9.0, " ", "v_int_real_real_9.1", " ", (v_int_real_real_9.1 == -29.01), " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == -14.40), " ", "v_array_1[3]", " ", (v_array_1[3] == map[v_int_real_real_45 := multiset{}, v_int_real_real_46 := multiset{false, false, true, true}]), " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == -10.11), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == -27.15), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == 7.37), " ", "v_int_126", " ", v_int_126, " ", "v_int_127", " ", v_int_127, " ", "v_int_128", " ", v_int_128, " ", "v_seq_98", " ", v_seq_98, " ", "v_int_122", " ", v_int_122, " ", "v_seq_99", " ", (v_seq_99 == [29.12]), " ", "v_int_123", " ", v_int_123, " ", "v_int_124", " ", v_int_124, " ", "v_int_9", " ", v_int_9, " ", "v_int_125", " ", v_int_125, " ", "v_seq_94", " ", (v_seq_94 == ['W', 'R', 'M']), " ", "v_seq_95", " ", v_seq_95, " ", "v_seq_96", " ", v_seq_96, " ", "v_array_1[0]", " ", (v_array_1[0] == map[v_int_real_real_47 := multiset{}]), " ", "v_int_121", " ", v_int_121, " ", "v_seq_97", " ", v_seq_97, " ", "v_seq_90", " ", v_seq_90, " ", "v_seq_91", " ", (v_seq_91 == ['o', 'M', 'd', 'S']), " ", "v_char_88", " ", (v_char_88 == 'Q'), " ", "v_int_8", " ", v_int_8, " ", "v_int_10", " ", v_int_10, " ", "v_seq_87", " ", (v_seq_87 == ['s', 'M', 'd', 'S']), " ", "v_seq_88", " ", (v_seq_88 == ['s', 'M', 'd', 'S']), " ", "v_int_real_real_6.1", " ", (v_int_real_real_6.1 == 23.59), " ", "v_seq_89", " ", v_seq_89, " ", "v_int_real_real_6.2", " ", (v_int_real_real_6.2 == -18.47), " ", "v_int_real_real_9", " ", (v_int_real_real_9 == v_int_real_real_48), " ", "v_array_1[1]", " ", (v_array_1[1] == map[v_int_real_real_49 := multiset{}, v_int_real_real_50 := multiset{false, true}, v_int_real_real_51 := multiset{}, v_int_real_real_52 := multiset{}]), " ", "v_seq_84", " ", (v_seq_84 == ['s', 'M', 'x', 'S']), " ", "v_seq_85", " ", (v_seq_85 == ['s', 'M', 'x', 'S']), " ", "v_seq_86", " ", v_seq_86, "\n";
				continue;
			}
			var v_map_88: map<char, char> := map['U' := 'm'];
			var v_char_114: char := 'a';
			var v_map_89: map<char, char> := map['W' := 'g', 't' := 'L'];
			var v_char_115: char := 'Y';
			var v_seq_151: seq<char> := ['f'];
			var v_seq_172: seq<char> := v_seq_151;
			var v_int_253: int := 16;
			var v_int_254: int := -11;
			var v_int_255: int, v_int_256: int := safe_subsequence(v_seq_172, v_int_253, v_int_254);
			var v_int_251: int, v_int_252: int := v_int_255, v_int_256;
			var v_seq_152: seq<char> := (if ((|v_seq_151| > 0)) then (v_seq_151[v_int_251..v_int_252]) else (v_seq_151));
			var v_int_195: int := |map['C' := 'z', 'w' := 'Z']|;
			v_char_84 := (match 'I' {
				case 'D' => (if ((match 'x' {
					case _ => true
				})) then ((if ((v_char_114 in v_map_88)) then (v_map_88[v_char_114]) else ('v'))) else ((if ((v_char_115 in v_map_89)) then (v_map_89[v_char_115]) else ('V'))))
				case 'C' => v_char_85
				case _ => (if ((|v_seq_152| > 0)) then (v_seq_152[v_int_195]) else ((if (true) then ('V') else ('I'))))
			});
			var v_int_196: int := v_int_128;
			var v_seq_153: seq<char> := [];
			var v_int_198: int := 6;
			var v_map_91: map<char, int> := map['M' := 22, 'r' := 21, 'x' := -21, 'w' := 5, 'm' := 14]['k' := -20][(if ((|v_seq_153| > 0)) then (v_seq_153[v_int_198]) else ('o')) := v_int_128];
			var v_char_117: char := v_char_103;
			var v_map_90: map<char, int> := map['c' := -24]['N' := 9];
			var v_char_116: char := (if (true) then ('U') else ('Z'));
			var v_int_197: int := (if ((v_char_117 in v_map_91)) then (v_map_91[v_char_117]) else ((if ((v_char_116 in v_map_90)) then (v_map_90[v_char_116]) else ((-29.85).Floor))));
			while (v_int_196 < v_int_197) 
				decreases v_int_197 - v_int_196;
				invariant (v_int_196 <= v_int_197);
			{
				v_int_196 := (v_int_196 + 1);
			}
			var v_int_real_real_53: (int, real, real) := (19, 23.76, 17.29);
			var v_int_real_real_54: (int, real, real) := (29, -16.28, -27.43);
			var v_int_real_real_55: (int, real, real) := (18, 23.59, -18.47);
			var v_int_real_real_56: (int, real, real) := (27, -10.11, -14.40);
			var v_int_real_real_57: (int, real, real) := (24, -23.26, 15.63);
			var v_int_real_real_58: (int, real, real) := (10, -5.13, -28.00);
			var v_int_real_real_59: (int, real, real) := (20, 23.32, -14.86);
			var v_int_real_real_60: (int, real, real) := (10, 7.37, -27.15);
			var v_int_real_real_61: (int, real, real) := (23, -3.34, -24.46);
			var v_int_real_real_62: (int, real, real) := (23, -3.34, -24.46);
			var v_int_real_real_63: (int, real, real) := (25, -29.01, -17.40);
			var v_int_real_real_64: (int, real, real) := (18, 23.59, -18.47);
			var v_int_real_real_65: (int, real, real) := (19, 23.76, 17.29);
			var v_int_real_real_66: (int, real, real) := (29, -16.28, -27.43);
			var v_int_real_real_67: (int, real, real) := (10, 7.37, -27.15);
			var v_int_real_real_68: (int, real, real) := (25, -29.01, -17.40);
			var v_int_real_real_69: (int, real, real) := (24, -23.26, 15.63);
			var v_int_real_real_70: (int, real, real) := (27, -10.11, -14.40);
			var v_int_real_real_71: (int, real, real) := (10, -5.13, -28.00);
			var v_int_real_real_72: (int, real, real) := (20, 23.32, -14.86);
			print "v_seq_141", " ", (v_seq_141 == ['b', 'F', 'f', 'V']), " ", "v_seq_140", " ", (v_seq_140 == ['t', 'I', 'Q']), " ", "v_seq_143", " ", (v_seq_143 == []), " ", "v_char_116", " ", (v_char_116 == 'U'), " ", "v_map_91", " ", (v_map_91 == map['r' := 21, 'w' := 5, 'x' := -21, 'k' := -20, 'M' := 22, 'm' := 14, 'o' := 0]), " ", "v_seq_142", " ", (v_seq_142 == []), " ", "v_char_117", " ", (v_char_117 == 'e'), " ", "v_char_110", " ", (v_char_110 == 'W'), " ", "v_char_111", " ", (v_char_111 == 'n'), " ", "v_char_79", " ", (v_char_79 == 'k'), " ", "v_map_90", " ", (v_map_90 == map['c' := -24, 'N' := 9]), " ", "v_char_112", " ", (v_char_112 == 'U'), " ", "v_seq_149", " ", v_seq_149, " ", "v_seq_148", " ", v_seq_148, " ", "v_seq_145", " ", v_seq_145, " ", "v_seq_144", " ", v_seq_144, " ", "v_seq_147", " ", v_seq_147, " ", "v_seq_146", " ", v_seq_146, " ", "v_int_188", " ", v_int_188, " ", "v_int_189", " ", v_int_189, " ", "v_int_184", " ", v_int_184, " ", "v_char_86", " ", (v_char_86 == 'S'), " ", "v_int_186", " ", v_int_186, " ", "v_int_187", " ", v_int_187, " ", "v_char_84", " ", (v_char_84 == 'V'), " ", "v_int_180", " ", v_int_180, " ", "v_int_181", " ", v_int_181, " ", "v_int_182", " ", v_int_182, " ", "v_int_183", " ", v_int_183, " ", "v_int_190", " ", v_int_190, " ", "v_seq_153", " ", (v_seq_153 == []), " ", "v_int_196", " ", v_int_196, " ", "v_int_197", " ", v_int_197, " ", "v_int_198", " ", v_int_198, " ", "v_int_191", " ", v_int_191, " ", "v_int_193", " ", v_int_193, " ", "v_int_194", " ", v_int_194, " ", "v_map_79", " ", (v_map_79 == map['u' := 'n', 'G' := 'x', 'k' := 'M', 'L' := 'v']), " ", "v_seq_129", " ", (v_seq_129 == [map['Q' := false, 'T' := false, 'G' := false, 'H' := true, 'N' := true]]), " ", "v_map_77", " ", (v_map_77 == map['Q' := false, 'T' := false, 'G' := false, 'H' := true, 'N' := true]), " ", "v_map_78", " ", (v_map_78 == map['p' := 'T', 'B' := 'T', 't' := 'W', 'T' := 'b']), " ", "v_char_103", " ", (v_char_103 == 'e'), " ", "v_seq_130", " ", (v_seq_130 == ['J', 'N', 'f']), " ", "v_map_82", " ", (v_map_82 == map['A' := 'T', 'R' := 'B', 'c' := 'o', 'f' := 'Y', 'x' := 'g', 'H' := 'w']), " ", "v_char_104", " ", (v_char_104 == 'A'), " ", "v_map_83", " ", (v_map_83 == map['D' := 'u', 'U' := 'P', 'g' := 'v', 'h' := 'z', 'Z' := 'L', 'j' := 'i']), " ", "v_seq_132", " ", (v_seq_132 == ['J', 'N', 'f']), " ", "v_char_105", " ", (v_char_105 == 'q'), " ", "v_seq_131", " ", (v_seq_131 == ['J', 'N', 'f']), " ", "v_seq_138", " ", (v_seq_138 == ['t', 'I', 'Q']), " ", "v_seq_139", " ", (v_seq_139 == ['t', 'I', 'Q']), " ", "v_seq_134", " ", (v_seq_134 == []), " ", "v_map_86", " ", (v_map_86 == map['b' := 'l', 't' := 'a']), " ", "v_seq_133", " ", (v_seq_133 == ['F']), " ", "v_char_108", " ", (v_char_108 == 't'), " ", "v_char_109", " ", (v_char_109 == 'H'), " ", "v_map_84", " ", (v_map_84 == map['p' := 'v']), " ", "v_map_85", " ", (v_map_85 == map['D' := 'O', 'V' := 'x']), " ", "v_int_179", " ", v_int_179, " ", "v_int_173", " ", v_int_173, " ", "v_int_174", " ", v_int_174, " ", "v_int_175", " ", v_int_175, " ", "v_int_170", " ", v_int_170, " ", "v_int_171", " ", v_int_171, " ", "v_int_172", " ", v_int_172, " ", "v_char_89", " ", (v_char_89 == 'z'), " ", "v_seq_101", " ", (v_seq_101 == []), " ", "v_map_64", " ", (v_map_64 == map['R' := true, 'D' := false, 'e' := true, 'J' := false]), " ", "v_seq_100", " ", (v_seq_100 == []), " ", "v_map_65", " ", (v_map_65 == map['B' := false, 'l' := false, 'M' := true]), " ", "v_seq_103", " ", (v_seq_103 == ['R', 'V']), " ", "v_seq_102", " ", (v_seq_102 == []), " ", "v_map_63", " ", (v_map_63 == map['G' := false, 'i' := true, 'L' := true, 'l' := false]), " ", "v_char_90", " ", (v_char_90 == 'A'), " ", "v_int_129", " ", v_int_129, " ", "v_int_133", " ", v_int_133, " ", "v_int_130", " ", v_int_130, " ", "v_int_131", " ", v_int_131, " ", "v_int_132", " ", v_int_132, " ", "v_char_91", " ", (v_char_91 == 'R'), " ", "v_int_real_real_8", " ", (v_int_real_real_8 == v_int_real_real_53), " ", "v_int_real_real_6.0", " ", v_int_real_real_6.0, " ", "v_int_real_real_7", " ", (v_int_real_real_7 == v_int_real_real_54), " ", "v_int_real_real_2.1", " ", (v_int_real_real_2.1 == 23.32), " ", "v_int_real_real_6", " ", (v_int_real_real_6 == v_int_real_real_55), " ", "v_int_real_real_2.2", " ", (v_int_real_real_2.2 == -14.86), " ", "v_int_real_real_5", " ", (v_int_real_real_5 == v_int_real_real_56), " ", "v_int_real_real_4", " ", (v_int_real_real_4 == v_int_real_real_57), " ", "v_int_real_real_2.0", " ", v_int_real_real_2.0, " ", "v_int_real_real_3", " ", (v_int_real_real_3 == v_int_real_real_58), " ", "v_int_real_real_2", " ", (v_int_real_real_2 == v_int_real_real_59), " ", "v_int_real_real_1", " ", (v_int_real_real_1 == v_int_real_real_60), " ", "v_int_104", " ", v_int_104, " ", "v_int_103", " ", v_int_103, " ", "v_int_115", " ", v_int_115, " ", "v_int_116", " ", v_int_116, " ", "v_int_117", " ", v_int_117, " ", "v_int_118", " ", v_int_118, " ", "v_int_real_real_7.2", " ", (v_int_real_real_7.2 == -27.43), " ", "v_int_111", " ", v_int_111, " ", "v_int_112", " ", v_int_112, " ", "v_int_real_real_7.0", " ", v_int_real_real_7.0, " ", "v_int_113", " ", v_int_113, " ", "v_int_real_real_7.1", " ", (v_int_real_real_7.1 == -16.28), " ", "v_int_114", " ", v_int_114, " ", "v_int_real_real_10", " ", (v_int_real_real_10 == v_int_real_real_61), " ", "v_int_110", " ", v_int_110, " ", "v_int_real_real_3.2", " ", (v_int_real_real_3.2 == -28.00), " ", "v_int_real_real_3.0", " ", v_int_real_real_3.0, " ", "v_int_real_real_3.1", " ", (v_int_real_real_3.1 == -5.13), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_1[4]", " ", (v_array_1[4] == map[v_int_real_real_62 := multiset{false, true}, v_int_real_real_63 := multiset{true}]), " ", "v_int_real_real_8.1", " ", (v_int_real_real_8.1 == 23.76), " ", "v_int_real_real_8.2", " ", (v_int_real_real_8.2 == 17.29), " ", "v_int_real_real_8.0", " ", v_int_real_real_8.0, " ", "v_char_79", " ", (v_char_79 == 'k'), " ", "v_char_78", " ", (v_char_78 == 'w'), " ", "v_int_real_real_4.1", " ", (v_int_real_real_4.1 == -23.26), " ", "v_map_57", " ", (v_map_57 == map['s' := 3, 'u' := 3, 'e' := 26, 'E' := 22]), " ", "v_int_real_real_4.2", " ", (v_int_real_real_4.2 == 15.63), " ", "v_map_58", " ", (v_map_58 == map['p' := 'j', 'W' := 'I']), " ", "v_int_real_real_4.0", " ", v_int_real_real_4.0, " ", "v_map_56", " ", (v_map_56 == map['d' := 0, 'F' := 21, 'i' := 27]), " ", "v_map_53", " ", (v_map_53 == map['D' := true, 'u' := true, 'j' := true, 'n' := false, 'o' := true]), " ", "v_map_54", " ", (v_map_54 == map['B' := 'F', 'd' := 'H', 'D' := 'y']), " ", "v_map_52", " ", (v_map_52 == map['q' := 'G', 'H' := 'R', 'Z' := 't', 'M' := 'I']), " ", "v_map_59", " ", (v_map_59 == map['u' := true]), " ", "v_char_87", " ", (v_char_87 == 'M'), " ", "v_array_1[2]", " ", (v_array_1[2] == map[v_int_real_real_64 := multiset{}]), " ", "v_char_86", " ", (v_char_86 == 'S'), " ", "v_char_85", " ", (v_char_85 == 'p'), " ", "v_char_84", " ", (v_char_84 == 'V'), " ", "v_char_83", " ", (v_char_83 == 'o'), " ", "v_char_82", " ", (v_char_82 == 'f'), " ", "v_char_80", " ", (v_char_80 == 'o'), " ", "v_map_60", " ", (v_map_60 == map['u' := 11, 'e' := 20, 'V' := 9, 'F' := 4, 'L' := 12]), " ", "v_map_61", " ", (v_map_61 == map['r' := 'J', 'f' := 'k', 'J' := 'B']), " ", "v_int_real_real_10.2", " ", (v_int_real_real_10.2 == -24.46), " ", "v_int_real_real_10.0", " ", v_int_real_real_10.0, " ", "v_int_real_real_10.1", " ", (v_int_real_real_10.1 == -3.34), " ", "v_map_62", " ", (v_map_62 == map['c' := 27.67, 'X' := -12.03, 'l' := -0.56, 'N' := 2.53]), " ", "v_int_real_real_9.2", " ", (v_int_real_real_9.2 == -17.40), " ", "v_int_real_real_9.0", " ", v_int_real_real_9.0, " ", "v_int_real_real_9.1", " ", (v_int_real_real_9.1 == -29.01), " ", "v_int_real_real_5.2", " ", (v_int_real_real_5.2 == -14.40), " ", "v_array_1[3]", " ", (v_array_1[3] == map[v_int_real_real_65 := multiset{}, v_int_real_real_66 := multiset{false, false, true, true}]), " ", "v_int_real_real_5.0", " ", v_int_real_real_5.0, " ", "v_int_real_real_5.1", " ", (v_int_real_real_5.1 == -10.11), " ", "v_int_real_real_1.2", " ", (v_int_real_real_1.2 == -27.15), " ", "v_int_real_real_1.0", " ", v_int_real_real_1.0, " ", "v_int_real_real_1.1", " ", (v_int_real_real_1.1 == 7.37), " ", "v_int_126", " ", v_int_126, " ", "v_int_127", " ", v_int_127, " ", "v_int_128", " ", v_int_128, " ", "v_seq_98", " ", v_seq_98, " ", "v_int_122", " ", v_int_122, " ", "v_seq_99", " ", (v_seq_99 == [29.12]), " ", "v_int_123", " ", v_int_123, " ", "v_int_124", " ", v_int_124, " ", "v_int_9", " ", v_int_9, " ", "v_int_125", " ", v_int_125, " ", "v_seq_94", " ", (v_seq_94 == ['W', 'R', 'M']), " ", "v_seq_95", " ", v_seq_95, " ", "v_seq_96", " ", v_seq_96, " ", "v_array_1[0]", " ", (v_array_1[0] == map[v_int_real_real_67 := multiset{}]), " ", "v_int_121", " ", v_int_121, " ", "v_seq_97", " ", v_seq_97, " ", "v_seq_90", " ", v_seq_90, " ", "v_seq_91", " ", (v_seq_91 == ['o', 'M', 'd', 'S']), " ", "v_char_88", " ", (v_char_88 == 'Q'), " ", "v_int_8", " ", v_int_8, " ", "v_int_10", " ", v_int_10, " ", "v_seq_87", " ", (v_seq_87 == ['s', 'M', 'd', 'S']), " ", "v_seq_88", " ", (v_seq_88 == ['s', 'M', 'd', 'S']), " ", "v_int_real_real_6.1", " ", (v_int_real_real_6.1 == 23.59), " ", "v_seq_89", " ", v_seq_89, " ", "v_int_real_real_6.2", " ", (v_int_real_real_6.2 == -18.47), " ", "v_int_real_real_9", " ", (v_int_real_real_9 == v_int_real_real_68), " ", "v_array_1[1]", " ", (v_array_1[1] == map[v_int_real_real_69 := multiset{}, v_int_real_real_70 := multiset{false, true}, v_int_real_real_71 := multiset{}, v_int_real_real_72 := multiset{}]), " ", "v_seq_84", " ", (v_seq_84 == ['s', 'M', 'x', 'S']), " ", "v_seq_85", " ", (v_seq_85 == ['s', 'M', 'x', 'S']), " ", "v_seq_86", " ", v_seq_86, "\n";
			return ;
		}
	}
	return ;
}
