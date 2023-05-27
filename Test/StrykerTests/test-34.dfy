// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
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

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: char, p_m_method_5_3: char) returns (ret_1: char)
	requires ((p_m_method_5_1 == 'd') && (p_m_method_5_3 == 'w') && (p_m_method_5_2 == 'H')) || ((p_m_method_5_1 == 'F') && (p_m_method_5_3 == 'A') && (p_m_method_5_2 == 'Y')) || ((p_m_method_5_1 == 'U') && (p_m_method_5_3 == 'l') && (p_m_method_5_2 == 'm')) || ((p_m_method_5_1 == 'E') && (p_m_method_5_3 == 'b') && (p_m_method_5_2 == 'L'));
	ensures (((p_m_method_5_1 == 'd') && (p_m_method_5_3 == 'w') && (p_m_method_5_2 == 'H')) ==> ((ret_1 == 'D'))) && (((p_m_method_5_1 == 'E') && (p_m_method_5_3 == 'b') && (p_m_method_5_2 == 'L')) ==> ((ret_1 == 'D'))) && (((p_m_method_5_1 == 'U') && (p_m_method_5_3 == 'l') && (p_m_method_5_2 == 'm')) ==> ((ret_1 == 'D'))) && (((p_m_method_5_1 == 'F') && (p_m_method_5_3 == 'A') && (p_m_method_5_2 == 'Y')) ==> ((ret_1 == 'D')));
{
	print "p_m_method_5_3", " ", (p_m_method_5_3 == 'l'), " ", "p_m_method_5_2", " ", (p_m_method_5_2 == 'm'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'U'), "\n";
	return 'D';
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char, p_m_method_4_3: char) returns (ret_1: real)
	requires ((p_m_method_4_2 == 'b') && (p_m_method_4_1 == 'H') && (p_m_method_4_3 == 'T'));
	ensures (((p_m_method_4_2 == 'b') && (p_m_method_4_1 == 'H') && (p_m_method_4_3 == 'T')) ==> ((21.07 < ret_1 < 21.27)));
{
	print "p_m_method_4_1", " ", (p_m_method_4_1 == 'H'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'T'), " ", "p_m_method_4_2", " ", (p_m_method_4_2 == 'b'), "\n";
	return 21.17;
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char, p_m_method_3_4: char) returns (ret_1: real)
	requires ((p_m_method_3_1 == 'J') && (p_m_method_3_3 == 'H') && (p_m_method_3_2 == 'D') && (p_m_method_3_4 == 'D'));
	ensures (((p_m_method_3_1 == 'J') && (p_m_method_3_3 == 'H') && (p_m_method_3_2 == 'D') && (p_m_method_3_4 == 'D')) ==> ((21.07 < ret_1 < 21.27)));
{
	var v_int_12: int := 2;
	var v_int_13: int := 18;
	var v_int_14: int := safe_modulus(v_int_12, v_int_13);
	var v_int_15: int, v_int_16: int := (18 / 21), v_int_14;
	for v_int_11 := v_int_15 to v_int_16 
		invariant (v_int_16 - v_int_11 >= 0)
	{
		var v_char_1: char := 'H';
		var v_char_2: char := 'b';
		var v_char_3: char := 'T';
		var v_real_1: real := m_method_4(v_char_1, v_char_2, v_char_3);
		print "v_char_1", " ", (v_char_1 == 'H'), " ", "v_int_11", " ", v_int_11, " ", "v_char_3", " ", (v_char_3 == 'T'), " ", "v_char_2", " ", (v_char_2 == 'b'), " ", "v_real_1", " ", (v_real_1 == 21.17), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_14", " ", v_int_14, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'D'), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'J'), " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 'D'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'H'), "\n";
		return v_real_1;
	}
	var v_char_4: char := p_m_method_3_3;
	var v_seq_5: seq<real> := [-10.14];
	var v_int_17: int := 25;
	return (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_17]) else (-17.56));
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

method m_method_2(p_m_method_2_1: seq<bool>, p_m_method_2_2: char) returns (ret_1: real)
	requires ((p_m_method_2_2 == 'D') && |p_m_method_2_1| == 4 && (p_m_method_2_1[0] == true) && (p_m_method_2_1[1] == false) && (p_m_method_2_1[2] == true) && (p_m_method_2_1[3] == false));
	ensures (((p_m_method_2_2 == 'D') && |p_m_method_2_1| == 4 && (p_m_method_2_1[0] == true) && (p_m_method_2_1[1] == false) && (p_m_method_2_1[2] == true) && (p_m_method_2_1[3] == false)) ==> ((21.07 < ret_1 < 21.27)));
{
	var v_seq_6: seq<char> := ['J'];
	var v_int_18: int := 12;
	var v_seq_17: seq<char> := v_seq_6;
	var v_int_32: int := v_int_18;
	var v_int_33: int := safe_index_seq(v_seq_17, v_int_32);
	v_int_18 := v_int_33;
	var v_char_13: char := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_18]) else ('m'));
	var v_char_5: char := 'd';
	var v_char_6: char := 'H';
	var v_char_7: char := 'w';
	var v_char_8: char := m_method_5(v_char_5, v_char_6, v_char_7);
	var v_char_14: char := v_char_8;
	var v_char_15: char := v_char_6;
	var v_char_9: char := 'F';
	var v_char_10: char := 'Y';
	var v_char_11: char := 'A';
	var v_char_12: char := m_method_5(v_char_9, v_char_10, v_char_11);
	var v_char_16: char := v_char_12;
	var v_real_2: real := m_method_3(v_char_13, v_char_14, v_char_15, v_char_16);
	print "v_char_16", " ", (v_char_16 == 'D'), " ", "v_char_15", " ", (v_char_15 == 'H'), " ", "v_char_5", " ", (v_char_5 == 'd'), " ", "v_char_14", " ", (v_char_14 == 'D'), " ", "v_char_13", " ", (v_char_13 == 'J'), " ", "v_char_7", " ", (v_char_7 == 'w'), " ", "v_char_12", " ", (v_char_12 == 'D'), " ", "v_char_6", " ", (v_char_6 == 'H'), " ", "v_char_11", " ", (v_char_11 == 'A'), " ", "v_char_9", " ", (v_char_9 == 'F'), " ", "v_char_8", " ", (v_char_8 == 'D'), " ", "v_int_18", " ", v_int_18, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_seq_6", " ", (v_seq_6 == ['J']), " ", "v_char_10", " ", (v_char_10 == 'Y'), " ", "v_real_2", " ", (v_real_2 == 21.17), " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'D'), "\n";
	return v_real_2;
}

method m_method_1(p_m_method_1_1: char, p_m_method_1_2: int, p_m_method_1_3: char) returns (ret_1: array<int>, ret_2: real, ret_3: map<int, int>)
	requires ((p_m_method_1_1 == 'D') && (p_m_method_1_3 == 'V') && (p_m_method_1_2 == 112));
	ensures (((p_m_method_1_1 == 'D') && (p_m_method_1_3 == 'V') && (p_m_method_1_2 == 112)) ==> (ret_1.Length == 4 && (ret_1[0] == 26) && (ret_1[1] == -1) && (ret_1[2] == 26) && (ret_1[3] == 25) && (21.07 < ret_2 < 21.27) && (ret_3 == map[17 := -2, 1 := 14, 2 := 15, 19 := 10, 21 := 21, 9 := 9, 11 := 22, 14 := 26, 15 := 3])));
{
	var v_array_1: array<int> := new int[3] [14, 25, 24];
	var v_array_2: array<int> := new int[4] [26, -1, 26, 25];
	var v_map_1: map<int, seq<array<int>>> := map[22 := [v_array_1, v_array_2]];
	var v_int_7: int := (8 / -27);
	var v_array_3: array<int> := new int[5] [23, 25, 4, 10, -20];
	var v_array_4: array<int> := new int[5] [11, -1, 15, 9, 25];
	var v_seq_4: seq<array<int>> := (if ((v_int_7 in v_map_1)) then (v_map_1[v_int_7]) else ((if (true) then ([]) else ([v_array_3, v_array_4]))));
	var v_seq_3: seq<bool> := ([true, false, true, false] + []);
	var v_int_8: int := v_array_1[0];
	var v_int_9: int := safe_index_seq(v_seq_3, v_int_8);
	var v_int_10: int := v_int_9;
	var v_seq_7: seq<bool> := v_seq_3;
	var v_map_2: map<char, char> := map['F' := 'G'];
	var v_char_17: char := 'E';
	var v_char_18: char := (match 'g' {
		case 'N' => (if ((v_char_17 in v_map_2)) then (v_map_2[v_char_17]) else ('b'))
		case 'e' => (if (true) then ('d') else ('n'))
		case _ => p_m_method_1_1
	});
	var v_real_3: real := m_method_2(v_seq_7, v_char_18);
	var v_seq_8: seq<int> := [1, 0];
	var v_seq_18: seq<int> := v_seq_8;
	var v_int_36: int := 27;
	var v_int_37: int := 11;
	var v_int_38: int, v_int_39: int := safe_subsequence(v_seq_18, v_int_36, v_int_37);
	var v_int_34: int, v_int_35: int := v_int_38, v_int_39;
	var v_seq_9: seq<int> := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_34..v_int_35]) else (v_seq_8));
	var v_int_19: int := (19 * 3);
	var v_int_20: int := 16;
	var v_int_21: int := 22;
	var v_int_22: int := safe_division(v_int_20, v_int_21);
	var v_seq_10: seq<int> := [];
	var v_int_23: int := 14;
	print "v_char_18", " ", (v_char_18 == 'D'), " ", "v_array_4[4]", " ", v_array_4[4], " ", "v_int_19", " ", v_int_19, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'D'), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_array_4[1]", " ", v_array_4[1], " ", "p_m_method_1_3", " ", (p_m_method_1_3 == 'V'), " ", "v_array_3[4]", " ", v_array_3[4], " ", "v_array_4[3]", " ", v_array_4[3], " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[22 := [v_array_1, v_array_2]]), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", v_seq_8, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_seq_3", " ", v_seq_3, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_real_3", " ", (v_real_3 == 21.17), " ", "v_array_3[3]", " ", v_array_3[3], " ", "v_array_4[0]", " ", v_array_4[0], " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_array_3[1]", " ", v_array_3[1], " ", "v_array_4[2]", " ", v_array_4[2], "\n";
	return (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_10]) else (v_array_2)), v_real_3, (map[17 := -2, 11 := 22, 14 := 26][2 := 15] + (if (true) then (map[9 := 9, 19 := 10, 21 := 21, 15 := 3]) else (map[29 := 26, -8 := 26, 13 := 5])))[(if ((|v_seq_9| > 0)) then (v_seq_9[v_int_19]) else ((28 - 27))) := (match 'B' {
		case 'E' => v_int_22
		case _ => (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_23]) else (14))
	})];
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_3: map<char, seq<char>> := map['s' := ['W']];
	var v_char_19: char := 'n';
	var v_seq_11: seq<char> := (if ((v_char_19 in v_map_3)) then (v_map_3[v_char_19]) else (['v', 'B']));
	var v_map_4: map<char, int> := map['M' := 6, 'P' := 14, 't' := 3];
	var v_char_20: char := 'b';
	var v_int_24: int := (if ((v_char_20 in v_map_4)) then (v_map_4[v_char_20]) else (-22));
	var v_seq_12: seq<char> := ['U', 'Y', 'I', 'd'];
	var v_int_25: int := 8;
	var v_seq_16: seq<char> := v_seq_12;
	var v_int_30: int := v_int_25;
	var v_int_31: int := safe_index_seq(v_seq_16, v_int_30);
	v_int_25 := v_int_31;
	var v_char_21: char := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_25]) else ('R'));
	var v_char_22: char := (if (true) then ('m') else ('i'));
	var v_seq_13: seq<char> := ['t', 'g', 'l'];
	var v_int_26: int := 2;
	var v_char_23: char := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_26]) else ('m'));
	var v_char_24: char := m_method_5(v_char_21, v_char_22, v_char_23);
	var v_char_25: char := 'E';
	var v_char_26: char := 'L';
	var v_char_27: char := 'b';
	var v_char_28: char := m_method_5(v_char_25, v_char_26, v_char_27);
	var v_char_30: char := (match 'A' {
		case 'l' => (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_24]) else (v_char_19))
		case 'm' => v_char_24
		case _ => (match 'N' {
			case 'a' => (if (true) then ('t') else ('t'))
			case _ => v_char_28
		})
	});
	var v_seq_14: seq<real> := [];
	var v_int_27: int := 19;
	var v_map_5: map<char, int> := map['I' := 6, 'v' := 3, 'E' := 15];
	var v_char_29: char := 'V';
	var v_int_28: int := (((if ((|v_seq_14| > 0)) then (v_seq_14[v_int_27]) else (28.97))).Floor * (if ((match 'u' {
		case 'V' => true
		case _ => false
	})) then ((if ((v_char_29 in v_map_5)) then (v_map_5[v_char_29]) else (19))) else (|map['i' := 'K', 'T' := 'x', 'I' := 'R', 'B' := 'O']|)));
	var v_char_31: char := v_char_29;
	var v_array_5: array<int>, v_real_4: real, v_map_6: map<int, int> := m_method_1(v_char_30, v_int_28, v_char_31);
	v_array_5, v_real_4, v_map_6 := v_array_5, v_real_4, v_map_6;
	v_char_29, v_char_31, v_char_30 := v_char_30, v_char_30, v_char_29;
	var v_map_9: map<char, seq<char>> := map['Q' := ['V', 'O'], 'k' := ['o']]['c' := ['M', 'Q']];
	var v_map_7: map<char, char> := map['B' := 'p', 'v' := 'R', 'C' := 'h'];
	var v_char_32: char := 'w';
	var v_char_34: char := (if ((v_char_32 in v_map_7)) then (v_map_7[v_char_32]) else ('h'));
	var v_map_8: map<char, seq<char>> := map['l' := []];
	var v_char_33: char := 'I';
	var v_seq_15: seq<char> := (if ((v_char_34 in v_map_9)) then (v_map_9[v_char_34]) else ((if ((v_char_33 in v_map_8)) then (v_map_8[v_char_33]) else (['m']))));
	var v_int_29: int := (v_int_27 + (28 / 18));
	var v_seq_19: seq<char> := v_seq_15;
	var v_int_40: int := v_int_29;
	var v_int_41: int := safe_index_seq(v_seq_19, v_int_40);
	v_int_29 := v_int_41;
	v_char_29, v_char_34, v_char_31, v_char_32 := v_char_31, (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_29]) else (v_char_30)), v_char_34, v_char_29;
	print "v_map_5", " ", (v_map_5 == map['E' := 15, 'v' := 3, 'I' := 6]), " ", "v_char_29", " ", (v_char_29 == 'D'), " ", "v_map_7", " ", (v_map_7 == map['B' := 'p', 'C' := 'h', 'v' := 'R']), " ", "v_map_6", " ", (v_map_6 == map[17 := -2, 1 := 14, 2 := 15, 19 := 10, 21 := 21, 9 := 9, 11 := 22, 14 := 26, 15 := 3]), " ", "v_map_9", " ", (v_map_9 == map['Q' := ['V', 'O'], 'c' := ['M', 'Q'], 'k' := ['o']]), " ", "v_map_8", " ", (v_map_8 == map['l' := []]), " ", "v_char_34", " ", (v_char_34 == 'm'), " ", "v_char_33", " ", (v_char_33 == 'I'), " ", "v_int_29", " ", v_int_29, " ", "v_seq_14", " ", (v_seq_14 == []), " ", "v_seq_15", " ", (v_seq_15 == ['m']), " ", "v_array_5", " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_char_32", " ", (v_char_32 == 'D'), " ", "v_char_31", " ", (v_char_31 == 'h'), " ", "v_char_30", " ", (v_char_30 == 'V'), " ", "v_real_4", " ", (v_real_4 == 21.17), "\n";
}
