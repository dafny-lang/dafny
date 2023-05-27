// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_5(DT_1_5_1: T_2)
datatype DT_2 = DT_2_1
method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method m_method_9(p_m_method_9_1: char, p_m_method_9_2: char, p_m_method_9_3: char, p_m_method_9_4: char) returns (ret_1: char)
{
	var v_map_4: map<char, char> := map['e' := 'h', 'S' := 'l', 'U' := 'q', 'E' := 'n'];
	var v_char_25: char := 'l';
	return (if ((v_char_25 in v_map_4)) then (v_map_4[v_char_25]) else ('y'));
}

method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_8(p_m_method_8_1: char, p_m_method_8_2: char) returns (ret_1: (char, char, char))
{
	var v_char_char_char_6: (char, char, char) := ('p', 'r', 'B');
	return v_char_char_char_6;
}

method m_method_7(p_m_method_7_1: char, p_m_method_7_2: char, p_m_method_7_3: char) returns (ret_1: (char, char, char))
{
	var v_map_3: map<char, char> := map['G' := 'I', 'Q' := 'S', 'c' := 'V'];
	var v_char_15: char := 'W';
	var v_char_21: char := (if ((v_char_15 in v_map_3)) then (v_map_3[v_char_15]) else ('M'));
	var v_bool_4: bool := ('p' !in map['n' := 'g', 'w' := 'l', 'q' := 'g', 'g' := 'h', 'X' := 'S']);
	var v_char_16: char := 'o';
	var v_char_17: char := 'c';
	var v_char_18: char := 'D';
	var v_char_19: char := 'J';
	var v_char_20: char := m_method_4(v_char_16, v_char_17, v_char_18, v_char_19);
	var v_char_22: char := v_char_20;
	var v_bool_5: bool := m_method_6(v_char_21, v_bool_4, v_char_22);
	if v_bool_5 {
		
	}
	if (if (v_bool_4) then (('v' in map['v' := 's', 'H' := 'D'])) else (v_bool_4)) {
		var v_char_char_char_1: (char, char, char) := ('e', 'V', 'Q');
		var v_char_char_char_2: (char, char, char) := ('j', 'j', 'b');
		var v_char_char_char_3: (char, char, char) := ('Y', 'w', 'C');
		var v_char_char_char_4: (char, char, char) := ('o', 'Z', 'S');
		var v_seq_17: seq<(char, char, char)> := [v_char_char_char_1, v_char_char_char_2, v_char_char_char_3, v_char_char_char_4];
		var v_seq_18: seq<(char, char, char)> := v_seq_17;
		var v_int_32: int := 24;
		var v_int_33: int := safe_index_seq(v_seq_18, v_int_32);
		var v_int_34: int := v_int_33;
		var v_char_char_char_5: (char, char, char) := ('N', 's', 'E');
		var v_seq_20: seq<(char, char, char)> := (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_34 := v_char_char_char_5]) else (v_seq_17));
		var v_seq_19: seq<int> := [13];
		var v_int_35: int := 10;
		var v_int_36: int := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_35]) else (10));
		var v_char_23: char := 'Y';
		var v_char_24: char := 'k';
		var v_char_char_char_7: (char, char, char) := m_method_8(v_char_23, v_char_24);
		return (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_36]) else (v_char_char_char_7));
	}
	var v_char_char_char_8: (char, char, char) := ('Q', 'G', 'w');
	var v_char_char_char_9: (char, char, char) := ('w', 'u', 'c');
	var v_char_char_char_10: (char, char, char) := ('I', 'f', 'H');
	var v_char_char_char_11: (char, char, char) := ('P', 'K', 'R');
	var v_char_char_char_12: (char, char, char) := ('V', 'Z', 'c');
	var v_char_char_char_13: (char, char, char) := ('q', 'h', 'c');
	var v_char_char_char_14: (char, char, char) := ('F', 'E', 'L');
	var v_seq_21: seq<(char, char, char)> := ([v_char_char_char_8, v_char_char_char_9, v_char_char_char_10, v_char_char_char_11] + [v_char_char_char_12, v_char_char_char_13, v_char_char_char_14]);
	var v_int_37: int := (-6 * 25);
	var v_char_char_char_15: (char, char, char) := ('R', 'M', 'T');
	var v_char_char_char_16: (char, char, char) := ('N', 'l', 'u');
	var v_seq_22: seq<(char, char, char)> := [v_char_char_char_15, v_char_char_char_16];
	var v_int_38: int := 22;
	var v_char_char_char_17: (char, char, char) := ('S', 'e', 'C');
	return (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_37]) else ((if ((|v_seq_22| > 0)) then (v_seq_22[v_int_38]) else (v_char_char_char_17))));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: char, p_m_method_6_2: bool, p_m_method_6_3: char) returns (ret_1: bool)
{
	if p_m_method_6_2 {
		return (false && true);
	}
	return p_m_method_6_2;
}

method m_method_5(p_m_method_5_1: char, p_m_method_5_2: char) returns (ret_1: bool)
{
	if (if (false) then (true) else (true)) {
		return (if (true) then (false) else (false));
	} else {
		return (if (true) then (false) else (false));
	}
}

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: char, p_m_method_4_3: char, p_m_method_4_4: char) returns (ret_1: char)
{
	return 'S';
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char) returns (ret_1: seq<bool>)
{
	return [false, false, false];
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

method m_method_2(p_m_method_2_1: char) returns (ret_1: seq<int>)
{
	return [6, 28];
}

method m_method_1(p_m_method_1_1: int) returns (ret_1: seq<char>)
	requires ((p_m_method_1_1 == 0));
	ensures (((p_m_method_1_1 == 0)) ==> (|ret_1| == 4 && (ret_1[0] == 'a') && (ret_1[1] == 'C') && (ret_1[2] == 'i') && (ret_1[3] == 'O')));
{
	var v_seq_5: seq<bool> := [];
	var v_int_10: int := 1;
	if (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_10]) else (true)) {
		
	} else {
		var v_int_11: int := (22 / 24);
		var v_int_12: int := p_m_method_1_1;
		while (v_int_11 < v_int_12) 
			decreases v_int_12 - v_int_11;
			invariant (v_int_11 <= v_int_12);
		{
			v_int_11 := (v_int_11 + 1);
		}
	}
	var v_seq_6: seq<int> := [13, 26, 17];
	var v_int_14: int := 19;
	var v_seq_42: seq<int> := v_seq_6;
	var v_int_63: int := v_int_14;
	var v_int_64: int := safe_index_seq(v_seq_42, v_int_63);
	v_int_14 := v_int_64;
	var v_int_15: int, v_int_16: int := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_14]) else (21)), (match false {
		case true => 5
		case _ => 16
	});
	for v_int_13 := v_int_15 to v_int_16 
		invariant (v_int_16 - v_int_13 >= 0)
	{
		print "v_int_13", " ", v_int_13, " ", "v_seq_6", " ", v_seq_6, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_10", " ", v_int_10, " ", "v_int_14", " ", v_int_14, "\n";
		continue;
	}
	var v_bool_bool_bool_1: (bool, bool, bool) := (false, true, true);
	var v_array_1: array<bool> := new bool[4] [true, true, true, true];
	var v_bool_bool_bool_array_1: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_1, v_array_1);
	var v_bool_bool_bool_2: (bool, bool, bool) := (true, true, true);
	var v_array_2: array<bool> := new bool[5] [false, false, false, false, true];
	var v_bool_bool_bool_array_2: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_2, v_array_2);
	var v_map_1: map<((bool, bool, bool), array<bool>), seq<char>> := map[v_bool_bool_bool_array_1 := ['m'], v_bool_bool_bool_array_2 := []];
	var v_bool_bool_bool_3: (bool, bool, bool) := (false, true, true);
	var v_array_3: array<bool> := new bool[3];
	v_array_3[0] := false;
	v_array_3[1] := true;
	v_array_3[2] := true;
	var v_bool_bool_bool_array_3: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_3, v_array_3);
	var v_bool_bool_bool_array_4: ((bool, bool, bool), array<bool>) := v_bool_bool_bool_array_3;
	var v_bool_bool_bool_4: (bool, bool, bool) := (true, true, true);
	var v_bool_bool_bool_array_5: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_4, v_array_2);
	var v_bool_bool_bool_5: (bool, bool, bool) := (false, true, true);
	var v_bool_bool_bool_array_6: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_5, v_array_3);
	var v_bool_bool_bool_6: (bool, bool, bool) := (false, true, true);
	var v_bool_bool_bool_array_7: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_6, v_array_3);
	var v_bool_bool_bool_7: (bool, bool, bool) := (false, true, true);
	var v_bool_bool_bool_array_8: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_7, v_array_1);
	var v_bool_bool_bool_8: (bool, bool, bool) := (false, true, true);
	var v_bool_bool_bool_array_9: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_8, v_array_1);
	var v_bool_bool_bool_9: (bool, bool, bool) := (true, true, true);
	var v_bool_bool_bool_array_10: ((bool, bool, bool), array<bool>) := (v_bool_bool_bool_9, v_array_2);
	print "v_bool_bool_bool_1", " ", v_bool_bool_bool_1, " ", "v_bool_bool_bool_3", " ", v_bool_bool_bool_3, " ", "v_bool_bool_bool_2", " ", v_bool_bool_bool_2, " ", "v_bool_bool_bool_1.2", " ", v_bool_bool_bool_1.2, " ", "v_bool_bool_bool_2.1", " ", v_bool_bool_bool_2.1, " ", "v_bool_bool_bool_3.0", " ", v_bool_bool_bool_3.0, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "v_bool_bool_bool_1.1", " ", v_bool_bool_bool_1.1, " ", "v_bool_bool_bool_2.0", " ", v_bool_bool_bool_2.0, " ", "v_bool_bool_bool_3.2", " ", v_bool_bool_bool_3.2, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_bool_bool_bool_2.2", " ", v_bool_bool_bool_2.2, " ", "v_bool_bool_bool_3.1", " ", v_bool_bool_bool_3.1, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_bool_bool_bool_array_2", " ", (v_bool_bool_bool_array_2 == v_bool_bool_bool_array_5), " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_array_3[0]", " ", v_array_3[0], " ", "v_bool_bool_bool_array_3", " ", (v_bool_bool_bool_array_3 == v_bool_bool_bool_array_6), " ", "v_bool_bool_bool_array_4", " ", (v_bool_bool_bool_array_4 == v_bool_bool_bool_array_7), " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_bool_bool_bool_1.0", " ", v_bool_bool_bool_1.0, " ", "v_array_2[3]", " ", v_array_2[3], " ", "v_array_3[2]", " ", v_array_3[2], " ", "v_bool_bool_bool_array_1", " ", (v_bool_bool_bool_array_1 == v_bool_bool_bool_array_8), " ", "v_bool_bool_bool_array_3.1", " ", (v_bool_bool_bool_array_3.1 == v_array_3), " ", "v_map_1", " ", (v_map_1 == map[v_bool_bool_bool_array_9 := ['m'], v_bool_bool_bool_array_10 := []]), " ", "v_bool_bool_bool_array_1.0", " ", v_bool_bool_bool_array_1.0, " ", "v_bool_bool_bool_array_1.1", " ", (v_bool_bool_bool_array_1.1 == v_array_1), " ", "v_bool_bool_bool_array_2.0", " ", v_bool_bool_bool_array_2.0, " ", "v_bool_bool_bool_array_2.1", " ", (v_bool_bool_bool_array_2.1 == v_array_2), " ", "v_bool_bool_bool_array_3.0", " ", v_bool_bool_bool_array_3.0, " ", "v_seq_6", " ", v_seq_6, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_10", " ", v_int_10, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_array_2[4]", " ", v_array_2[4], " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], " ", "v_array_3[1]", " ", v_array_3[1], "\n";
	return (if ((v_bool_bool_bool_array_4 in v_map_1)) then (v_map_1[v_bool_bool_bool_array_4]) else (['a', 'C', 'i', 'O']));
}

method m_method_10(p_m_method_10_1: char) returns (ret_1: char)
{
	return 'G';
}

method Main() returns ()
{
	var v_seq_3: seq<seq<int>> := [[27, 28], [], [12, 18], [15, 13, 17, 10]];
	var v_int_8: int := 25;
	var v_seq_41: seq<seq<int>> := v_seq_3;
	var v_int_61: int := v_int_8;
	var v_int_62: int := safe_index_seq(v_seq_41, v_int_61);
	v_int_8 := v_int_62;
	var v_seq_4: seq<int> := ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_8]) else ([25, -29, 11, 27])) + ([] + []));
	var v_int_9: int := v_int_8;
	var v_int_17: int := v_int_8;
	var v_seq_7: seq<char> := m_method_1(v_int_17);
	var v_seq_8: seq<char> := v_seq_7;
	var v_int_18: int := v_int_17;
	var v_int_19: int := safe_index_seq(v_seq_8, v_int_18);
	var v_int_41: int, v_int_42: int := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_9]) else (v_int_8)), v_int_19;
	for v_int_7 := v_int_41 downto v_int_42 
		invariant (v_int_7 - v_int_42 >= 0) && ((((v_int_7 == 26)) ==> (((|v_seq_4| == 2 && (v_seq_4[0] == 27) && (v_seq_4[1] == 28))))))
	{
		var v_int_22: int := v_int_9;
		var v_int_23: int := (1 - 2);
		var v_int_24: int := safe_division(v_int_22, v_int_23);
		var v_int_20: int := (v_int_17 * v_int_24);
		var v_int_21: int := v_int_22;
		while (v_int_20 < v_int_21) 
			decreases v_int_21 - v_int_20;
			invariant (v_int_20 <= v_int_21) && ((((v_int_20 == 0)) ==> (((|v_seq_4| == 2 && (v_seq_4[0] == 27) && (v_seq_4[1] == 28))))));
		{
			v_int_20 := (v_int_20 + 1);
			var v_char_1: char := 'Y';
			var v_seq_9: seq<int> := m_method_2(v_char_1);
			var v_seq_12: seq<int> := (v_seq_9 + ([6, 18, 1, 4] + [21, 22, 9, 7]));
			var v_seq_13: seq<int> := v_seq_12;
			var v_int_27: int := v_int_24;
			var v_int_28: int := safe_index_seq(v_seq_13, v_int_27);
			var v_int_29: int := v_int_28;
			var v_seq_10: seq<int> := (match 'A' {
				case _ => [28, 11]
			});
			var v_int_25: int := (20 * -1);
			var v_seq_11: seq<int> := [];
			var v_int_26: int := 15;
			var v_char_2: char := 't';
			var v_char_3: char := 'L';
			var v_char_4: char := 'd';
			var v_seq_14: seq<bool> := m_method_3(v_char_2, v_char_3, v_char_4);
			var v_seq_15: seq<bool> := v_seq_14;
			var v_int_30: int := v_int_28;
			var v_char_5: char := 'D';
			var v_char_6: char := 'h';
			var v_char_7: char := 'f';
			var v_char_8: char := 's';
			var v_char_9: char := m_method_4(v_char_5, v_char_6, v_char_7, v_char_8);
			var v_map_2: map<char, char> := map['t' := 'Z'];
			var v_char_10: char := 'Q';
			var v_char_11: char := (if ((v_char_10 in v_map_2)) then (v_map_2[v_char_10]) else ('A'));
			var v_char_12: char := (match 'm' {
				case _ => 'N'
			});
			var v_bool_1: bool := m_method_5(v_char_11, v_char_12);
			var v_char_13: char := v_char_6;
			var v_bool_2: bool := (multiset({'k', 'I'}) != multiset{'b', 'L'});
			var v_char_14: char := v_char_1;
			var v_bool_3: bool := m_method_6(v_char_13, v_bool_2, v_char_14);
			var v_seq_16: seq<bool> := [];
			var v_int_31: int := 4;
			var v_char_28: char := v_char_14;
			var v_char_29: char := v_char_5;
			var v_char_30: char := (if (false) then ('j') else ('r'));
			var v_char_26: char := 'v';
			var v_char_27: char := m_method_10(v_char_26);
			var v_char_31: char := v_char_27;
			var v_char_32: char := m_method_9(v_char_28, v_char_29, v_char_30, v_char_31);
			var v_char_37: char := v_char_32;
			var v_char_33: char := 'W';
			var v_bool_6: bool := false;
			var v_char_34: char := 's';
			var v_bool_7: bool := m_method_6(v_char_33, v_bool_6, v_char_34);
			var v_map_5: map<char, char> := map['q' := 'Q', 'F' := 'm', 'v' := 'g'];
			var v_char_35: char := 'd';
			var v_map_6: map<char, char> := map['m' := 'Q', 'n' := 'u', 'g' := 'N'];
			var v_char_36: char := 'p';
			var v_char_38: char := (if (v_bool_7) then ((if ((v_char_35 in v_map_5)) then (v_map_5[v_char_35]) else ('t'))) else ((if ((v_char_36 in v_map_6)) then (v_map_6[v_char_36]) else ('t'))));
			var v_char_39: char := (if (v_bool_3) then ((if (true) then ('p') else ('y'))) else (v_char_1));
			var v_char_char_char_18: (char, char, char) := m_method_7(v_char_37, v_char_38, v_char_39);
			var v_char_41: char := v_char_14;
			var v_char_42: char := v_char_11;
			var v_char_43: char := v_char_26;
			var v_seq_23: seq<bool> := [false, false];
			var v_int_39: int := 17;
			var v_map_7: map<char, char> := map['b' := 'M', 'c' := 'j', 'b' := 'S', 'm' := 'g', 'd' := 'O'];
			var v_char_40: char := 'v';
			var v_seq_24: seq<char> := ['c', 'V', 'Q', 'K'];
			var v_int_40: int := -15;
			var v_char_44: char := (if ((if ((|v_seq_23| > 0)) then (v_seq_23[v_int_39]) else (true))) then ((if ((v_char_40 in v_map_7)) then (v_map_7[v_char_40]) else ('T'))) else ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_40]) else ('K'))));
			var v_char_45: char := m_method_4(v_char_41, v_char_42, v_char_43, v_char_44);
			v_seq_4, v_bool_7, v_bool_1, v_char_char_char_18, v_char_40 := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_29 := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_25]) else ((if ((|v_seq_11| > 0)) then (v_seq_11[v_int_26]) else (28))))]) else (v_seq_12)), (if ((if ((|v_seq_15| > 0)) then (v_seq_15[v_int_30]) else ((true && false)))) then ((v_char_9 in (['e'] + ['b', 'q', 'X']))) else (v_bool_1)), (if ((match 'P' {
				case _ => (true ==> true)
			})) then (v_bool_3) else ((if ((true <==> true)) then ((false != true)) else ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_31]) else (true)))))), v_char_char_char_18, v_char_45;
			break;
		}
		print "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_int_7", " ", v_int_7, " ", "v_int_20", " ", v_int_20, " ", "v_seq_8", " ", (v_seq_8 == ['a', 'C', 'i', 'O']), " ", "v_seq_7", " ", (v_seq_7 == ['a', 'C', 'i', 'O']), " ", "v_seq_4", " ", v_seq_4, " ", "v_int_17", " ", v_int_17, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, "\n";
		return ;
	}
	var v_seq_25: seq<bool> := [false, true, false];
	var v_int_43: int := 4;
	var v_map_8: map<char, char> := map['O' := 'J', 'F' := 'K', 'G' := 'p'];
	var v_char_46: char := 'M';
	var v_map_9: map<char, char> := map['v' := 'A', 'e' := 'W', 'U' := 'j', 'U' := 's', 'q' := 'J'];
	var v_char_47: char := 'C';
	var v_seq_26: seq<char> := [];
	var v_seq_27: seq<char> := (if ((|v_seq_26| > 0)) then (v_seq_26[11..18]) else (v_seq_26));
	var v_int_44: int := (14 % -15);
	match (if ((if (('i' in map['s' := 'K', 'Z' := 'H', 'E' := 'N', 'C' := 'r'])) then ((match 'l' {
		case _ => true
	})) else ((if ((|v_seq_25| > 0)) then (v_seq_25[v_int_43]) else (true))))) then ((match 'U' {
		case _ => (if ((v_char_47 in v_map_9)) then (v_map_9[v_char_47]) else ('Z'))
	})) else ((if ((|v_seq_27| > 0)) then (v_seq_27[v_int_44]) else ((match 'x' {
		case _ => 'H'
	}))))) {
		case _ => {
			assert true;
			expect true;
			return ;
		}
		
	}
	
	assert true;
	expect true;
	return ;
}
