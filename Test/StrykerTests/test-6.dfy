// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1 | DT_1_2
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

method m_method_4(p_m_method_4_1: char, p_m_method_4_2: DT_1, p_m_method_4_3: char, p_m_method_4_4: char) returns (ret_1: bool)
	requires ((p_m_method_4_2.DT_1_2? && ((p_m_method_4_2 == DT_1_2))) && (p_m_method_4_1 == 'G') && (p_m_method_4_4 == 'Y') && (p_m_method_4_3 == 'O'));
	ensures (((p_m_method_4_2.DT_1_2? && ((p_m_method_4_2 == DT_1_2))) && (p_m_method_4_1 == 'G') && (p_m_method_4_4 == 'Y') && (p_m_method_4_3 == 'O')) ==> ((ret_1 == false)));
{
	var v_int_35: int := 25;
	print "v_int_35", " ", v_int_35, " ", "p_m_method_4_4", " ", (p_m_method_4_4 == 'Y'), " ", "p_m_method_4_1", " ", (p_m_method_4_1 == 'G'), " ", "p_m_method_4_3", " ", (p_m_method_4_3 == 'O'), " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return false;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: bool, p_m_method_3_3: DT_1, p_m_method_3_4: int) returns (ret_1: real)
{
	if false {
		return -4.77;
	}
	return 29.96;
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

method m_method_2(p_m_method_2_1: bool, p_m_method_2_2: bool, p_m_method_2_3: bool) returns (ret_1: char)
{
	return (match 'y' {
		case _ => 'Q'
	});
}

method m_method_1(p_m_method_1_1: bool, p_m_method_1_2: real) returns (ret_1: char)
	requires ((p_m_method_1_1 == true) && (14.06 < p_m_method_1_2 < 14.26));
	ensures (((p_m_method_1_1 == true) && (14.06 < p_m_method_1_2 < 14.26)) ==> ((ret_1 == 'k')));
{
	assert ((p_m_method_1_1 == true) && (p_m_method_1_2 == 14.16));
	expect ((p_m_method_1_1 == true) && (p_m_method_1_2 == 14.16));
	var v_seq_6: seq<int> := [];
	var v_int_17: int := 3;
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_int_int_bool_1: (int, int, bool) := (-17, 14, false);
	var v_DT_1_1_int_int_bool_1: (DT_1, (int, int, bool)) := (v_DT_1_1_1, v_int_int_bool_1);
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_int_int_bool_2: (int, int, bool) := (18, 29, true);
	var v_DT_1_1_int_int_bool_2: (DT_1, (int, int, bool)) := (v_DT_1_1_2, v_int_int_bool_2);
	var v_DT_1_1_3: DT_1 := DT_1_1;
	var v_int_int_bool_3: (int, int, bool) := (-20, 24, true);
	var v_DT_1_1_int_int_bool_3: (DT_1, (int, int, bool)) := (v_DT_1_1_3, v_int_int_bool_3);
	var v_DT_1_1_4: DT_1 := DT_1_1;
	var v_int_int_bool_4: (int, int, bool) := (1, -14, true);
	var v_DT_1_1_int_int_bool_4: (DT_1, (int, int, bool)) := (v_DT_1_1_4, v_int_int_bool_4);
	var v_DT_1_1_5: DT_1 := DT_1_1;
	var v_int_int_bool_5: (int, int, bool) := (28, 4, false);
	var v_DT_1_1_int_int_bool_5: (DT_1, (int, int, bool)) := (v_DT_1_1_5, v_int_int_bool_5);
	var v_DT_1_1_6: DT_1 := DT_1_1;
	var v_int_int_bool_6: (int, int, bool) := (2, 4, false);
	var v_DT_1_1_int_int_bool_6: (DT_1, (int, int, bool)) := (v_DT_1_1_6, v_int_int_bool_6);
	var v_DT_1_1_7: DT_1 := DT_1_1;
	var v_int_int_bool_7: (int, int, bool) := (22, 3, false);
	var v_DT_1_1_int_int_bool_7: (DT_1, (int, int, bool)) := (v_DT_1_1_7, v_int_int_bool_7);
	var v_DT_1_1_8: DT_1 := DT_1_1;
	var v_int_int_bool_8: (int, int, bool) := (5, 24, false);
	var v_DT_1_1_int_int_bool_8: (DT_1, (int, int, bool)) := (v_DT_1_1_8, v_int_int_bool_8);
	var v_DT_1_1_9: DT_1 := DT_1_1;
	var v_int_int_bool_9: (int, int, bool) := (-14, 0, false);
	var v_DT_1_1_int_int_bool_9: (DT_1, (int, int, bool)) := (v_DT_1_1_9, v_int_int_bool_9);
	var v_seq_7: seq<seq<(DT_1, (int, int, bool))>> := [[v_DT_1_1_int_int_bool_1, v_DT_1_1_int_int_bool_2, v_DT_1_1_int_int_bool_3, v_DT_1_1_int_int_bool_4], [v_DT_1_1_int_int_bool_5, v_DT_1_1_int_int_bool_6], [v_DT_1_1_int_int_bool_7, v_DT_1_1_int_int_bool_8, v_DT_1_1_int_int_bool_9]];
	var v_int_18: int := -26;
	var v_seq_22: seq<seq<(DT_1, (int, int, bool))>> := v_seq_7;
	var v_int_47: int := v_int_18;
	var v_int_48: int := safe_index_seq(v_seq_22, v_int_47);
	v_int_18 := v_int_48;
	var v_DT_1_1_10: DT_1 := DT_1_1;
	var v_int_int_bool_10: (int, int, bool) := (28, 29, true);
	var v_DT_1_1_int_int_bool_10: (DT_1, (int, int, bool)) := (v_DT_1_1_10, v_int_int_bool_10);
	var v_seq_8: seq<(DT_1, (int, int, bool))> := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_18]) else ([v_DT_1_1_int_int_bool_10]));
	var v_int_19: int := v_int_int_bool_1.1;
	var v_seq_24: seq<(DT_1, (int, int, bool))> := v_seq_8;
	var v_int_51: int := v_int_19;
	var v_int_52: int := safe_index_seq(v_seq_24, v_int_51);
	v_int_19 := v_int_52;
	var v_DT_1_1_11: DT_1 := DT_1_1;
	var v_int_int_bool_11: (int, int, bool) := (26, 17, false);
	var v_DT_1_1_int_int_bool_11: (DT_1, (int, int, bool)) := (v_DT_1_1_11, v_int_int_bool_11);
	var v_seq_9: seq<(DT_1, (int, int, bool))> := [v_DT_1_1_int_int_bool_11];
	var v_int_20: int := 5;
	var v_DT_1_1_12: DT_1 := DT_1_1;
	var v_int_int_bool_12: (int, int, bool) := (20, 0, false);
	var v_DT_1_1_int_int_bool_12: (DT_1, (int, int, bool)) := (v_DT_1_1_12, v_int_int_bool_12);
	var v_DT_1_1_13: DT_1 := DT_1_1;
	var v_DT_1_1_14: DT_1 := DT_1_1;
	var v_seq_10: seq<DT_1> := [v_DT_1_1_13, v_DT_1_1_14];
	var v_seq_11: seq<DT_1> := v_seq_10;
	var v_int_21: int := 19;
	var v_int_22: int := safe_index_seq(v_seq_11, v_int_21);
	var v_int_23: int := v_int_22;
	var v_DT_1_1_15: DT_1 := DT_1_1;
	var v_seq_13: seq<DT_1> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_23 := v_DT_1_1_15]) else (v_seq_10));
	var v_seq_12: seq<int> := [7, 4, 8, 3];
	var v_int_24: int := 7;
	var v_seq_23: seq<int> := v_seq_12;
	var v_int_49: int := v_int_24;
	var v_int_50: int := safe_index_seq(v_seq_23, v_int_49);
	v_int_24 := v_int_50;
	var v_int_25: int := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_24]) else (16));
	var v_seq_25: seq<DT_1> := v_seq_13;
	var v_int_53: int := v_int_25;
	var v_int_54: int := safe_index_seq(v_seq_25, v_int_53);
	v_int_25 := v_int_54;
	v_int_22, v_DT_1_1_int_int_bool_8, v_DT_1_1_13 := ((if (false) then (2) else (0)) - (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_17]) else (14))), (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_19]) else ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_20]) else (v_DT_1_1_int_int_bool_12)))), (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_25]) else (v_DT_1_1_7));
	var v_int_28: int := v_int_int_bool_1.1;
	var v_int_29: int := v_int_int_bool_5.0;
	var v_int_30: int := safe_modulus(v_int_28, v_int_29);
	var v_int_26: int := v_int_30;
	var v_int_27: int := (v_int_int_bool_5.1 % (if (true) then (21) else (16)));
	while (v_int_26 < v_int_27) 
		decreases v_int_27 - v_int_26;
		invariant (v_int_26 <= v_int_27);
	{
		v_int_26 := (v_int_26 + 1);
		var v_map_2: map<bool, set<int>> := map[false := {27, -1, 0, 29}, false := {}, true := {26}, false := {28, 16, 23}];
		var v_bool_1: bool := true;
		var v_bool_2: bool := v_int_int_bool_8.2;
		var v_bool_3: bool := (if (false) then (false) else (false));
		var v_seq_14: seq<bool> := [false];
		var v_int_31: int := 28;
		var v_bool_4: bool := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_31]) else (false));
		var v_char_1: char := m_method_2(v_bool_2, v_bool_3, v_bool_4);
		var v_int_32: int := 29;
		var v_bool_5: bool := false;
		var v_DT_1_2_1: DT_1 := DT_1_2;
		var v_DT_1_2_2: DT_1 := v_DT_1_2_1;
		var v_int_33: int := 23;
		var v_real_1: real := m_method_3(v_int_32, v_bool_5, v_DT_1_2_2, v_int_33);
		var v_map_3: map<int, seq<int>>, v_char_2: char, v_int_34: int := ((map[6 := [27, 19], 2 := [12, 25, 12, 22]] - {16}) - (if ((v_bool_1 in v_map_2)) then (v_map_2[v_bool_1]) else ({}))), v_char_1, (v_real_1).Floor;
		var v_char_3: char := 'W';
		var v_DT_1_2_3: DT_1 := DT_1_2;
		var v_DT_1_2_4: DT_1 := v_DT_1_2_3;
		var v_char_4: char := 'x';
		var v_char_5: char := 'Q';
		var v_bool_6: bool := m_method_4(v_char_3, v_DT_1_2_4, v_char_4, v_char_5);
		var v_bool_int_1: (bool, int) := (false, 3);
		var v_bool_int_bool_1: ((bool, int), bool) := (v_bool_int_1, false);
		var v_bool_int_2: (bool, int) := (false, 1);
		var v_bool_int_bool_2: ((bool, int), bool) := (v_bool_int_2, false);
		var v_map_4: map<((bool, int), bool), bool> := map[v_bool_int_bool_1 := false, v_bool_int_bool_2 := true];
		var v_bool_int_3: (bool, int) := (false, 6);
		var v_bool_int_bool_3: ((bool, int), bool) := (v_bool_int_3, false);
		var v_bool_int_bool_4: ((bool, int), bool) := v_bool_int_bool_3;
		if (match 'a' {
			case _ => (if ((v_bool_int_bool_4 in v_map_4)) then (v_map_4[v_bool_int_bool_4]) else (true))
		}) {
			var v_bool_8: bool := v_int_int_bool_10.2;
			var v_char_6: char := 'Z';
			var v_DT_1_2_5: DT_1 := DT_1_2;
			var v_DT_1_2_6: DT_1 := v_DT_1_2_5;
			var v_char_7: char := 'L';
			var v_char_8: char := 's';
			var v_bool_7: bool := m_method_4(v_char_6, v_DT_1_2_6, v_char_7, v_char_8);
			var v_bool_9: bool := v_bool_7;
			var v_bool_10: bool := ('c' < 'W');
			var v_char_9: char := m_method_2(v_bool_8, v_bool_9, v_bool_10);
			return v_char_9;
		} else {
			var v_seq_15: seq<seq<bool>> := [[false, false, true], [], [true, false, false], [true, true, false]];
			var v_int_36: int := 9;
			var v_seq_16: seq<bool> := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_36]) else ([true, true, true]));
			var v_int_37: int := (match 'y' {
				case _ => 5
			});
			if (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_37]) else ((match 22 {
				case _ => true
			}))) {
				var v_map_5: map<int, char> := map[3 := 'p', 19 := 'C', 15 := 'o'];
				var v_int_38: int := 25;
				return (if ((22 > 23)) then ((match 19 {
					case _ => 'c'
				})) else ((if ((v_int_38 in v_map_5)) then (v_map_5[v_int_38]) else ('X'))));
			}
			var v_seq_17: seq<array<int>> := [];
			var v_int_39: int := -14;
			var v_array_25: array<int> := new int[3];
			v_array_25[0] := 1;
			v_array_25[1] := -9;
			v_array_25[2] := 3;
			match (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_39]) else (v_array_25)).Length {
				case _ => {
					return v_char_2;
				}
				
			}
			
		}
	}
	var v_seq_18: seq<char> := [];
	var v_int_40: int := 7;
	print "v_DT_1_1_int_int_bool_8.1", " ", v_DT_1_1_int_int_bool_8.1, " ", "v_DT_1_1_int_int_bool_7", " ", v_DT_1_1_int_int_bool_7, " ", "v_DT_1_1_int_int_bool_8", " ", v_DT_1_1_int_int_bool_8, " ", "v_int_int_bool_11.2", " ", v_int_int_bool_11.2, " ", "v_DT_1_1_int_int_bool_4.0", " ", v_DT_1_1_int_int_bool_4.0, " ", "v_DT_1_1_int_int_bool_9", " ", v_DT_1_1_int_int_bool_9, " ", "v_DT_1_1_int_int_bool_3", " ", v_DT_1_1_int_int_bool_3, " ", "v_DT_1_1_int_int_bool_4", " ", v_DT_1_1_int_int_bool_4, " ", "v_DT_1_1_int_int_bool_4.1", " ", v_DT_1_1_int_int_bool_4.1, " ", "v_DT_1_1_int_int_bool_5", " ", v_DT_1_1_int_int_bool_5, " ", "v_DT_1_1_int_int_bool_8.0", " ", v_DT_1_1_int_int_bool_8.0, " ", "v_DT_1_1_int_int_bool_6", " ", v_DT_1_1_int_int_bool_6, " ", "v_int_int_bool_11.1", " ", v_int_int_bool_11.1, " ", "v_int_int_bool_11.0", " ", v_int_int_bool_11.0, " ", "v_DT_1_1_int_int_bool_12.0", " ", v_DT_1_1_int_int_bool_12.0, " ", "v_DT_1_1_int_int_bool_12.1", " ", v_DT_1_1_int_int_bool_12.1, " ", "v_int_29", " ", v_int_29, " ", "v_int_int_bool_6.2", " ", v_int_int_bool_6.2, " ", "v_DT_1_1_int_int_bool_1", " ", v_DT_1_1_int_int_bool_1, " ", "v_int_int_bool_6.0", " ", v_int_int_bool_6.0, " ", "v_DT_1_1_int_int_bool_2", " ", v_DT_1_1_int_int_bool_2, " ", "v_int_int_bool_6.1", " ", v_int_int_bool_6.1, " ", "v_int_int_bool_2.2", " ", v_int_int_bool_2.2, " ", "v_int_int_bool_2.0", " ", v_int_int_bool_2.0, " ", "v_int_int_bool_2.1", " ", v_int_int_bool_2.1, " ", "v_int_30", " ", v_int_30, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_int_int_bool_9.1", " ", v_DT_1_1_int_int_bool_9.1, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_int_int_bool_9.0", " ", v_DT_1_1_int_int_bool_9.0, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_DT_1_1_int_int_bool_1.1", " ", v_DT_1_1_int_int_bool_1.1, " ", "v_int_int_bool_12.2", " ", v_int_int_bool_12.2, " ", "v_DT_1_1_int_int_bool_1.0", " ", v_DT_1_1_int_int_bool_1.0, " ", "v_int_int_bool_12.1", " ", v_int_int_bool_12.1, " ", "v_DT_1_1_int_int_bool_5.1", " ", v_DT_1_1_int_int_bool_5.1, " ", "v_DT_1_1_int_int_bool_5.0", " ", v_DT_1_1_int_int_bool_5.0, " ", "v_int_int_bool_12.0", " ", v_int_int_bool_12.0, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_DT_1_1_15", " ", v_DT_1_1_15, " ", "v_DT_1_1_14", " ", v_DT_1_1_14, " ", "v_DT_1_1_13", " ", v_DT_1_1_13, " ", "v_int_int_bool_1", " ", v_int_int_bool_1, " ", "v_int_int_bool_7.1", " ", v_int_int_bool_7.1, " ", "v_int_int_bool_7.2", " ", v_int_int_bool_7.2, " ", "v_int_int_bool_3", " ", v_int_int_bool_3, " ", "v_int_int_bool_2", " ", v_int_int_bool_2, " ", "v_int_int_bool_7.0", " ", v_int_int_bool_7.0, " ", "v_int_int_bool_3.1", " ", v_int_int_bool_3.1, " ", "v_int_int_bool_3.2", " ", v_int_int_bool_3.2, " ", "v_int_int_bool_3.0", " ", v_int_int_bool_3.0, " ", "v_int_int_bool_9", " ", v_int_int_bool_9, " ", "v_int_int_bool_8", " ", v_int_int_bool_8, " ", "v_int_int_bool_5", " ", v_int_int_bool_5, " ", "v_int_int_bool_4", " ", v_int_int_bool_4, " ", "v_int_int_bool_7", " ", v_int_int_bool_7, " ", "v_int_int_bool_6", " ", v_int_int_bool_6, " ", "v_DT_1_1_int_int_bool_2.0", " ", v_DT_1_1_int_int_bool_2.0, " ", "v_DT_1_1_int_int_bool_2.1", " ", v_DT_1_1_int_int_bool_2.1, " ", "v_DT_1_1_int_int_bool_6.0", " ", v_DT_1_1_int_int_bool_6.0, " ", "v_DT_1_1_int_int_bool_6.1", " ", v_DT_1_1_int_int_bool_6.1, " ", "v_DT_1_1_int_int_bool_10.0", " ", v_DT_1_1_int_int_bool_10.0, " ", "v_DT_1_1_int_int_bool_10.1", " ", v_DT_1_1_int_int_bool_10.1, " ", "v_int_int_bool_8.2", " ", v_int_int_bool_8.2, " ", "v_int_int_bool_8.0", " ", v_int_int_bool_8.0, " ", "v_int_int_bool_8.1", " ", v_int_int_bool_8.1, " ", "v_int_int_bool_4.2", " ", v_int_int_bool_4.2, " ", "v_int_int_bool_4.0", " ", v_int_int_bool_4.0, " ", "v_int_int_bool_4.1", " ", v_int_int_bool_4.1, " ", "v_DT_1_1_int_int_bool_10", " ", v_DT_1_1_int_int_bool_10, " ", "v_DT_1_1_int_int_bool_11", " ", v_DT_1_1_int_int_bool_11, " ", "v_DT_1_1_int_int_bool_12", " ", v_DT_1_1_int_int_bool_12, " ", "v_DT_1_1_int_int_bool_3.1", " ", v_DT_1_1_int_int_bool_3.1, " ", "v_int_19", " ", v_int_19, " ", "v_DT_1_1_int_int_bool_3.0", " ", v_DT_1_1_int_int_bool_3.0, " ", "v_int_18", " ", v_int_18, " ", "v_DT_1_1_int_int_bool_7.1", " ", v_DT_1_1_int_int_bool_7.1, " ", "v_DT_1_1_int_int_bool_7.0", " ", v_DT_1_1_int_int_bool_7.0, " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 14.16), " ", "v_int_22", " ", v_int_22, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_int_21", " ", v_int_21, " ", "v_int_int_bool_10.0", " ", v_int_int_bool_10.0, " ", "v_seq_10", " ", v_seq_10, " ", "v_int_28", " ", v_int_28, " ", "v_seq_11", " ", v_seq_11, " ", "v_int_27", " ", v_int_27, " ", "v_int_int_bool_10.2", " ", v_int_int_bool_10.2, " ", "v_seq_12", " ", v_seq_12, " ", "v_int_26", " ", v_int_26, " ", "v_int_int_bool_10.1", " ", v_int_int_bool_10.1, " ", "v_seq_13", " ", v_seq_13, " ", "v_int_25", " ", v_int_25, " ", "v_DT_1_1_int_int_bool_11.0", " ", v_DT_1_1_int_int_bool_11.0, " ", "v_DT_1_1_int_int_bool_11.1", " ", v_DT_1_1_int_int_bool_11.1, " ", "v_int_20", " ", v_int_20, " ", "v_int_int_bool_12", " ", v_int_int_bool_12, " ", "v_int_int_bool_11", " ", v_int_int_bool_11, " ", "v_int_int_bool_10", " ", v_int_int_bool_10, " ", "v_int_int_bool_9.1", " ", v_int_int_bool_9.1, " ", "v_int_int_bool_9.2", " ", v_int_int_bool_9.2, " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", v_seq_8, " ", "v_int_int_bool_9.0", " ", v_int_int_bool_9.0, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_int_bool_5.1", " ", v_int_int_bool_5.1, " ", "v_int_int_bool_5.2", " ", v_int_int_bool_5.2, " ", "v_int_17", " ", v_int_17, " ", "v_int_int_bool_5.0", " ", v_int_int_bool_5.0, " ", "v_int_int_bool_1.1", " ", v_int_int_bool_1.1, " ", "v_int_int_bool_1.2", " ", v_int_int_bool_1.2, " ", "v_int_int_bool_1.0", " ", v_int_int_bool_1.0, "\n";
	return (match 27 {
		case 22 => (if (true) then ('J') else ('X'))
		case _ => (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_40]) else ('k'))
	});
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_array_1: array<set<int>> := new set<int>[4] [{22, 27, 21}, {18, 24, -20, 8}, {18, 23, 6, 25}, {5, 29, 12}];
	var v_array_2: array<set<int>> := new set<int>[4] [{16, 19}, {}, {5, 12, 29}, {6, 29}];
	var v_array_3: array<set<int>> := new set<int>[3] [{24, 8, 12}, {9, 6, 11, 17}, {2, 21, 4}];
	var v_array_4: array<set<int>> := new set<int>[4] [{15, 16}, {}, {26, 4, 17, -10}, {21, 28}];
	var v_array_5: array<set<int>> := new set<int>[3] [{}, {}, {10, 9}];
	var v_array_6: array<set<int>> := new set<int>[3] [{}, {2, 10, 8}, {17, 7, 16}];
	var v_array_7: array<set<int>> := new set<int>[3] [{5}, {0}, {24, 27, 17}];
	var v_array_8: array<set<int>> := new set<int>[3] [{7, 28}, {11, 16, -22}, {10, -8, 17, 23}];
	var v_array_9: array<set<int>> := new set<int>[3] [{10}, {27, 23}, {11, 3, 5}];
	var v_array_10: array<set<int>> := new set<int>[5] [{}, {17, 1}, {1, 27, 1, 19}, {16, 12, 23, 1}, {6, 15}];
	var v_array_11: array<set<int>> := new set<int>[4] [{}, {4, 28, 3, 14}, {25, 0, 14}, {23, 0, 27}];
	var v_map_1: map<int, seq<array<set<int>>>> := map[23 := [v_array_1, v_array_2, v_array_3, v_array_4], 28 := [], 25 := [v_array_5, v_array_6, v_array_7, v_array_8], 1 := [v_array_9, v_array_10, v_array_11]];
	var v_int_7: int := -26;
	var v_array_12: array<set<int>> := new set<int>[4] [{-8, -22}, {11}, {14, 13}, {0, 2}];
	var v_array_13: array<set<int>> := new set<int>[3] [{8}, {26, 7, 28, 12}, {12, 25}];
	var v_array_14: array<set<int>> := new set<int>[4] [{15}, {10}, {12, 27}, {16, 28}];
	var v_array_15: array<set<int>> := new set<int>[3] [{2}, {11, 13, -17}, {}];
	var v_array_16: array<set<int>> := new set<int>[3] [{25, 7, 20, 20}, {26}, {}];
	var v_array_17: array<set<int>> := new set<int>[4] [{1}, {18, 13, 9}, {10, 26, 1}, {15, -5, 23, 2}];
	var v_array_18: array<set<int>> := new set<int>[4] [{19, 23, 27}, {7, 23, 20}, {14, -21, 23}, {21}];
	var v_array_19: array<set<int>> := new set<int>[5];
	v_array_19[0] := {};
	v_array_19[1] := {2};
	v_array_19[2] := {21};
	v_array_19[3] := {27};
	v_array_19[4] := {10, -16};
	var v_array_20: array<set<int>> := new set<int>[4] [{2, 25}, {21, -14, 16}, {10, 27, 15, 26}, {}];
	var v_seq_3: seq<array<set<int>>> := (match false {
		case false => []
		case _ => ([v_array_15, v_array_16, v_array_17] + [v_array_18, v_array_19, v_array_20])
	});
	var v_int_8: int := 22;
	var v_int_9: int := 2;
	var v_int_10: int := safe_division(v_int_8, v_int_9);
	var v_int_11: int := (match 28 {
		case 7 => (13 * 11)
		case 4 => v_int_10
		case _ => (if (false) then (13) else (0))
	});
	var v_seq_4: seq<array<set<int>>> := v_seq_3;
	var v_int_12: int := 2;
	var v_int_13: int := 18;
	var v_int_14: int := safe_division(v_int_12, v_int_13);
	var v_int_15: int := v_int_14;
	var v_array_21: array<set<int>> := new set<int>[3] [{}, {2, 26, 17, 24}, {18}];
	var v_array_22: array<set<int>> := new set<int>[3] [{}, {2, 21}, {-13, 25}];
	var v_array_23: array<set<int>> := new set<int>[3] [{}, {}, {8, -7}];
	var v_seq_5: seq<array<set<int>>> := [v_array_21, v_array_22, v_array_23];
	var v_int_16: int := 9;
	var v_seq_26: seq<array<set<int>>> := v_seq_5;
	var v_int_55: int := v_int_16;
	var v_int_56: int := safe_index_seq(v_seq_26, v_int_55);
	v_int_16 := v_int_56;
	var v_array_24: array<set<int>> := new set<int>[5] [{0}, {11, 21, 4, 17}, {}, {26, 27}, {}];
	var v_char_10: char := 'G';
	var v_DT_1_2_7: DT_1 := DT_1_2;
	var v_DT_1_2_8: DT_1 := v_DT_1_2_7;
	var v_char_11: char := 'O';
	var v_char_12: char := 'Y';
	var v_bool_11: bool := m_method_4(v_char_10, v_DT_1_2_8, v_char_11, v_char_12);
	var v_map_6: map<int, bool> := map[28 := false];
	var v_int_41: int := 14;
	var v_seq_19: seq<bool> := [true, true];
	var v_int_42: int := -9;
	var v_seq_21: seq<bool> := v_seq_19;
	var v_int_45: int := v_int_42;
	var v_int_46: int := safe_index_seq(v_seq_21, v_int_45);
	v_int_42 := v_int_46;
	var v_bool_12: bool := (match 12 {
		case -14 => v_bool_11
		case -16 => (if ((v_int_41 in v_map_6)) then (v_map_6[v_int_41]) else (true))
		case _ => (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_42]) else (true))
	});
	var v_int_int_int_1: (int, int, int) := (16, 1, 20);
	var v_int_int_int_2: (int, int, int) := (5, 2, 1);
	var v_int_int_int_3: (int, int, int) := (5, -4, 25);
	var v_int_int_int_4: (int, int, int) := (28, 20, 9);
	var v_map_7: map<(int, int, int), real> := map[v_int_int_int_1 := -29.28, v_int_int_int_2 := -2.99, v_int_int_int_3 := -10.68, v_int_int_int_4 := -16.12];
	var v_int_int_int_5: (int, int, int) := (2, 4, 28);
	var v_int_int_int_6: (int, int, int) := v_int_int_int_5;
	var v_real_2: real := (if ((if (true) then (true) else (true))) then ((match 7 {
		case 19 => 4.15
		case _ => 14.16
	})) else ((if ((v_int_int_int_6 in v_map_7)) then (v_map_7[v_int_int_int_6]) else (4.55))));
	var v_char_13: char := m_method_1(v_bool_12, v_real_2);
	var v_array_26: array<set<int>>, v_char_14: char := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_11]) else ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_15]) else ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_16]) else (v_array_24)))))), v_char_13;
	assert ((v_int_int_int_1.1 == 1));
	expect ((v_int_int_int_1.1 == 1));
	var v_seq_20: seq<int> := [];
	var v_int_43: int := 28;
	var v_map_8: map<int, map<char, int>> := map[19 := map['H' := 26], 16 := map['w' := 18, 'a' := 8, 'E' := 5], 13 := map['g' := 8, 'J' := 27, 'v' := 28], 28 := map['C' := 11, 'r' := 7], 23 := map['n' := 8]];
	var v_int_44: int := 17;
	var v_map_9: map<char, int> := (if ((v_int_44 in v_map_8)) then (v_map_8[v_int_44]) else (map['b' := 23]));
	var v_char_15: char := (if (false) then ('B') else ('c'));
	v_int_13, v_int_15 := v_int_15, (match 8 {
		case 3 => (match 22 {
			case _ => (5 - 4)
		})
		case 10 => ((7 % 27) * |multiset{-29, 25}|)
		case _ => (if ((v_char_15 in v_map_9)) then (v_map_9[v_char_15]) else ((27 % 21)))
	});
	var v_int_int_int_7: (int, int, int) := (28, 20, 9);
	var v_int_int_int_8: (int, int, int) := (5, -4, 25);
	var v_int_int_int_9: (int, int, int) := (16, 1, 20);
	var v_int_int_int_10: (int, int, int) := (5, 2, 1);
	print "v_array_21[2]", " ", (v_array_21[2] == {18}), " ", "v_array_24[2]", " ", (v_array_24[2] == {}), " ", "v_array_23[1]", " ", (v_array_23[1] == {}), " ", "v_int_int_int_2.1", " ", v_int_int_int_2.1, " ", "v_int_int_int_3", " ", v_int_int_int_3, " ", "v_int_int_int_2.2", " ", v_int_int_int_2.2, " ", "v_int_int_int_4", " ", v_int_int_int_4, " ", "v_int_int_int_4.0", " ", v_int_int_int_4.0, " ", "v_int_int_int_1", " ", v_int_int_int_1, " ", "v_int_int_int_4.1", " ", v_int_int_int_4.1, " ", "v_int_int_int_2", " ", v_int_int_int_2, " ", "v_int_int_int_4.2", " ", v_int_int_int_4.2, " ", "v_int_int_int_5", " ", v_int_int_int_5, " ", "v_int_int_int_2.0", " ", v_int_int_int_2.0, " ", "v_int_int_int_6", " ", v_int_int_int_6, " ", "v_array_22", " ", (v_array_22 == v_array_22), " ", "v_array_21", " ", (v_array_21 == v_array_21), " ", "v_int_int_int_5.2", " ", v_int_int_int_5.2, " ", "v_array_21[1]", " ", (v_array_21[1] == {17, 2, 24, 26}), " ", "v_array_22[2]", " ", (v_array_22[2] == {25, -13}), " ", "v_array_24[3]", " ", (v_array_24[3] == {26, 27}), " ", "v_array_23[2]", " ", (v_array_23[2] == {-7, 8}), " ", "v_real_2", " ", (v_real_2 == 14.16), " ", "v_bool_12", " ", v_bool_12, " ", "v_array_26", " ", (v_array_26 == v_array_21), " ", "v_array_24", " ", (v_array_24 == v_array_24), " ", "v_array_23", " ", (v_array_23 == v_array_23), " ", "v_char_14", " ", (v_char_14 == 'k'), " ", "v_array_21[0]", " ", (v_array_21[0] == {}), " ", "v_char_13", " ", (v_char_13 == 'k'), " ", "v_array_22[1]", " ", (v_array_22[1] == {2, 21}), " ", "v_array_24[4]", " ", (v_array_24[4] == {}), " ", "v_array_24[0]", " ", (v_array_24[0] == {0}), " ", "v_int_int_int_1.2", " ", v_int_int_int_1.2, " ", "v_int_int_int_3.0", " ", v_int_int_int_3.0, " ", "v_int_int_int_3.1", " ", v_int_int_int_3.1, " ", "v_int_int_int_3.2", " ", v_int_int_int_3.2, " ", "v_int_int_int_5.0", " ", v_int_int_int_5.0, " ", "v_int_int_int_5.1", " ", v_int_int_int_5.1, " ", "v_int_int_int_1.0", " ", v_int_int_int_1.0, " ", "v_int_int_int_1.1", " ", v_int_int_int_1.1, " ", "v_map_7", " ", (v_map_7 == map[v_int_int_int_7 := -16.12, v_int_int_int_8 := -10.68, v_int_int_int_9 := -29.28, v_int_int_int_10 := -2.99]), " ", "v_array_22[0]", " ", (v_array_22[0] == {}), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_seq_5", " ", (v_seq_5 == [v_array_21, v_array_22, v_array_23]), " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_seq_3", " ", (v_seq_3 == []), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_array_24[1]", " ", (v_array_24[1] == {17, 4, 21, 11}), " ", "v_int_14", " ", v_int_14, " ", "v_array_23[0]", " ", (v_array_23[0] == {}), "\n";
}
