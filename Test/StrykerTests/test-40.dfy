// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_2
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

method m_method_4(p_m_method_4_1: char) returns (ret_1: char)
{
	return 'x';
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char, p_m_method_3_4: char) returns (ret_1: char)
{
	return 'y';
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

method m_method_2(p_m_method_2_1: int) returns (ret_1: char)
{
	var v_seq_9: seq<int> := (if (true) then ([10, 8, -11]) else ([]));
	var v_map_7: map<int, int> := map[24 := 24];
	var v_int_35: int := 12;
	var v_int_36: int := (if ((v_int_35 in v_map_7)) then (v_map_7[v_int_35]) else (25));
	var v_array_3: array<int> := new int[5] [20, 27, 4, 4, 29];
	var v_int_38: int := (18 / -20);
	var v_map_8: map<int, int> := map[6 := -20, 5 := 2, -10 := 12, 23 := 1, 8 := 3];
	var v_int_37: int := 0;
	var v_int_39: int := (if ((v_int_37 in v_map_8)) then (v_map_8[v_int_37]) else (5));
	var v_int_40: int := safe_modulus(v_int_38, v_int_39);
	v_int_37, v_array_3[1], v_int_40, v_int_39 := (match 24 {
		case _ => (match 21 {
			case _ => 9
		})
	}), (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_36]) else (v_array_3.Length)), v_array_3[3], v_int_40;
	var v_char_1: char := 'L';
	var v_char_2: char := 'v';
	var v_char_3: char := 'X';
	var v_char_4: char := 'K';
	var v_char_5: char := m_method_3(v_char_1, v_char_2, v_char_3, v_char_4);
	var v_char_6: char := 'z';
	var v_char_7: char := m_method_4(v_char_6);
	return (match 'C' {
		case _ => v_char_7
	});
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: int, p_m_method_1_3: int, p_m_method_1_4: int) returns (ret_1: real)
{
	var v_int_27: int := (match 1 {
		case _ => 0
	});
	match (if (true) then (9) else (6)) {
		case _ => {
			var v_seq_8: seq<real> := [24.95, 8.58];
			var v_int_28: int := 11;
			return (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_28]) else (17.60));
		}
		
	}
	
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_3: seq<DT_1<int, int>> := [];
	var v_int_9: int := 25;
	var v_int_10: int := safe_index_seq(v_seq_3, v_int_9);
	var v_int_7: int := ((if (false) then (29) else (v_int_10)) - |(multiset{} - multiset{true, true, true, true})|);
	var v_int_8: int := -29;
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		var v_bool_bool_int_1: (bool, bool, int) := (true, true, -15);
		var v_bool_bool_int_2: (bool, bool, int) := (false, true, 22);
		var v_bool_bool_int_3: (bool, bool, int) := (false, true, 22);
		var v_bool_bool_int_4: (bool, bool, int) := (true, false, 10);
		var v_bool_bool_int_5: (bool, bool, int) := (false, true, 17);
		var v_seq_4: seq<set<(bool, bool, int)>> := [{v_bool_bool_int_1}, {v_bool_bool_int_2, v_bool_bool_int_3, v_bool_bool_int_4, v_bool_bool_int_5}];
		var v_int_11: int := 9;
		var v_bool_bool_int_6: (bool, bool, int) := (true, false, 2);
		var v_bool_bool_int_7: (bool, bool, int) := (true, true, 0);
		var v_bool_bool_int_8: (bool, bool, int) := (false, true, 13);
		var v_bool_bool_int_9: (bool, bool, int) := (true, false, 12);
		var v_bool_int_int_1: (bool, int, int) := (false, 20, 26);
		var v_bool_bool_int_10: (bool, bool, int) := (true, true, 23);
		var v_bool_int_int_2: (bool, int, int) := (true, 6, 10);
		var v_bool_bool_int_11: (bool, bool, int) := (true, true, 7);
		var v_bool_int_int_3: (bool, int, int) := (false, 28, 12);
		var v_bool_bool_int_12: (bool, bool, int) := (true, false, 0);
		var v_bool_bool_int_13: (bool, bool, int) := (false, false, 17);
		var v_bool_bool_int_14: (bool, bool, int) := (false, false, 20);
		var v_bool_bool_int_15: (bool, bool, int) := (false, false, 7);
		var v_bool_bool_int_16: (bool, bool, int) := (true, true, 13);
		var v_bool_bool_int_17: (bool, bool, int) := (true, false, 18);
		var v_set_1: set<(bool, bool, int)> := (((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_11]) else ({v_bool_bool_int_6, v_bool_bool_int_7, v_bool_bool_int_8})) + (map[v_bool_bool_int_9 := v_bool_int_int_1, v_bool_bool_int_10 := v_bool_int_int_2, v_bool_bool_int_11 := v_bool_int_int_3]).Keys) + (map[v_bool_bool_int_12 := 9, v_bool_bool_int_13 := 5, v_bool_bool_int_14 := 24, v_bool_bool_int_15 := 21, v_bool_bool_int_16 := 2][v_bool_bool_int_17 := 11]).Keys);
		if v_bool_bool_int_7.0 {
			var v_int_16: int := |(if (true) then ({25}) else ({5}))|;
			var v_int_13: int := 13;
			var v_int_14: int := -2;
			var v_int_15: int := safe_modulus(v_int_13, v_int_14);
			var v_int_17: int := (if (v_bool_bool_int_3.1) then ((if (false) then (8) else (4))) else (v_int_15));
			var v_int_18: int := safe_division(v_int_16, v_int_17);
			var v_int_19: int, v_int_20: int := v_bool_int_int_1.2, v_int_18;
			for v_int_12 := v_int_19 to v_int_20 
				invariant (v_int_20 - v_int_12 >= 0)
			{
				
			}
			return ;
		} else {
			var v_DT_1_1_1: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_2: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_3: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_4: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_5: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_6: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_7: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_8: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_9: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_10: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_11: DT_1<char, char> := DT_1_1;
			var v_map_1: map<int, map<DT_1<char, char>, set<int>>> := map[28 := map[v_DT_1_1_1 := {}], 18 := map[v_DT_1_1_2 := {9}, v_DT_1_1_3 := {18, 21, 16}, v_DT_1_1_4 := {20, 17}], 29 := map[v_DT_1_1_5 := {1, 17}, v_DT_1_1_6 := {2, 26, 11}], 2 := map[v_DT_1_1_7 := {-4, 18, 16, 6}, v_DT_1_1_8 := {}], -9 := map[v_DT_1_1_9 := {15, 9, 21, 26}, v_DT_1_1_10 := {20}, v_DT_1_1_11 := {13, 21, -3}]];
			var v_int_21: int := 21;
			var v_DT_1_1_12: DT_1<char, char> := DT_1_1;
			var v_map_3: map<DT_1<char, char>, set<int>> := (if ((v_int_21 in v_map_1)) then (v_map_1[v_int_21]) else (map[v_DT_1_1_12 := {10, 11}]));
			var v_DT_1_1_13: DT_1<char, char> := DT_1_1;
			var v_map_2: map<int, DT_1<char, char>> := map[22 := v_DT_1_1_13];
			var v_int_22: int := 10;
			var v_DT_1_1_14: DT_1<char, char> := DT_1_1;
			var v_DT_1_1_15: DT_1<char, char> := (if ((v_int_22 in v_map_2)) then (v_map_2[v_int_22]) else (v_DT_1_1_14));
			var v_seq_5: seq<set<int>> := ([{3}, {3, 16, 13, 21}] + [{25, 8}, {8, 0, 12, 24}, {16}]);
			var v_int_23: int := (26.62).Floor;
			var v_map_4: map<int, set<int>> := map[29 := {25, 15}, 0 := {24, 10}, 17 := {13, 29, 6, -27}, 18 := {15, 4, 3}];
			var v_int_24: int := 1;
			var v_seq_6: seq<map<int, real>> := [map[0 := -2.93, 25 := -18.42, 1 := 28.21, 17 := -13.31], map[19 := 2.07, 28 := -21.03, 16 := -1.97, 23 := -2.65]];
			var v_int_25: int := 26;
			var v_seq_7: seq<set<int>> := [{}, {23, 28}];
			var v_int_26: int := 19;
			var v_map_6: map<int, real> := ((if ((|v_seq_6| > 0)) then (v_seq_6[v_int_25]) else (map[24 := -0.12, 26 := -20.37, -29 := 13.25, 27 := 25.19, 16 := 11.27])) - (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_26]) else ({17, 14, 15, 24})));
			var v_int_34: int := v_bool_bool_int_14.2;
			var v_int_30: int := (-2 - 9);
			var v_array_1: array<int> := new int[5] [3, 4, 7, 12, 8];
			var v_int_31: int := v_array_1.Length;
			var v_array_2: array<int> := new int[5] [18, 8, 7, 5, 18];
			var v_int_32: int := v_array_2.Length;
			var v_map_5: map<int, int> := map[29 := 6];
			var v_int_29: int := 21;
			var v_int_33: int := (if ((v_int_29 in v_map_5)) then (v_map_5[v_int_29]) else (10));
			var v_real_1: real := m_method_1(v_int_30, v_int_31, v_int_32, v_int_33);
			var v_map_10: map<char, int> := (map['D' := 8] + map['F' := 3, 'l' := 17]);
			var v_map_9: map<char, char> := map['H' := 'X', 'F' := 'u', 's' := 'i'];
			var v_char_8: char := 'f';
			var v_char_9: char := (if ((v_char_8 in v_map_9)) then (v_map_9[v_char_8]) else ('e'));
			var v_int_41: int := 23;
			var v_int_42: int := 3;
			var v_int_43: int := safe_modulus(v_int_41, v_int_42);
			var v_int_44: int := (if ((v_char_9 in v_map_10)) then (v_map_10[v_char_9]) else (v_int_43));
			var v_char_10: char := m_method_2(v_int_44);
			var v_multiset_1: multiset<bool>, v_set_2: set<int>, v_real_2: real, v_char_11: char, v_int_45: int := (((multiset{true, true} + multiset{true, false}) - (multiset{true, false} - multiset{false, true})) + ((if (true) then (multiset{}) else (multiset{true, true, false, true})) + (multiset({true, true}) * multiset{false, true, false}))), ((if ((v_DT_1_1_15 in v_map_3)) then (v_map_3[v_DT_1_1_15]) else ((match 'Z' {
				case _ => {16}
			}))) + (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_23]) else ((if ((v_int_24 in v_map_4)) then (v_map_4[v_int_24]) else ({}))))), (if ((v_int_34 in v_map_6)) then (v_map_6[v_int_34]) else (v_real_1)), v_char_10, v_array_2[4];
			var v_int_46: int := (if (v_bool_bool_int_5.1) then (v_bool_bool_int_1.2) else ((if (false) then (23) else (5))));
			var v_char_12: char := m_method_2(v_int_46);
			v_char_11, v_char_9 := v_char_11, v_char_12;
			var v_map_11: map<char, seq<char>> := map['k' := ['m', 'L', 'd'], 'D' := [], 'q' := ['J', 'T', 'd', 'H'], 'i' := []];
			var v_char_13: char := 'm';
			var v_seq_11: seq<char> := (match 'h' {
				case _ => (if ((v_char_13 in v_map_11)) then (v_map_11[v_char_13]) else (['a', 'h']))
			});
			var v_seq_10: seq<int> := [7];
			var v_int_47: int := 8;
			var v_int_48: int := ((if ((|v_seq_10| > 0)) then (v_seq_10[v_int_47]) else (29)) / v_int_10);
			var v_map_12: map<char, char> := map['B' := 'n'];
			var v_char_14: char := 'm';
			var v_map_13: map<char, char> := map['L' := 'O']['E' := 'n'][(match 't' {
				case _ => 'i'
			}) := (if ((v_char_14 in v_map_12)) then (v_map_12[v_char_14]) else ('T'))];
			var v_char_15: char := v_char_11;
			var v_seq_12: seq<char> := v_seq_11;
			var v_map_14: map<char, int> := map['i' := 16];
			var v_char_16: char := 'K';
			var v_int_49: int := (if ((v_char_16 in v_map_14)) then (v_map_14[v_char_16]) else (28));
			var v_seq_13: seq<char> := ['a'];
			var v_int_50: int := 25;
			v_char_11, v_char_14, v_char_8, v_char_9 := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_48]) else (v_char_11)), (if ((v_char_15 in v_map_13)) then (v_map_13[v_char_15]) else (v_char_11)), (match 'M' {
				case _ => (if ((if (false) then (false) else (false))) then (v_char_10) else ((if (false) then ('u') else ('Z'))))
			}), (match 'n' {
				case _ => (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_49]) else ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_50]) else ('G'))))
			});
		}
		var v_seq_14: seq<char> := ['E', 'a', 'k'];
		var v_int_51: int := 7;
		var v_map_15: map<char, char> := map['t' := 'b', 'R' := 'b', 'N' := 'k', 'D' := 'z', 'j' := 'J'];
		var v_char_17: char := 'Y';
		var v_map_17: map<char, char> := (match 'C' {
			case _ => map['k' := 'n', 'd' := 'r', 'c' := 't', 'J' := 'Z']
		})[(if ((|v_seq_14| > 0)) then (v_seq_14[v_int_51]) else ('R')) := (if ((v_char_17 in v_map_15)) then (v_map_15[v_char_17]) else ('O'))];
		var v_seq_15: seq<char> := v_seq_14;
		var v_int_52: int := v_bool_bool_int_15.2;
		var v_char_19: char := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_52]) else ((match 'h' {
			case _ => 'N'
		})));
		var v_map_16: map<char, char> := (map['p' := 'A', 'y' := 'd', 'L' := 'D', 'x' := 'y', 'b' := 'V'] - {'l', 'V', 'J', 'm'});
		var v_char_18: char := (if (false) then ('i') else ('J'));
		var v_seq_16: seq<map<char, char>> := [map['K' := 'P', 'l' := 'I', 'p' := 'l', 't' := 'P', 'z' := 'w'], map['m' := 'r', 'k' := 'H']];
		var v_seq_17: seq<map<char, char>> := (if ((|v_seq_16| > 0)) then (v_seq_16[19..0]) else (v_seq_16));
		var v_map_18: map<char, int> := map['A' := -29, 't' := 11];
		var v_char_20: char := 'b';
		var v_int_53: int := (if ((v_char_20 in v_map_18)) then (v_map_18[v_char_20]) else (10));
		var v_map_20: map<char, char> := (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_53]) else (map['G' := 'x', 'l' := 't', 'F' := 'f', 'M' := 'p']['g' := 'F']));
		var v_seq_18: seq<char> := ['q', 'w', 'B', 'I'];
		var v_int_54: int := 6;
		var v_char_22: char := (match 'o' {
			case _ => (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_54]) else ('n'))
		});
		var v_seq_19: seq<char> := (match 'O' {
			case _ => ['r', 'l']
		});
		var v_int_55: int := (if (true) then (14) else (4));
		var v_map_19: map<char, char> := map['N' := 'w', 'M' := 'o', 'z' := 'S', 's' := 'V'];
		var v_char_21: char := 'P';
		v_char_19, v_char_22 := (if ((v_char_19 in v_map_17)) then (v_map_17[v_char_19]) else ((if ((v_char_18 in v_map_16)) then (v_map_16[v_char_18]) else ((match 'W' {
			case _ => 'y'
		}))))), (if ((v_char_22 in v_map_20)) then (v_map_20[v_char_22]) else ((if ((|v_seq_19| > 0)) then (v_seq_19[v_int_55]) else ((if ((v_char_21 in v_map_19)) then (v_map_19[v_char_21]) else ('J'))))));
		return ;
	}
	print "v_int_10", " ", v_int_10, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, "\n";
}
