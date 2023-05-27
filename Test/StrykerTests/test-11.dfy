// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1
datatype DT_2<T_1, T_2> = DT_2_1 | DT_2_2(DT_2_2_1: T_2, DT_2_2_2: T_1)
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

method m_method_5(p_m_method_5_1: char) returns (ret_1: char)
	requires ((p_m_method_5_1 == 'E')) || ((p_m_method_5_1 == 'j')) || ((p_m_method_5_1 == 'w'));
	ensures (((p_m_method_5_1 == 'w')) ==> ((ret_1 == 'U'))) && (((p_m_method_5_1 == 'E')) ==> ((ret_1 == 'U'))) && (((p_m_method_5_1 == 'j')) ==> ((ret_1 == 'U')));
{
	var v_char_7: char, v_char_8: char, v_char_9: char, v_char_10: char := 'e', 'F', 'D', 'e';
	var v_int_24: int := 17;
	var v_int_25: int := 5;
	while (v_int_24 < v_int_25) 
		decreases v_int_25 - v_int_24;
		invariant (v_int_24 <= v_int_25);
	{
		v_int_24 := (v_int_24 + 1);
		if false {
			return 'i';
		} else {
			return 'U';
		}
	}
	print "v_int_24", " ", v_int_24, " ", "v_char_7", " ", (v_char_7 == 'e'), " ", "v_int_25", " ", v_int_25, " ", "v_char_9", " ", (v_char_9 == 'D'), " ", "v_char_10", " ", (v_char_10 == 'e'), " ", "v_char_8", " ", (v_char_8 == 'F'), " ", "p_m_method_5_1", " ", (p_m_method_5_1 == 'w'), "\n";
	return 'U';
}

method m_method_4(p_m_method_4_1: char) returns (ret_1: seq<char>)
	requires ((p_m_method_4_1 == 'X')) || ((p_m_method_4_1 == 'y'));
	ensures (((p_m_method_4_1 == 'X')) ==> (|ret_1| == 1 && (ret_1[0] == 'v'))) && (((p_m_method_4_1 == 'y')) ==> (|ret_1| == 1 && (ret_1[0] == 'v')));
{
	assert ((p_m_method_4_1 == 'X')) || ((p_m_method_4_1 == 'y'));
	expect ((p_m_method_4_1 == 'X')) || ((p_m_method_4_1 == 'y'));
	var v_char_11: char := 'w';
	var v_char_12: char := m_method_5(v_char_11);
	v_char_12 := v_char_12;
	assert ((p_m_method_4_1 == 'X') && (v_char_12 == 'U') && (v_char_11 == 'w')) || ((p_m_method_4_1 == 'y') && (v_char_12 == 'U') && (v_char_11 == 'w'));
	expect ((p_m_method_4_1 == 'X') && (v_char_12 == 'U') && (v_char_11 == 'w')) || ((p_m_method_4_1 == 'y') && (v_char_12 == 'U') && (v_char_11 == 'w'));
	print "v_char_12", " ", (v_char_12 == 'U'), " ", "v_char_11", " ", (v_char_11 == 'w'), " ", "p_m_method_4_1", " ", (p_m_method_4_1 == 'X'), "\n";
	return ['v'];
}

method m_method_3(p_m_method_3_1: bool, p_m_method_3_2: map<bool, bool>, p_m_method_3_3: real) returns (ret_1: seq<(seq<bool>, int, bool)>)
	requires ((p_m_method_3_1 == true) && (-10.43 < p_m_method_3_3 < -10.23) && (p_m_method_3_2 == map[false := false, true := false]));
	ensures (((p_m_method_3_1 == true) && (-10.43 < p_m_method_3_3 < -10.23) && (p_m_method_3_2 == map[false := false, true := false])) ==> (|ret_1| == 3 && |(ret_1[0]).0| == 2 && ((ret_1[0]).0[0] == false) && ((ret_1[0]).0[1] == false) && ((ret_1[0]).1 == 9) && ((ret_1[0]).2 == false) && |(ret_1[1]).0| == 2 && ((ret_1[1]).0[0] == false) && ((ret_1[1]).0[1] == true) && ((ret_1[1]).1 == 12) && ((ret_1[1]).2 == false) && |(ret_1[2]).0| == 4 && ((ret_1[2]).0[0] == false) && ((ret_1[2]).0[1] == false) && ((ret_1[2]).0[2] == true) && ((ret_1[2]).0[3] == true) && ((ret_1[2]).1 == 8) && ((ret_1[2]).2 == true)));
{
	match 10.86 {
		case -15.67 => {
			var v_seq_int_bool_1: (seq<bool>, int, bool) := ([false], 2, false);
			return [v_seq_int_bool_1];
		}
			case 26.11 => {
			var v_seq_int_bool_2: (seq<bool>, int, bool) := ([true, false, true, false], 13, true);
			return [v_seq_int_bool_2];
		}
			case _ => {
			var v_seq_int_bool_3: (seq<bool>, int, bool) := ([false, false], 9, false);
			var v_seq_int_bool_4: (seq<bool>, int, bool) := ([false, true], 12, false);
			var v_seq_int_bool_5: (seq<bool>, int, bool) := ([false, false, true, true], 8, true);
			print "v_seq_int_bool_4", " ", v_seq_int_bool_4, " ", "v_seq_int_bool_5", " ", v_seq_int_bool_5, " ", "v_seq_int_bool_3.0", " ", v_seq_int_bool_3.0, " ", "v_seq_int_bool_3", " ", v_seq_int_bool_3, " ", "v_seq_int_bool_3.2", " ", v_seq_int_bool_3.2, " ", "v_seq_int_bool_4.1", " ", v_seq_int_bool_4.1, " ", "v_seq_int_bool_5.0", " ", v_seq_int_bool_5.0, " ", "v_seq_int_bool_3.1", " ", v_seq_int_bool_3.1, " ", "v_seq_int_bool_4.0", " ", v_seq_int_bool_4.0, " ", "v_seq_int_bool_5.2", " ", v_seq_int_bool_5.2, " ", "v_seq_int_bool_4.2", " ", v_seq_int_bool_4.2, " ", "v_seq_int_bool_5.1", " ", v_seq_int_bool_5.1, " ", "p_m_method_3_2", " ", (p_m_method_3_2 == map[false := false, true := false]), " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_3", " ", (p_m_method_3_3 == -10.33), "\n";
			return [v_seq_int_bool_3, v_seq_int_bool_4, v_seq_int_bool_5];
		}
		
	}
	
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

method m_method_2(p_m_method_2_1: char, p_m_method_2_2: char, p_m_method_2_3: bool) returns (ret_1: real)
	requires ((p_m_method_2_2 == 'V') && (p_m_method_2_1 == 'u') && (p_m_method_2_3 == false));
	ensures (((p_m_method_2_2 == 'V') && (p_m_method_2_1 == 'u') && (p_m_method_2_3 == false)) ==> ((24.69 < ret_1 < 24.89)));
{
	var v_array_1: array<char> := new char[5] ['s', 'G', 'B', 's', 'D'];
	var v_int_8: int, v_bool_1: bool, v_char_1: char, v_array_2: array<char> := 18, true, 'z', v_array_1;
	print "v_bool_1", " ", v_bool_1, " ", "v_char_1", " ", (v_char_1 == 'z'), " ", "v_int_8", " ", v_int_8, " ", "p_m_method_2_1", " ", (p_m_method_2_1 == 'u'), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[1]", " ", (v_array_1[1] == 'G'), " ", "v_array_1[2]", " ", (v_array_1[2] == 'B'), " ", "v_array_1[0]", " ", (v_array_1[0] == 's'), " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'V'), " ", "v_array_1[3]", " ", (v_array_1[3] == 's'), " ", "v_array_1[4]", " ", (v_array_1[4] == 'D'), "\n";
	return 24.79;
}

method m_method_1(p_m_method_1_1: DT_1) returns (ret_1: bool)
	requires ((p_m_method_1_1.DT_1_1? && ((p_m_method_1_1 == DT_1_1))));
	ensures (((p_m_method_1_1.DT_1_1? && ((p_m_method_1_1 == DT_1_1)))) ==> ((ret_1 == false)));
{
	var v_char_2: char := 'u';
	var v_char_3: char := 'V';
	var v_bool_2: bool := false;
	var v_real_1: real := m_method_2(v_char_2, v_char_3, v_bool_2);
	var v_seq_3: seq<seq<int>> := [[3], [0, 23], [14, 15], [0, 14]];
	var v_int_9: int := -21;
	var v_seq_19: seq<seq<int>> := v_seq_3;
	var v_int_36: int := v_int_9;
	var v_int_37: int := safe_index_seq(v_seq_19, v_int_36);
	v_int_9 := v_int_37;
	var v_seq_5: seq<int> := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_9]) else ([]));
	var v_seq_4: seq<int> := [26, 26, 17];
	var v_int_10: int := 26;
	var v_seq_20: seq<int> := v_seq_4;
	var v_int_38: int := v_int_10;
	var v_int_39: int := safe_index_seq(v_seq_20, v_int_38);
	v_int_10 := v_int_39;
	var v_int_11: int := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_10]) else (19));
	var v_seq_21: seq<int> := v_seq_5;
	var v_int_40: int := v_int_11;
	var v_int_41: int := safe_index_seq(v_seq_21, v_int_40);
	v_int_11 := v_int_41;
	var v_int_18: int, v_int_19: int := (v_real_1).Floor, (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_11]) else ((20 % 24)));
	for v_int_7 := v_int_18 downto v_int_19 
		invariant (v_int_7 - v_int_19 >= 0)
	{
		var v_seq_6: seq<map<multiset<bool>, int>> := [map[multiset{true} := 2], map[multiset{false} := 18, multiset{false, true} := 13, multiset({true}) := 24, multiset{true, false, false} := 9]];
		var v_int_12: int := 3;
		var v_seq_22: seq<map<multiset<bool>, int>> := v_seq_6;
		var v_int_42: int := v_int_12;
		var v_int_43: int := safe_index_seq(v_seq_22, v_int_42);
		v_int_12 := v_int_43;
		var v_seq_7: seq<multiset<bool>> := [];
		var v_int_13: int := -9;
		var v_bool_3: bool := true;
		var v_map_1: map<bool, bool> := map[true := false, false := false];
		var v_real_2: real := -10.33;
		var v_seq_8: seq<(seq<bool>, int, bool)> := m_method_3(v_bool_3, v_map_1, v_real_2);
		var v_seq_9: seq<(seq<bool>, int, bool)> := v_seq_8;
		var v_int_14: int := v_int_12;
		var v_seq_23: seq<(seq<bool>, int, bool)> := v_seq_9;
		var v_int_44: int := v_int_14;
		var v_int_45: int := safe_index_seq(v_seq_23, v_int_44);
		v_int_14 := v_int_45;
		var v_seq_int_bool_6: (seq<bool>, int, bool) := ([false, true], 17, false);
		var v_map_2: map<set<map<bool, bool>>, (seq<bool>, int, bool)> := map[{map[true := true, false := true]} := v_seq_int_bool_6];
		var v_set_1: set<map<bool, bool>> := {map[true := false, false := true], map[false := false], map[false := true], map[false := false]};
		var v_seq_int_bool_7: (seq<bool>, int, bool) := ([true, false], 18, true);
		var v_int_15: int := 24;
		var v_int_16: int := 10;
		var v_int_17: int := safe_division(v_int_15, v_int_16);
		var v_char_4: char, v_map_3: map<multiset<bool>, int>, v_seq_int_bool_8: (seq<bool>, int, bool), v_bool_4: bool, v_bool_5: bool := v_char_2, (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_12]) else (map[multiset{true, false} := 5, multiset({true, false, true}) := 25]))[(if ((|v_seq_7| > 0)) then (v_seq_7[v_int_13]) else (multiset({}))) := v_int_10], (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_14]) else ((if ((v_set_1 in v_map_2)) then (v_map_2[v_set_1]) else (v_seq_int_bool_7)))), (({'n', 'L'} * {'g'}) !! ({} - {})), (v_seq_int_bool_7.1 != v_int_17);
		match v_char_2 {
			case 'w' => {
				continue;
			}
				case _ => {
				var v_seq_int_bool_9: (seq<bool>, int, bool) := ([false, true], 17, false);
				print "v_bool_3", " ", v_bool_3, " ", "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_char_4", " ", (v_char_4 == 'u'), " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[false := false, true := false]), " ", "v_map_3", " ", (v_map_3 == map[multiset{} := 0, multiset{true} := 2]), " ", "v_seq_9", " ", v_seq_9, " ", "v_map_2", " ", (v_map_2 == map[{map[false := true, true := true]} := v_seq_int_bool_9]), " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", v_seq_8, " ", "v_int_12", " ", v_int_12, " ", "v_seq_7", " ", (v_seq_7 == []), " ", "v_seq_6", " ", (v_seq_6 == [map[multiset{true} := 2], map[multiset{false, true} := 13, multiset{false} := 18, multiset{false, false, true} := 9, multiset{true} := 24]]), " ", "v_seq_int_bool_8", " ", v_seq_int_bool_8, " ", "v_seq_int_bool_6", " ", v_seq_int_bool_6, " ", "v_set_1", " ", (v_set_1 == {map[false := false], map[false := true, true := false], map[false := true]}), " ", "v_int_17", " ", v_int_17, " ", "v_seq_int_bool_7", " ", v_seq_int_bool_7, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_real_2", " ", (v_real_2 == -10.33), " ", "v_seq_int_bool_6.1", " ", v_seq_int_bool_6.1, " ", "v_seq_int_bool_7.0", " ", v_seq_int_bool_7.0, " ", "v_seq_int_bool_6.0", " ", v_seq_int_bool_6.0, " ", "v_seq_int_bool_7.2", " ", v_seq_int_bool_7.2, " ", "v_seq_int_bool_6.2", " ", v_seq_int_bool_6.2, " ", "v_seq_int_bool_7.1", " ", v_seq_int_bool_7.1, " ", "v_char_3", " ", (v_char_3 == 'V'), " ", "v_int_11", " ", v_int_11, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_char_2", " ", (v_char_2 == 'u'), " ", "v_bool_2", " ", v_bool_2, " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_real_1", " ", (v_real_1 == 24.79), "\n";
				return v_bool_2;
			}
			
		}
		
	}
	return v_bool_2;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_seq_10: seq<DT_1> := [v_DT_1_1_1];
	var v_seq_11: seq<DT_1> := v_seq_10;
	var v_int_20: int := 14;
	var v_int_21: int := safe_index_seq(v_seq_11, v_int_20);
	var v_int_22: int := v_int_21;
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_seq_12: seq<DT_1> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_22 := v_DT_1_1_2]) else (v_seq_10));
	var v_int_23: int := v_int_20;
	var v_seq_18: seq<DT_1> := v_seq_12;
	var v_int_34: int := v_int_23;
	var v_int_35: int := safe_index_seq(v_seq_18, v_int_34);
	v_int_23 := v_int_35;
	var v_DT_1_1_3: DT_1 := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_23]) else (v_DT_1_1_2));
	var v_bool_6: bool := m_method_1(v_DT_1_1_3);
	var v_map_4: map<char, char> := map['z' := 'q', 'j' := 'x', 'Z' := 'C'];
	var v_char_5: char := 'U';
	var v_map_5: map<char, char> := map['V' := 'E', 'e' := 'L', 'E' := 'e', 'Y' := 'z', 'R' := 'O'];
	var v_char_6: char := 'n';
	var v_char_13: char := 'X';
	var v_seq_13: seq<char> := m_method_4(v_char_13);
	var v_seq_14: seq<char> := v_seq_13;
	var v_int_26: int := (if (false) then (16) else (1));
	var v_seq_25: seq<char> := v_seq_14;
	var v_int_48: int := v_int_26;
	var v_int_49: int := safe_index_seq(v_seq_25, v_int_48);
	v_int_26 := v_int_49;
	var v_map_6: map<char, map<char, char>> := map['d' := map['f' := 's', 'N' := 'R'], 'h' := map['l' := 'D'], 'v' := map['H' := 'S']];
	var v_char_14: char := 'G';
	var v_map_7: map<char, char> := ((if ((v_char_14 in v_map_6)) then (v_map_6[v_char_14]) else (map['U' := 'E', 'p' := 'T'])) - (if (false) then ({'z', 'f', 'n'}) else ({'V', 'j'})));
	var v_seq_15: seq<char> := (['S', 'Z'] + ['P', 'f']);
	var v_int_27: int := (26 + 3);
	var v_seq_24: seq<char> := v_seq_15;
	var v_int_46: int := v_int_27;
	var v_int_47: int := safe_index_seq(v_seq_24, v_int_46);
	v_int_27 := v_int_47;
	var v_char_15: char := 'j';
	var v_char_16: char := m_method_5(v_char_15);
	var v_char_19: char := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_27]) else (v_char_16));
	var v_char_17: char := (if (false) then ('m') else ('E'));
	var v_char_18: char := m_method_5(v_char_17);
	var v_bool_7: bool, v_char_20: char, v_bool_8: bool, v_char_21: char := v_bool_6, (match 24 {
		case -8 => (match 'R' {
			case _ => (if ((v_char_6 in v_map_5)) then (v_map_5[v_char_6]) else ('G'))
		})
		case _ => (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_26]) else ((if (true) then ('d') else ('D'))))
	}), v_bool_6, (if ((v_char_19 in v_map_7)) then (v_map_7[v_char_19]) else (v_char_18));
	var v_map_9: map<bool, int> := map[false := -25, true := 4][false := 28];
	var v_map_8: map<int, bool> := map[12 := true, 3 := false];
	var v_int_29: int := 29;
	var v_bool_9: bool := (if ((v_int_29 in v_map_8)) then (v_map_8[v_int_29]) else (false));
	var v_char_22: char := 'y';
	var v_seq_16: seq<char> := m_method_4(v_char_22);
	var v_seq_17: seq<char> := v_seq_16;
	var v_int_30: int := (23 % 4);
	var v_int_31: int := safe_index_seq(v_seq_17, v_int_30);
	var v_int_32: int, v_int_33: int := v_int_21, (if (v_bool_6) then ((if ((v_bool_9 in v_map_9)) then (v_map_9[v_bool_9]) else ((if (false) then (16) else (23))))) else (v_int_31));
	for v_int_28 := v_int_32 downto v_int_33 
		invariant (v_int_28 - v_int_33 >= 0)
	{
		return ;
	}
	print "v_char_18", " ", (v_char_18 == 'U'), " ", "v_char_17", " ", (v_char_17 == 'E'), " ", "v_char_16", " ", (v_char_16 == 'U'), " ", "v_char_15", " ", (v_char_15 == 'j'), " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_char_14", " ", (v_char_14 == 'G'), " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_bool_7", " ", v_bool_7, " ", "v_bool_6", " ", v_bool_6, " ", "v_char_19", " ", (v_char_19 == 'S'), " ", "v_int_23", " ", v_int_23, " ", "v_seq_15", " ", (v_seq_15 == ['S', 'Z', 'P', 'f']), " ", "v_int_22", " ", v_int_22, " ", "v_seq_16", " ", (v_seq_16 == ['v']), " ", "v_int_21", " ", v_int_21, " ", "v_seq_17", " ", (v_seq_17 == ['v']), " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", v_seq_11, " ", "v_int_27", " ", v_int_27, " ", "v_seq_12", " ", v_seq_12, " ", "v_char_21", " ", (v_char_21 == 'U'), " ", "v_char_20", " ", (v_char_20 == 'v'), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_int_20", " ", v_int_20, " ", "v_map_7", " ", (v_map_7 == map['p' := 'T', 'U' := 'E']), " ", "v_map_6", " ", (v_map_6 == map['d' := map['f' := 's', 'N' := 'R'], 'v' := map['H' := 'S'], 'h' := map['l' := 'D']]), " ", "v_map_9", " ", (v_map_9 == map[false := 28, true := 4]), " ", "v_map_8", " ", (v_map_8 == map[3 := false, 12 := true]), " ", "v_char_22", " ", (v_char_22 == 'y'), " ", "v_int_29", " ", v_int_29, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, "\n";
	return ;
}
