// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
datatype DT_2<T_2, T_3> = DT_2_1 | DT_2_4(DT_2_4_1: T_3, DT_2_4_2: T_3)
datatype DT_3<T_4> = DT_3_1
datatype DT_4<T_5, T_6> = DT_4_1
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

method m_method_8(p_m_method_8_1: seq<int>, p_m_method_8_2: bool, p_m_method_8_3: int) returns (ret_1: map<int, seq<int>>)
{
	var v_char_4: char, v_seq_14: seq<seq<int>>, v_char_5: char := (match false {
		case _ => 'v'
	}), (match true {
		case _ => []
	}), (match false {
		case _ => 'X'
	});
	return (if (true) then (map[-12 := [15, 4]]) else (map[-4 := [27, 20, 2], 2 := [18, 4, 1, 28], 24 := [2], 2 := [18, 10, 10]]));
}

method m_method_7(p_m_method_7_1: int, p_m_method_7_2: int, p_m_method_7_3: int, p_m_method_7_4: int) returns (ret_1: bool)
{
	var v_int_24: int, v_int_25: int := 25, 26;
	for v_int_23 := v_int_24 to v_int_25 
		invariant (v_int_25 - v_int_23 >= 0)
	{
		match 19 {
			case _ => {
				return false;
			}
			
		}
		
	}
	var v_int_26: int, v_int_27: int, v_int_28: int, v_int_29: int, v_bool_14: bool := 21, 10, -22, 2, false;
	var v_int_31: int, v_int_32: int := 23, 6;
	for v_int_30 := v_int_31 to v_int_32 
		invariant (v_int_32 - v_int_30 >= 0)
	{
		return false;
	}
	return false;
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: int) returns (ret_1: bool, ret_2: bool, ret_3: int, ret_4: int)
{
	assert true;
	expect true;
	if false {
		return true, true, 13, 8;
	} else {
		return false, false, -10, 20;
	}
}

method m_method_5(p_m_method_5_1: bool, p_m_method_5_2: bool, p_m_method_5_3: bool) returns (ret_1: char)
{
	var v_int_20: int := 6;
	var v_bool_9: bool, v_bool_10: bool, v_int_21: int, v_int_22: int := m_method_6(v_int_20);
	v_bool_10, v_bool_9, v_int_22, v_int_21 := v_bool_9, v_bool_10, v_int_21, v_int_22;
	assert true;
	expect true;
	return 'c';
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool) returns (ret_1: seq<DT_1<int>>)
{
	var v_DT_1_1_8: DT_1<int> := DT_1_1;
	var v_DT_1_1_9: DT_1<int> := DT_1_1;
	var v_DT_1_1_10: DT_1<int> := DT_1_1;
	return [v_DT_1_1_8, v_DT_1_1_9, v_DT_1_1_10];
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: bool, p_m_method_3_3: bool, p_m_method_3_4: bool) returns (ret_1: map<int, int>)
{
	return map[7 := 9, 7 := 2, 29 := 28, 9 := 24, -16 := 23];
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

method m_method_2(p_m_method_2_1: DT_2<int, real>, p_m_method_2_2: (real, int, int)) returns (ret_1: int)
	requires ((8.78 < (p_m_method_2_2).0 < 8.98) && ((p_m_method_2_2).1 == 17) && ((p_m_method_2_2).2 == 14) && (p_m_method_2_1.DT_2_1? && ((p_m_method_2_1 == DT_2_1))));
	ensures (((8.78 < (p_m_method_2_2).0 < 8.98) && ((p_m_method_2_2).1 == 17) && ((p_m_method_2_2).2 == 14) && (p_m_method_2_1.DT_2_1? && ((p_m_method_2_1 == DT_2_1)))) ==> ((ret_1 == -14)));
{
	var v_int_10: int := 24;
	var v_int_11: int := 29;
	while (v_int_10 < v_int_11) 
		decreases v_int_11 - v_int_10;
		invariant (v_int_10 <= v_int_11);
	{
		v_int_10 := (v_int_10 + 1);
		var v_DT_2_4_1: DT_2<char, int> := DT_2_4(0, 13);
		var v_DT_3_1_1: DT_3<array<int>> := DT_3_1;
		var v_DT_2_4_2: DT_2<char, int>, v_DT_3_1_2: DT_3<array<int>>, v_bool_2: bool := v_DT_2_4_1, v_DT_3_1_1, false;
		var v_DT_3_1_3: DT_3<array<int>> := DT_3_1;
		assert ((v_DT_3_1_2 == v_DT_3_1_3));
		expect ((v_DT_3_1_2 == v_DT_3_1_3));
		var v_real_int_int_5: (real, int, int) := (8.88, 17, 14);
		print "v_DT_2_4_1", " ", v_DT_2_4_1, " ", "v_DT_3_1_1", " ", v_DT_3_1_1, " ", "v_DT_2_4_1.DT_2_4_2", " ", v_DT_2_4_1.DT_2_4_2, " ", "v_DT_2_4_1.DT_2_4_1", " ", v_DT_2_4_1.DT_2_4_1, " ", "v_DT_3_1_2", " ", v_DT_3_1_2, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_2_4_2", " ", v_DT_2_4_2, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_2.0", " ", (p_m_method_2_2.0 == 8.88), " ", "v_int_11", " ", v_int_11, " ", "p_m_method_2_2.1", " ", p_m_method_2_2.1, " ", "v_int_10", " ", v_int_10, " ", "p_m_method_2_2.2", " ", p_m_method_2_2.2, " ", "p_m_method_2_2", " ", (p_m_method_2_2 == v_real_int_int_5), "\n";
		return -14;
	}
	return 14;
}

method m_method_1(p_m_method_1_1: bool) returns (ret_1: seq<bool>)
	requires ((p_m_method_1_1 == false));
	ensures (((p_m_method_1_1 == false)) ==> (|ret_1| == 2 && (ret_1[0] == true) && (ret_1[1] == false)));
{
	assert ((p_m_method_1_1 == false));
	expect ((p_m_method_1_1 == false));
	print "p_m_method_1_1", " ", p_m_method_1_1, "\n";
	return [true, false];
}

method Main() returns ()
{
	var v_DT_1_1_1: DT_1<int> := DT_1_1;
	var v_DT_1_1_2: DT_1<int> := DT_1_1;
	var v_DT_1_1_3: DT_1<int> := DT_1_1;
	var v_DT_1_1_4: DT_1<int> := DT_1_1;
	var v_DT_1_1_5: DT_1<int> := DT_1_1;
	var v_map_1: map<DT_1<int>, seq<set<int>>> := map[v_DT_1_1_1 := [{14, 2}, {}, {1, 13, 7, 8}]];
	var v_DT_1_1_6: DT_1<int> := DT_1_1;
	var v_DT_1_1_7: DT_1<int> := v_DT_1_1_6;
	var v_seq_3: seq<set<int>> := (if ((v_DT_1_1_7 in v_map_1)) then (v_map_1[v_DT_1_1_7]) else ([{}, {25, 0, 4, 25}, {-9, 9, -26, 2}, {7, -22}]));
	var v_int_8: int := (11.78).Floor;
	var v_seq_20: seq<set<int>> := v_seq_3;
	var v_int_58: int := v_int_8;
	var v_int_59: int := safe_index_seq(v_seq_20, v_int_58);
	v_int_8 := v_int_59;
	var v_int_56: int, v_int_57: int := |(if ((|v_seq_3| > 0)) then (v_seq_3[v_int_8]) else (({21} * {})))|, v_int_8;
	for v_int_7 := v_int_56 downto v_int_57 
		invariant (v_int_7 - v_int_57 >= 0) && ((((v_int_7 == 1)) ==> ((((v_DT_1_1_7.DT_1_1? && ((v_DT_1_1_7 == DT_1_1))))))) && (((v_int_7 == 0)) ==> ((((v_DT_1_1_7.DT_1_1? && ((v_DT_1_1_7 == DT_1_1))))))))
	{
		var v_bool_1: bool := false;
		var v_seq_4: seq<bool> := m_method_1(v_bool_1);
		var v_seq_5: seq<bool> := v_seq_4;
		var v_int_9: int := (match 'Y' {
			case 'u' => 25
			case 'D' => 7
			case _ => 23
		});
		var v_seq_21: seq<bool> := v_seq_5;
		var v_int_60: int := v_int_9;
		var v_int_61: int := safe_index_seq(v_seq_21, v_int_60);
		v_int_9 := v_int_61;
		var v_DT_2_1_1: DT_2<int, real> := DT_2_1;
		var v_DT_2_1_2: DT_2<int, real> := v_DT_2_1_1;
		var v_real_int_int_1: (real, int, int) := (8.88, 17, 14);
		var v_real_int_int_2: (real, int, int) := v_real_int_int_1;
		var v_int_12: int := m_method_2(v_DT_2_1_2, v_real_int_int_2);
		var v_seq_6: seq<int> := [13];
		var v_int_13: int := 14;
		var v_seq_22: seq<int> := v_seq_6;
		var v_int_62: int := v_int_13;
		var v_int_63: int := safe_index_seq(v_seq_22, v_int_62);
		v_int_13 := v_int_63;
		if (if ((if ((|v_seq_5| > 0)) then (v_seq_5[v_int_9]) else ((if (true) then (true) else (false))))) then ((v_int_12 == (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_13]) else (15)))) else (v_bool_1)) {
			
		} else {
			var v_int_14: int := v_int_8;
			var v_int_15: int := v_int_9;
			var v_int_16: int := safe_modulus(v_int_14, v_int_15);
			v_int_13 := v_int_16;
			var v_real_int_int_6: (real, int, int) := (8.88, 17, 14);
			var v_real_int_int_7: (real, int, int) := (8.88, 17, 14);
			var v_DT_1_1_11: DT_1<int> := DT_1_1;
			print "v_int_13", " ", v_int_13, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_bool_1", " ", v_bool_1, " ", "v_int_7", " ", v_int_7, " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_real_int_int_1.0", " ", (v_real_int_int_1.0 == 8.88), " ", "v_DT_2_1_2", " ", v_DT_2_1_2, " ", "v_seq_6", " ", v_seq_6, " ", "v_seq_5", " ", v_seq_5, " ", "v_DT_2_1_1", " ", v_DT_2_1_1, " ", "v_seq_4", " ", v_seq_4, " ", "v_real_int_int_1.2", " ", v_real_int_int_1.2, " ", "v_real_int_int_1.1", " ", v_real_int_int_1.1, " ", "v_int_9", " ", v_int_9, " ", "v_real_int_int_2", " ", (v_real_int_int_2 == v_real_int_int_6), " ", "v_real_int_int_1", " ", (v_real_int_int_1 == v_real_int_int_7), " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_seq_3", " ", (v_seq_3 == [{2, 14}, {}, {1, 7, 8, 13}]), " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_8", " ", v_int_8, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_map_1", " ", (v_map_1 == map[v_DT_1_1_11 := [{2, 14}, {}, {1, 7, 8, 13}]]), "\n";
			continue;
		}
		var v_int_17: int := 8;
		var v_bool_3: bool := true;
		var v_bool_4: bool := false;
		var v_bool_5: bool := false;
		var v_map_2: map<int, int> := m_method_3(v_int_17, v_bool_3, v_bool_4, v_bool_5);
		var v_array_1: array<bool> := new bool[5] [false, true, true, false, false];
		var v_map_4: map<int, int> := v_map_2[v_array_1.Length := v_int_7];
		var v_map_3: map<bool, int> := map[false := 20, true := 16];
		var v_bool_6: bool := true;
		var v_int_18: int := ((if ((v_bool_6 in v_map_3)) then (v_map_3[v_bool_6]) else (4)) - (25 / 24));
		var v_bool_7: bool := false;
		var v_bool_8: bool := true;
		var v_seq_7: seq<DT_1<int>> := m_method_4(v_bool_7, v_bool_8);
		var v_seq_8: seq<DT_1<int>> := v_seq_7;
		var v_int_19: int := v_int_18;
		var v_bool_11: bool := false;
		var v_bool_12: bool := true;
		var v_bool_13: bool := true;
		var v_char_1: char := m_method_5(v_bool_11, v_bool_12, v_bool_13);
		var v_map_5: map<bool, char> := (map[true := 'N', false := 'N', false := 'H'] - {false, true})[(match true {
			case _ => true
		}) := v_char_1];
		var v_bool_19: bool := v_array_1[1];
		var v_bool_16: bool := (multiset{26} <= multiset{29});
		var v_bool_17: bool := (if (false) then (true) else (true));
		var v_int_33: int := 25;
		var v_int_34: int := 12;
		var v_int_35: int := 29;
		var v_int_36: int := 22;
		var v_bool_15: bool := m_method_7(v_int_33, v_int_34, v_int_35, v_int_36);
		var v_bool_18: bool := v_bool_15;
		var v_char_2: char := m_method_5(v_bool_16, v_bool_17, v_bool_18);
		var v_bool_22: bool := (v_bool_13 || v_bool_17);
		var v_seq_9: seq<int> := [];
		var v_int_37: int := 25;
		var v_int_42: int := (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_37]) else (3));
		var v_int_38: int := 23;
		var v_int_39: int := 12;
		var v_int_40: int := safe_division(v_int_38, v_int_39);
		var v_int_43: int := v_int_40;
		var v_seq_10: seq<int> := [14];
		var v_int_41: int := 1;
		var v_int_44: int := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_41]) else (25));
		var v_int_45: int := v_int_12;
		var v_bool_20: bool := m_method_7(v_int_42, v_int_43, v_int_44, v_int_45);
		var v_bool_23: bool := v_bool_20;
		var v_map_6: map<bool, bool> := (map[true := true, true := false, true := true] - {false});
		var v_bool_21: bool := (if (true) then (true) else (true));
		var v_bool_24: bool := (if ((v_bool_21 in v_map_6)) then (v_map_6[v_bool_21]) else ((true ==> false)));
		var v_char_3: char := m_method_5(v_bool_22, v_bool_23, v_bool_24);
		v_int_33, v_DT_1_1_7, v_char_3, v_char_2 := (if ((v_int_18 in v_map_4)) then (v_map_4[v_int_18]) else (v_real_int_int_1.1)), (match true {
			case _ => v_DT_1_1_1
		}), (if ((v_bool_19 in v_map_5)) then (v_map_5[v_bool_19]) else (v_char_2)), v_char_3;
		var v_DT_2_4_3: DT_2<char, int> := DT_2_4(5, 15);
		var v_DT_2_4_4: DT_2<char, int> := DT_2_4(16, 13);
		var v_DT_2_4_5: DT_2<char, int> := DT_2_4(12, 3);
		var v_DT_2_4_6: DT_2<char, int> := DT_2_4(2, 29);
		var v_DT_2_4_7: DT_2<char, int> := DT_2_4(7, 19);
		var v_DT_2_4_8: DT_2<char, int> := DT_2_4(6, 14);
		var v_DT_2_4_9: DT_2<char, int> := DT_2_4(22, 17);
		var v_DT_2_4_10: DT_2<char, int> := DT_2_4(24, 13);
		var v_DT_2_4_11: DT_2<char, int> := DT_2_4(1, 9);
		var v_DT_2_4_12: DT_2<char, int> := DT_2_4(2, 16);
		var v_DT_2_4_13: DT_2<char, int> := DT_2_4(7, 5);
		var v_DT_2_4_14: DT_2<char, int> := DT_2_4(11, 27);
		var v_DT_2_4_15: DT_2<char, int> := DT_2_4(23, 28);
		var v_DT_2_4_16: DT_2<char, int> := DT_2_4(15, -5);
		var v_DT_2_4_17: DT_2<char, int> := DT_2_4(22, -19);
		var v_DT_2_4_18: DT_2<char, int> := DT_2_4(8, 29);
		var v_DT_2_4_19: DT_2<char, int> := DT_2_4(7, 0);
		var v_DT_2_4_20: DT_2<char, int> := DT_2_4(14, 18);
		var v_DT_2_4_21: DT_2<char, int> := DT_2_4(23, 26);
		var v_DT_2_4_22: DT_2<char, int> := DT_2_4(22, 12);
		var v_DT_2_4_23: DT_2<char, int> := DT_2_4(12, 5);
		var v_DT_2_4_24: DT_2<char, int> := DT_2_4(2, 0);
		var v_DT_2_4_25: DT_2<char, int> := DT_2_4(26, 11);
		var v_DT_2_4_26: DT_2<char, int> := DT_2_4(26, 3);
		var v_DT_2_4_27: DT_2<char, int> := DT_2_4(15, 28);
		var v_DT_2_4_28: DT_2<char, int> := DT_2_4(14, 6);
		var v_DT_2_4_29: DT_2<char, int> := DT_2_4(7, 8);
		var v_DT_2_4_30: DT_2<char, int> := DT_2_4(15, 12);
		var v_seq_11: seq<map<set<bool>, bool>> := [map[{true, true, false} := false, {true, true} := true], map[{false} := true, {true} := false, {true, true, false} := true, {true, false} := true], map[{true} := true, {false, false, false} := true, {true} := false]];
		var v_int_46: int := -18;
		var v_map_7: map<set<bool>, bool> := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_46]) else (map[{} := true]));
		var v_seq_12: seq<set<bool>> := [{true, false}, {}, {false, false, true, false}];
		var v_int_47: int := 28;
		var v_set_1: set<bool> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_47]) else ({false, false, false}));
		if (((if (true) then (multiset{{v_DT_2_4_3, v_DT_2_4_4, v_DT_2_4_5}, {v_DT_2_4_6, v_DT_2_4_7}}) else (multiset{{v_DT_2_4_8}, {}, {v_DT_2_4_9}, {v_DT_2_4_10, v_DT_2_4_11, v_DT_2_4_12}})) !! (match false {
			case _ => multiset{{}, {v_DT_2_4_29, v_DT_2_4_30}}
		})) ==> (if ((v_set_1 in v_map_7)) then (v_map_7[v_set_1]) else (v_bool_6))) {
			var v_map_8: map<bool, map<int, bool>> := map[false := map[18 := false, -29 := false], true := map[5 := false, 17 := false, 19 := false]];
			var v_bool_25: bool := true;
			var v_map_9: map<int, bool> := (if ((v_bool_25 in v_map_8)) then (v_map_8[v_bool_25]) else (map[27 := false, 15 := true]));
			var v_int_48: int := (match 24.83 {
				case _ => 29
			});
			var v_seq_13: seq<set<set<bool>>> := (match 'l' {
				case _ => [{}]
			});
			var v_int_49: int := (28 - -21);
			var v_seq_15: seq<int> := [16, 7, 26, 18];
			var v_seq_16: seq<int> := (if ((|v_seq_15| > 0)) then (v_seq_15[23..22]) else (v_seq_15));
			var v_bool_26: bool := !(true);
			var v_DT_2_1_3: DT_2<int, real> := DT_2_1;
			var v_DT_2_1_4: DT_2<int, real> := v_DT_2_1_3;
			var v_real_int_int_3: (real, int, int) := (-8.72, -22, -22);
			var v_real_int_int_4: (real, int, int) := v_real_int_int_3;
			var v_int_50: int := m_method_2(v_DT_2_1_4, v_real_int_int_4);
			var v_int_51: int := v_int_50;
			var v_map_10: map<int, seq<int>> := m_method_8(v_seq_16, v_bool_26, v_int_51);
			var v_map_13: map<int, seq<int>> := v_map_10;
			var v_map_11: map<bool, int> := map[false := 18, false := 23, false := -8, false := 9];
			var v_bool_27: bool := true;
			var v_map_12: map<bool, int> := map[false := -14];
			var v_bool_28: bool := false;
			var v_int_55: int := ((if ((v_bool_27 in v_map_11)) then (v_map_11[v_bool_27]) else (22)) - (if ((v_bool_28 in v_map_12)) then (v_map_12[v_bool_28]) else (-19)));
			var v_seq_17: seq<int> := [14, 21, 19];
			var v_seq_18: seq<int> := v_seq_17;
			var v_int_52: int := 5;
			var v_int_53: int := safe_index_seq(v_seq_18, v_int_52);
			var v_int_54: int := v_int_53;
			var v_set_2: set<set<bool>>, v_seq_19: seq<int> := (if ((if ((v_int_48 in v_map_9)) then (v_map_9[v_int_48]) else (v_array_1[0]))) then ((if ((|v_seq_13| > 0)) then (v_seq_13[v_int_49]) else (({} - {{}, {true}, {false, false, true}, {}})))) else ((({{false}, {false, false, false, false}, {false}} - {{}, {}}) * ({{true, false, true, false}, {true, false, false}} + {{true, true, true, true}, {true, false, true}, {true, false, false, true}, {}})))), (if ((v_int_55 in v_map_13)) then (v_map_13[v_int_55]) else (((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_54 := 4]) else (v_seq_17)) + v_seq_16)));
			break;
		} else {
			return ;
		}
	}
	var v_DT_1_1_12: DT_1<int> := DT_1_1;
	var v_DT_1_1_13: DT_1<int> := DT_1_1;
	assert ((v_DT_1_1_2 == v_DT_1_1_12) && (v_int_8 == 0) && (v_DT_1_1_7 == v_DT_1_1_13));
	expect ((v_DT_1_1_2 == v_DT_1_1_12) && (v_int_8 == 0) && (v_DT_1_1_7 == v_DT_1_1_13));
	var v_DT_1_1_14: DT_1<int> := DT_1_1;
	print "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_int_57", " ", v_int_57, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_int_56", " ", v_int_56, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_seq_3", " ", (v_seq_3 == [{2, 14}, {}, {1, 7, 8, 13}]), " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_8", " ", v_int_8, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_map_1", " ", (v_map_1 == map[v_DT_1_1_14 := [{2, 14}, {}, {1, 7, 8, 13}]]), "\n";
}
