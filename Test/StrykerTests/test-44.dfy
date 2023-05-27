// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1 = DT_1_1
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

method m_method_5(p_m_method_5_1: bool, p_m_method_5_2: bool) returns (ret_1: seq<bool>)
{
	var v_seq_15: seq<int> := [29, 26, 17];
	var v_int_23: int := 27;
	var v_int_24: int, v_int_25: int := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_23]) else (11)), (8.55).Floor;
	for v_int_22 := v_int_24 to v_int_25 
		invariant (v_int_25 - v_int_22 >= 0)
	{
		var v_map_5: map<bool, seq<bool>> := map[true := [true], false := [true, true, false], false := [true, false, false], false := [true, true, false, false], true := []];
		var v_bool_17: bool := true;
		return (if ((v_bool_17 in v_map_5)) then (v_map_5[v_bool_17]) else ([false, true, false, true]));
	}
	match (if (false) then (false) else (false)) {
		case _ => {
			var v_seq_16: seq<bool> := [true];
			var v_seq_17: seq<bool> := v_seq_16;
			var v_int_26: int := 27;
			var v_int_27: int := safe_index_seq(v_seq_17, v_int_26);
			var v_int_28: int := v_int_27;
			return (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_28 := true]) else (v_seq_16));
		}
		
	}
	
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool, p_m_method_4_3: bool, p_m_method_4_4: bool) returns (ret_1: (bool, int, bool))
	requires ((p_m_method_4_2 == true) && (p_m_method_4_1 == true) && (p_m_method_4_4 == false) && (p_m_method_4_3 == true));
	ensures (((p_m_method_4_2 == true) && (p_m_method_4_1 == true) && (p_m_method_4_4 == false) && (p_m_method_4_3 == true)) ==> (((ret_1).0 == false) && ((ret_1).1 == 9) && ((ret_1).2 == true)));
{
	var v_bool_4: bool, v_bool_5: bool, v_bool_6: bool := p_m_method_4_3, (7 >= 28), p_m_method_4_4;
	var v_bool_int_bool_1: (bool, int, bool) := (true, -29, true);
	var v_bool_int_bool_2: (bool, int, bool) := (false, 9, true);
	print "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_bool_6", " ", v_bool_6, " ", "v_bool_int_bool_1.0", " ", v_bool_int_bool_1.0, " ", "v_bool_int_bool_2", " ", v_bool_int_bool_2, " ", "p_m_method_4_4", " ", p_m_method_4_4, " ", "v_bool_int_bool_1", " ", v_bool_int_bool_1, " ", "v_bool_int_bool_1.1", " ", v_bool_int_bool_1.1, " ", "v_bool_int_bool_2.0", " ", v_bool_int_bool_2.0, " ", "p_m_method_4_1", " ", p_m_method_4_1, " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "v_bool_int_bool_1.2", " ", v_bool_int_bool_1.2, " ", "v_bool_int_bool_2.1", " ", v_bool_int_bool_2.1, " ", "p_m_method_4_2", " ", p_m_method_4_2, " ", "v_bool_int_bool_2.2", " ", v_bool_int_bool_2.2, "\n";
	return (if (false) then (v_bool_int_bool_1) else (v_bool_int_bool_2));
}

method m_method_3(p_m_method_3_1: real, p_m_method_3_2: seq<bool>, p_m_method_3_3: bool, p_m_method_3_4: char) returns (ret_1: DT_1)
	requires ((19.11 < p_m_method_3_1 < 19.31) && (p_m_method_3_3 == true) && |p_m_method_3_2| == 2 && (p_m_method_3_2[0] == false) && (p_m_method_3_2[1] == true) && (p_m_method_3_4 == 'U'));
	ensures (((19.11 < p_m_method_3_1 < 19.31) && (p_m_method_3_3 == true) && |p_m_method_3_2| == 2 && (p_m_method_3_2[0] == false) && (p_m_method_3_2[1] == true) && (p_m_method_3_4 == 'U')) ==> ((ret_1.DT_1_1? && ((ret_1 == DT_1_1)))));
{
	var v_seq_6: seq<bool> := [true];
	var v_int_11: int := -22;
	var v_int_12: int := safe_index_seq(v_seq_6, v_int_11);
	var v_seq_7: seq<bool> := [false];
	var v_int_13: int := 23;
	var v_int_14: int := safe_index_seq(v_seq_7, v_int_13);
	var v_int_15: int, v_int_16: int := v_int_12, v_int_14;
	for v_int_10 := v_int_15 downto v_int_16 
		invariant (v_int_10 - v_int_16 >= 0)
	{
		
	}
	var v_DT_1_1_1: DT_1 := DT_1_1;
	var v_DT_1_1_2: DT_1 := DT_1_1;
	var v_DT_1_1_3: DT_1 := DT_1_1;
	var v_DT_1_1_4: DT_1 := DT_1_1;
	var v_seq_8: seq<DT_1> := [v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3, v_DT_1_1_4];
	var v_int_17: int := 0;
	var v_DT_1_1_5: DT_1 := DT_1_1;
	print "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", v_seq_8, " ", "v_int_12", " ", v_int_12, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_11", " ", v_int_11, " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 19.21), " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 'U'), " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
	return (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_17]) else (v_DT_1_1_5));
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

method m_method_2(p_m_method_2_1: (real, real)) returns (ret_1: array<real>)
	requires ((-5.78 < (p_m_method_2_1).0 < -5.58) && (-15.46 < (p_m_method_2_1).1 < -15.26));
	ensures (((-5.78 < (p_m_method_2_1).0 < -5.58) && (-15.46 < (p_m_method_2_1).1 < -15.26)) ==> (ret_1.Length == 3 && (-14.23 < ret_1[0] < -14.03) && (17.95 < ret_1[1] < 18.15) && (-28.47 < ret_1[2] < -28.27)));
{
	var v_array_3: array<real> := new real[3] [-14.13, 18.05, -28.37];
	var v_array_4: array<real> := new real[5] [-15.10, 15.65, -9.53, -19.82, 4.91];
	var v_seq_4: seq<array<real>> := [v_array_3, v_array_4];
	var v_int_8: int := 18;
	var v_seq_49: seq<array<real>> := v_seq_4;
	var v_int_65: int := v_int_8;
	var v_int_66: int := safe_index_seq(v_seq_49, v_int_65);
	v_int_8 := v_int_66;
	var v_array_5: array<real> := new real[3] [19.15, 22.18, -15.95];
	var v_real_real_5: (real, real) := (-5.68, -15.36);
	print "v_array_4[4]", " ", (v_array_4[4] == 4.91), " ", "v_int_8", " ", v_int_8, " ", "v_array_3", " ", (v_array_3 == v_array_3), " ", "p_m_method_2_1.0", " ", (p_m_method_2_1.0 == -5.68), " ", "v_array_4", " ", (v_array_4 == v_array_4), " ", "p_m_method_2_1.1", " ", (p_m_method_2_1.1 == -15.36), " ", "p_m_method_2_1", " ", (p_m_method_2_1 == v_real_real_5), " ", "v_array_5", " ", (v_array_5 == v_array_5), " ", "v_seq_4", " ", (v_seq_4 == [v_array_3, v_array_4]), " ", "v_array_3[0]", " ", (v_array_3[0] == -14.13), " ", "v_array_4[1]", " ", (v_array_4[1] == 15.65), " ", "v_array_5[0]", " ", (v_array_5[0] == 19.15), " ", "v_array_4[0]", " ", (v_array_4[0] == -15.10), " ", "v_array_3[1]", " ", (v_array_3[1] == 18.05), " ", "v_array_4[3]", " ", (v_array_4[3] == -19.82), " ", "v_array_5[2]", " ", (v_array_5[2] == -15.95), " ", "v_array_3[2]", " ", (v_array_3[2] == -28.37), " ", "v_array_4[2]", " ", (v_array_4[2] == -9.53), " ", "v_array_5[1]", " ", (v_array_5[1] == 22.18), "\n";
	return (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_8]) else (v_array_5));
}

method m_method_1(p_m_method_1_1: array<bool>, p_m_method_1_2: array<real>, p_m_method_1_3: DT_1, p_m_method_1_4: (bool, int, bool)) returns (ret_1: bool)
	requires (p_m_method_1_1.Length == 3 && (p_m_method_1_1[0] == true) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == true) && (p_m_method_1_3.DT_1_1? && ((p_m_method_1_3 == DT_1_1))) && p_m_method_1_2.Length == 3 && (-14.23 < p_m_method_1_2[0] < -14.03) && (17.95 < p_m_method_1_2[1] < 18.15) && (-28.47 < p_m_method_1_2[2] < -28.27) && ((p_m_method_1_4).0 == false) && ((p_m_method_1_4).1 == 9) && ((p_m_method_1_4).2 == true));
	ensures ((p_m_method_1_1.Length == 3 && (p_m_method_1_1[0] == true) && (p_m_method_1_1[1] == false) && (p_m_method_1_1[2] == true) && (p_m_method_1_3.DT_1_1? && ((p_m_method_1_3 == DT_1_1))) && p_m_method_1_2.Length == 3 && (-14.23 < p_m_method_1_2[0] < -14.03) && (17.95 < p_m_method_1_2[1] < 18.15) && (-28.47 < p_m_method_1_2[2] < -28.27) && ((p_m_method_1_4).0 == false) && ((p_m_method_1_4).1 == 9) && ((p_m_method_1_4).2 == true)) ==> ((ret_1 == false)));
{
	print "p_m_method_1_4.0", " ", p_m_method_1_4.0, " ", "p_m_method_1_1[2]", " ", p_m_method_1_1[2], " ", "p_m_method_1_2[0]", " ", (p_m_method_1_2[0] == -14.13), " ", "p_m_method_1_1[1]", " ", p_m_method_1_1[1], " ", "p_m_method_1_2[1]", " ", (p_m_method_1_2[1] == 18.05), " ", "p_m_method_1_1[0]", " ", p_m_method_1_1[0], " ", "p_m_method_1_4.1", " ", p_m_method_1_4.1, " ", "p_m_method_1_4.2", " ", p_m_method_1_4.2, " ", "p_m_method_1_2", " ", "p_m_method_1_1", " ", "p_m_method_1_2[2]", " ", (p_m_method_1_2[2] == -28.37), " ", "p_m_method_1_4", " ", p_m_method_1_4, " ", "p_m_method_1_3", " ", p_m_method_1_3, "\n";
	return p_m_method_1_4.0;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_array_1: array<bool> := new bool[5] [true, true, false, true, true];
	var v_array_2: array<bool> := new bool[3];
	v_array_2[0] := true;
	v_array_2[1] := false;
	v_array_2[2] := true;
	var v_seq_3: seq<array<bool>> := [v_array_1, v_array_2];
	var v_int_7: int := (19 / 19);
	var v_array_7: array<bool> := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (v_array_1));
	var v_real_real_1: (real, real) := (-5.68, -15.36);
	var v_real_real_2: (real, real) := (3.28, 28.21);
	var v_seq_5: seq<(real, real)> := [v_real_real_1, v_real_real_2];
	var v_int_9: int := 28;
	var v_seq_48: seq<(real, real)> := v_seq_5;
	var v_int_63: int := v_int_9;
	var v_int_64: int := safe_index_seq(v_seq_48, v_int_63);
	v_int_9 := v_int_64;
	var v_real_real_3: (real, real) := (17.62, 19.21);
	var v_real_real_4: (real, real) := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_9]) else (v_real_real_3));
	var v_array_6: array<real> := m_method_2(v_real_real_4);
	var v_array_8: array<real> := v_array_6;
	var v_real_1: real := v_real_real_3.1;
	var v_map_1: map<bool, seq<bool>> := map[true := [false, true], false := [true, false]];
	var v_bool_1: bool := true;
	var v_seq_9: seq<bool> := (if ((v_bool_1 in v_map_1)) then (v_map_1[v_bool_1]) else ([false]));
	var v_bool_3: bool := v_array_2[2];
	var v_map_2: map<bool, char> := map[true := 'U'];
	var v_bool_2: bool := true;
	var v_char_1: char := (if ((v_bool_2 in v_map_2)) then (v_map_2[v_bool_2]) else ('w'));
	var v_DT_1_1_6: DT_1 := m_method_3(v_real_1, v_seq_9, v_bool_3, v_char_1);
	var v_DT_1_1_7: DT_1 := v_DT_1_1_6;
	var v_bool_7: bool := (true <== false);
	var v_bool_8: bool := (false || true);
	var v_bool_9: bool := !(false);
	var v_bool_10: bool := (if (false) then (false) else (false));
	var v_bool_int_bool_3: (bool, int, bool) := m_method_4(v_bool_7, v_bool_8, v_bool_9, v_bool_10);
	var v_bool_int_bool_4: (bool, int, bool) := v_bool_int_bool_3;
	var v_bool_11: bool := m_method_1(v_array_7, v_array_8, v_DT_1_1_7, v_bool_int_bool_4);
	if v_bool_11 {
		var v_map_4: map<bool, bool> := ((map[true := true] + map[true := false, false := true]) - (match true {
			case _ => {true, true, false}
		}));
		var v_array_9: array<bool> := new bool[5] [false, true, false, true, false];
		var v_array_10: array<bool> := new bool[3] [false, true, true];
		var v_array_11: array<bool> := new bool[3] [true, true, true];
		var v_seq_10: seq<array<bool>> := [v_array_9, v_array_10, v_array_11];
		var v_int_18: int := -17;
		var v_array_12: array<bool> := new bool[5] [true, true, true, false, true];
		var v_array_13: array<bool> := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_18]) else (v_array_12));
		var v_array_14: array<real> := v_array_8;
		var v_DT_1_1_8: DT_1 := DT_1_1;
		var v_DT_1_1_9: DT_1 := DT_1_1;
		var v_seq_11: seq<DT_1> := [v_DT_1_1_8, v_DT_1_1_9];
		var v_int_19: int := 12;
		var v_DT_1_1_10: DT_1 := DT_1_1;
		var v_DT_1_1_11: DT_1 := (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_19]) else (v_DT_1_1_10));
		var v_bool_int_bool_5: (bool, int, bool) := (false, 16, true);
		var v_bool_int_bool_6: (bool, int, bool) := (true, 4, true);
		var v_bool_int_bool_7: (bool, int, bool) := (true, 14, false);
		var v_bool_int_bool_8: (bool, int, bool) := (false, 6, true);
		var v_seq_12: seq<(bool, int, bool)> := [v_bool_int_bool_5, v_bool_int_bool_6, v_bool_int_bool_7, v_bool_int_bool_8];
		var v_int_20: int := -17;
		var v_bool_int_bool_9: (bool, int, bool) := (true, 11, true);
		var v_bool_int_bool_10: (bool, int, bool) := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_20]) else (v_bool_int_bool_9));
		var v_bool_12: bool := m_method_1(v_array_13, v_array_14, v_DT_1_1_11, v_bool_int_bool_10);
		var v_bool_16: bool := v_bool_12;
		var v_array_15: array<bool> := new bool[3] [false, true, false];
		var v_array_16: array<bool> := new bool[4];
		v_array_16[0] := true;
		v_array_16[1] := true;
		v_array_16[2] := false;
		v_array_16[3] := true;
		var v_array_17: array<bool> := new bool[5] [false, false, false, false, false];
		var v_map_3: map<bool, array<bool>> := map[true := v_array_15, true := v_array_16, true := v_array_17];
		var v_bool_13: bool := false;
		var v_array_18: array<bool> := new bool[4] [false, true, false, false];
		var v_array_23: array<bool> := (if ((v_bool_13 in v_map_3)) then (v_map_3[v_bool_13]) else (v_array_18));
		var v_array_19: array<real> := new real[4] [18.58, -9.56, 28.73, -2.28];
		var v_array_20: array<real> := new real[4] [25.28, 10.09, -7.57, -17.36];
		var v_array_21: array<real> := new real[4] [2.11, 2.54, 20.86, 6.45];
		var v_seq_13: seq<array<real>> := [v_array_19, v_array_20, v_array_21];
		var v_int_21: int := 0;
		var v_array_22: array<real> := new real[5] [-19.84, 6.97, 22.69, -4.84, -22.60];
		var v_array_24: array<real> := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_21]) else (v_array_22));
		var v_real_2: real := 3.48;
		var v_seq_14: seq<bool> := [true, true, false, false];
		var v_bool_14: bool := false;
		var v_char_2: char := 'v';
		var v_DT_1_1_12: DT_1 := m_method_3(v_real_2, v_seq_14, v_bool_14, v_char_2);
		var v_DT_1_1_13: DT_1 := v_DT_1_1_12;
		var v_bool_int_bool_11: (bool, int, bool) := v_bool_int_bool_3;
		var v_bool_15: bool := m_method_1(v_array_23, v_array_24, v_DT_1_1_13, v_bool_int_bool_11);
		if (if ((v_bool_16 in v_map_4)) then (v_map_4[v_bool_16]) else (v_bool_15)) {
			var v_bool_18: bool := (match 'Z' {
				case _ => true
			});
			var v_bool_19: bool := ('i' in ['n', 'o']);
			var v_seq_18: seq<bool> := m_method_5(v_bool_18, v_bool_19);
			var v_seq_19: seq<bool> := v_seq_18;
			var v_int_29: int := (if (true) then (17) else (-21));
			var v_int_30: int := v_int_7;
			var v_int_31: int := safe_division(v_int_29, v_int_30);
			var v_int_32: int := v_int_31;
			var v_seq_20: seq<seq<bool>> := [[true, true, false], [false], [false, false, false, true], [false]];
			var v_int_33: int := 5;
			var v_seq_21: seq<bool> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_33]) else ([]));
			var v_seq_22: seq<bool> := (if (true) then ([false, false, true, false]) else ([false, true, false, true]));
			var v_seq_23: seq<bool> := (if ((|v_seq_22| > 0)) then (v_seq_22[(if (true) then (18) else (27))..v_bool_int_bool_6.1]) else (v_seq_22));
			var v_int_34: int := v_int_33;
			var v_map_7: map<char, map<char, char>> := map['n' := map['r' := 'z', 'k' := 'f'], 'M' := map['v' := 'n'], 'P' := map['O' := 'K', 'i' := 'f'], 'b' := map['L' := 'Z', 'i' := 'D']];
			var v_char_4: char := 'm';
			v_array_10[0], v_seq_9, v_bool_13 := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_32]) else (v_array_9[0])), (v_seq_9 + (if ((|v_seq_21| > 0)) then (v_seq_21[(14 / 25)..v_bool_int_bool_9.1]) else (v_seq_21))), (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_34]) else ((v_char_2 in (if ((v_char_4 in v_map_7)) then (v_map_7[v_char_4]) else (map['E' := 'k', 'q' := 'v'])))));
			return ;
		}
		var v_map_8: map<char, char> := ((match 'l' {
			case _ => map['D' := 'E', 'J' := 'U', 'X' := 'j']
		}) + (map['j' := 't', 'G' := 'C', 'n' := 's'] + map['X' := 'd', 'X' := 'M', 'h' := 'v', 'T' := 't']));
		var v_char_5: char := v_char_2;
		match (if ((v_char_5 in v_map_8)) then (v_map_8[v_char_5]) else (v_char_1)) {
			case _ => {
				return ;
			}
			
		}
		
	} else {
		var v_seq_28: seq<bool> := v_seq_9;
		var v_int_42: int := (v_int_7 * (if (false) then (9) else (5)));
		var v_seq_50: seq<bool> := v_seq_28;
		var v_int_67: int := v_int_42;
		var v_int_68: int := safe_index_seq(v_seq_50, v_int_67);
		v_int_42 := v_int_68;
		var v_seq_29: seq<bool> := v_seq_9;
		var v_map_19: map<char, int> := map['G' := 19, 'W' := -18, 'J' := 9];
		var v_char_18: char := 'e';
		var v_int_43: int := (if ((v_char_18 in v_map_19)) then (v_map_19[v_char_18]) else (10));
		if (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_42]) else ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_43]) else (v_bool_3)))) {
			return ;
		} else {
			var v_map_20: map<char, map<char, char>> := map['L' := map['x' := 'M'], 'n' := map['p' := 'c', 'I' := 'C', 'v' := 'v', 'g' := 'u']];
			var v_char_19: char := 'X';
			var v_map_21: map<char, char> := ((if ((v_char_19 in v_map_20)) then (v_map_20[v_char_19]) else (map['c' := 'G', 'B' := 'o'])) - (match 'a' {
				case 'f' => {'a', 'y', 'q'}
				case 'q' => {'p', 'r', 'b'}
				case _ => {'F'}
			}));
			var v_char_20: char := v_char_19;
			v_char_20 := (if ((v_char_20 in v_map_21)) then (v_map_21[v_char_20]) else ((match 'B' {
				case 'v' => v_char_1
				case _ => (if (false) then ('Q') else ('m'))
			})));
			var v_map_23: map<char, bool> := map['B' := true, 'V' := false, 'm' := false, 'O' := false, 'j' := false]['s' := false];
			var v_seq_30: seq<char> := ['Z', 'Q'];
			var v_int_44: int := 1;
			var v_char_22: char := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_44]) else ('B'));
			var v_map_22: map<char, bool> := map['z' := false, 'V' := false, 'N' := true];
			var v_char_21: char := 'q';
			var v_seq_31: seq<bool> := [];
			var v_seq_32: seq<bool> := v_seq_31;
			var v_int_45: int := 26;
			var v_int_46: int := safe_index_seq(v_seq_32, v_int_45);
			var v_int_47: int := v_int_46;
			var v_seq_33: seq<bool> := (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_47 := false]) else (v_seq_31));
			var v_int_48: int := v_int_7;
			if ((if ((v_char_22 in v_map_23)) then (v_map_23[v_char_22]) else ((if ((v_char_21 in v_map_22)) then (v_map_22[v_char_21]) else (false)))) && (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_48]) else (('L' in multiset{'O'})))) {
				var v_map_24: map<char, seq<char>> := map['N' := ['V', 'Q']];
				var v_char_23: char := 'w';
				var v_seq_34: seq<char> := (if ((v_char_23 in v_map_24)) then (v_map_24[v_char_23]) else (['n']));
				var v_int_49: int := (if (false) then (24) else (27));
				var v_map_25: map<char, char> := map['Z' := 'U'];
				var v_char_24: char := 'C';
				var v_map_26: map<char, char> := map['P' := 'l'];
				var v_char_25: char := 'z';
				var v_seq_35: seq<char> := ['S'];
				var v_int_50: int := 27;
				var v_map_27: map<char, seq<char>> := map['I' := [], 'g' := ['C', 'e', 'k', 'r']];
				var v_char_26: char := 'V';
				var v_seq_36: seq<char> := (if ((v_char_26 in v_map_27)) then (v_map_27[v_char_26]) else ([]));
				var v_seq_37: seq<char> := v_seq_36;
				var v_int_51: int := (5 % 1);
				var v_int_52: int := safe_index_seq(v_seq_37, v_int_51);
				var v_int_53: int := v_int_52;
				var v_seq_38: seq<char> := (if ((|v_seq_36| > 0)) then (v_seq_36[v_int_53 := (match 'n' {
					case _ => 'V'
				})]) else (v_seq_36));
				var v_int_54: int := v_int_46;
				var v_map_29: map<char, char> := v_map_21;
				var v_char_28: char := (if (true) then ('X') else ('e'));
				var v_map_28: map<char, char> := map['h' := 'g', 'Q' := 'd', 'Y' := 'G', 'b' := 'L'];
				var v_char_27: char := 'g';
				var v_seq_39: seq<seq<char>> := [];
				var v_seq_40: seq<seq<char>> := (if ((|v_seq_39| > 0)) then (v_seq_39[10..0]) else (v_seq_39));
				var v_map_30: map<char, int> := map['g' := 22, 't' := 1, 'W' := 13];
				var v_char_29: char := 'w';
				var v_int_55: int := (if ((v_char_29 in v_map_30)) then (v_map_30[v_char_29]) else (8));
				var v_seq_41: seq<char> := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_55]) else ((if (true) then (['z']) else ([]))));
				var v_int_56: int := (if ((match 'f' {
					case _ => true
				})) then (v_int_7) else ((if (false) then (25) else (18))));
				var v_seq_42: seq<char> := ['K', 'n', 'C'];
				var v_seq_43: seq<char> := v_seq_42;
				var v_int_57: int := 5;
				var v_int_58: int := safe_index_seq(v_seq_43, v_int_57);
				var v_int_59: int := v_int_58;
				var v_seq_44: seq<char> := (if ((|v_seq_42| > 0)) then (v_seq_42[v_int_59 := 'W']) else (v_seq_42));
				var v_int_60: int := v_int_59;
				v_char_26, v_char_22, v_char_21, v_char_20, v_char_29 := v_char_1, (match 'i' {
					case _ => (if ((if (false) then (false) else (false))) then ((if ((v_char_25 in v_map_26)) then (v_map_26[v_char_25]) else ('Q'))) else ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_50]) else ('H'))))
				}), v_char_18, (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_54]) else ((if ((v_char_28 in v_map_29)) then (v_map_29[v_char_28]) else ((if ((v_char_27 in v_map_28)) then (v_map_28[v_char_27]) else ('w')))))), (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_56]) else ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_60]) else ((match 'g' {
					case _ => 'G'
				})))));
				var v_seq_45: seq<bool> := [false];
				var v_seq_46: seq<bool> := (if ((|v_seq_45| > 0)) then (v_seq_45[13..29]) else (v_seq_45));
				var v_int_61: int := (match 'a' {
					case _ => 22
				});
				var v_map_31: map<char, char> := (match 'r' {
					case _ => map['p' := 'F']
				});
				var v_seq_47: seq<char> := ['R', 'k', 'K'];
				var v_int_62: int := 3;
				var v_char_30: char := (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_62]) else ('D'));
				match (if ((if ((|v_seq_46| > 0)) then (v_seq_46[v_int_61]) else ((if (true) then (false) else (false))))) then ((if ((if (true) then (true) else (true))) then ((match 'Z' {
					case _ => 'b'
				})) else ((if (true) then ('B') else ('R'))))) else ((if ((v_char_30 in v_map_31)) then (v_map_31[v_char_30]) else (v_char_22)))) {
					case _ => {
						return ;
					}
					
				}
				
			}
			var v_real_real_6: (real, real) := (3.28, 28.21);
			var v_real_real_7: (real, real) := (-5.68, -15.36);
			var v_real_real_8: (real, real) := (-5.68, -15.36);
			var v_real_real_9: (real, real) := (17.62, 19.21);
			var v_real_real_10: (real, real) := (-5.68, -15.36);
			var v_real_real_11: (real, real) := (3.28, 28.21);
			print "v_char_22", " ", (v_char_22 == 'Q'), " ", "v_map_22", " ", (v_map_22 == map['V' := false, 'z' := false, 'N' := true]), " ", "v_map_23", " ", (v_map_23 == map['B' := true, 's' := false, 'V' := false, 'j' := false, 'm' := false, 'O' := false]), " ", "v_map_20", " ", (v_map_20 == map['L' := map['x' := 'M'], 'n' := map['p' := 'c', 'v' := 'v', 'g' := 'u', 'I' := 'C']]), " ", "v_map_21", " ", (v_map_21 == map['B' := 'o', 'c' := 'G']), " ", "v_char_19", " ", (v_char_19 == 'X'), " ", "v_int_46", " ", v_int_46, " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_seq_32", " ", v_seq_32, " ", "v_seq_33", " ", v_seq_33, " ", "v_int_48", " ", v_int_48, " ", "v_int_47", " ", v_int_47, " ", "v_char_21", " ", (v_char_21 == 'q'), " ", "v_char_20", " ", (v_char_20 == 'm'), " ", "v_seq_30", " ", (v_seq_30 == ['Z', 'Q']), " ", "v_seq_31", " ", v_seq_31, " ", "v_char_18", " ", (v_char_18 == 'e'), " ", "v_map_19", " ", (v_map_19 == map['G' := 19, 'W' := -18, 'J' := 9]), " ", "v_seq_28", " ", v_seq_28, " ", "v_int_43", " ", v_int_43, " ", "v_int_42", " ", v_int_42, " ", "v_seq_29", " ", v_seq_29, " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_real_real_2", " ", (v_real_real_2 == v_real_real_6), " ", "v_real_real_1", " ", (v_real_real_1 == v_real_real_7), " ", "v_real_real_4", " ", (v_real_real_4 == v_real_real_8), " ", "v_bool_7", " ", v_bool_7, " ", "v_real_real_3", " ", (v_real_real_3 == v_real_real_9), " ", "v_array_6", " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_bool_int_bool_4", " ", v_bool_int_bool_4, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_bool_int_bool_3", " ", v_bool_int_bool_3, " ", "v_array_7", " ", (v_array_7 == v_array_2), " ", "v_array_8", " ", "v_array_1[4]", " ", v_array_1[4], " ", "v_char_1", " ", (v_char_1 == 'U'), " ", "v_int_7", " ", v_int_7, " ", "v_real_real_3.1", " ", (v_real_real_3.1 == 19.21), " ", "v_real_real_2.1", " ", (v_real_real_2.1 == 28.21), " ", "v_real_real_3.0", " ", (v_real_real_3.0 == 17.62), " ", "v_real_real_1.1", " ", (v_real_real_1.1 == -15.36), " ", "v_real_real_2.0", " ", (v_real_real_2.0 == 3.28), " ", "v_map_1", " ", (v_map_1 == map[false := [true, false], true := [false, true]]), " ", "v_real_real_1.0", " ", (v_real_real_1.0 == -5.68), " ", "v_map_2", " ", (v_map_2 == map[true := 'U']), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_5", " ", (v_seq_5 == [v_real_real_10, v_real_real_11]), " ", "v_seq_3", " ", (v_seq_3 == [v_array_1, v_array_2]), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_real_1", " ", (v_real_1 == 19.21), " ", "v_bool_11", " ", v_bool_11, " ", "v_bool_10", " ", v_bool_10, " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
		}
		var v_real_real_12: (real, real) := (3.28, 28.21);
		var v_real_real_13: (real, real) := (-5.68, -15.36);
		var v_real_real_14: (real, real) := (-5.68, -15.36);
		var v_real_real_15: (real, real) := (17.62, 19.21);
		var v_real_real_16: (real, real) := (-5.68, -15.36);
		var v_real_real_17: (real, real) := (3.28, 28.21);
		print "v_char_18", " ", (v_char_18 == 'e'), " ", "v_map_19", " ", (v_map_19 == map['G' := 19, 'W' := -18, 'J' := 9]), " ", "v_seq_28", " ", v_seq_28, " ", "v_int_43", " ", v_int_43, " ", "v_int_42", " ", v_int_42, " ", "v_seq_29", " ", v_seq_29, " ", "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_real_real_2", " ", (v_real_real_2 == v_real_real_12), " ", "v_real_real_1", " ", (v_real_real_1 == v_real_real_13), " ", "v_real_real_4", " ", (v_real_real_4 == v_real_real_14), " ", "v_bool_7", " ", v_bool_7, " ", "v_real_real_3", " ", (v_real_real_3 == v_real_real_15), " ", "v_array_6", " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_bool_int_bool_4", " ", v_bool_int_bool_4, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_bool_int_bool_3", " ", v_bool_int_bool_3, " ", "v_array_7", " ", (v_array_7 == v_array_2), " ", "v_array_8", " ", "v_array_1[4]", " ", v_array_1[4], " ", "v_char_1", " ", (v_char_1 == 'U'), " ", "v_int_7", " ", v_int_7, " ", "v_real_real_3.1", " ", (v_real_real_3.1 == 19.21), " ", "v_real_real_2.1", " ", (v_real_real_2.1 == 28.21), " ", "v_real_real_3.0", " ", (v_real_real_3.0 == 17.62), " ", "v_real_real_1.1", " ", (v_real_real_1.1 == -15.36), " ", "v_real_real_2.0", " ", (v_real_real_2.0 == 3.28), " ", "v_map_1", " ", (v_map_1 == map[false := [true, false], true := [false, true]]), " ", "v_real_real_1.0", " ", (v_real_real_1.0 == -5.68), " ", "v_map_2", " ", (v_map_2 == map[true := 'U']), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_5", " ", (v_seq_5 == [v_real_real_16, v_real_real_17]), " ", "v_seq_3", " ", (v_seq_3 == [v_array_1, v_array_2]), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_real_1", " ", (v_real_1 == 19.21), " ", "v_bool_11", " ", v_bool_11, " ", "v_bool_10", " ", v_bool_10, " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
	}
	assert ((v_bool_7 == true));
	expect ((v_bool_7 == true));
	var v_real_real_18: (real, real) := (3.28, 28.21);
	var v_real_real_19: (real, real) := (-5.68, -15.36);
	var v_real_real_20: (real, real) := (-5.68, -15.36);
	var v_real_real_21: (real, real) := (17.62, 19.21);
	var v_real_real_22: (real, real) := (-5.68, -15.36);
	var v_real_real_23: (real, real) := (3.28, 28.21);
	print "v_bool_1", " ", v_bool_1, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_bool_9", " ", v_bool_9, " ", "v_bool_8", " ", v_bool_8, " ", "v_real_real_2", " ", (v_real_real_2 == v_real_real_18), " ", "v_real_real_1", " ", (v_real_real_1 == v_real_real_19), " ", "v_real_real_4", " ", (v_real_real_4 == v_real_real_20), " ", "v_bool_7", " ", v_bool_7, " ", "v_real_real_3", " ", (v_real_real_3 == v_real_real_21), " ", "v_array_6", " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_2), " ", "v_int_9", " ", v_int_9, " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_array_2[1]", " ", v_array_2[1], " ", "v_bool_int_bool_4", " ", v_bool_int_bool_4, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_bool_int_bool_3", " ", v_bool_int_bool_3, " ", "v_array_7", " ", (v_array_7 == v_array_2), " ", "v_array_8", " ", "v_array_1[4]", " ", v_array_1[4], " ", "v_char_1", " ", (v_char_1 == 'U'), " ", "v_int_7", " ", v_int_7, " ", "v_real_real_3.1", " ", (v_real_real_3.1 == 19.21), " ", "v_real_real_2.1", " ", (v_real_real_2.1 == 28.21), " ", "v_real_real_3.0", " ", (v_real_real_3.0 == 17.62), " ", "v_real_real_1.1", " ", (v_real_real_1.1 == -15.36), " ", "v_real_real_2.0", " ", (v_real_real_2.0 == 3.28), " ", "v_map_1", " ", (v_map_1 == map[false := [true, false], true := [false, true]]), " ", "v_real_real_1.0", " ", (v_real_real_1.0 == -5.68), " ", "v_map_2", " ", (v_map_2 == map[true := 'U']), " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_5", " ", (v_seq_5 == [v_real_real_22, v_real_real_23]), " ", "v_seq_3", " ", (v_seq_3 == [v_array_1, v_array_2]), " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_array_2[0]", " ", v_array_2[0], " ", "v_real_1", " ", (v_real_1 == 19.21), " ", "v_bool_11", " ", v_bool_11, " ", "v_bool_10", " ", v_bool_10, " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_array_2[2]", " ", v_array_2[2], "\n";
}
