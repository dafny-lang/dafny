// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
datatype DT_2<T_2, T_3> = DT_2_1
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

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char) returns (ret_1: char)
	requires ((p_m_method_3_1 == 'y') && (p_m_method_3_3 == 'S') && (p_m_method_3_2 == 'W')) || ((p_m_method_3_1 == 'w') && (p_m_method_3_3 == 'O') && (p_m_method_3_2 == 'w')) || ((p_m_method_3_1 == 'v') && (p_m_method_3_3 == 'D') && (p_m_method_3_2 == 'c')) || ((p_m_method_3_1 == 'r') && (p_m_method_3_3 == 'Q') && (p_m_method_3_2 == 'H')) || ((p_m_method_3_1 == 'P') && (p_m_method_3_3 == 'p') && (p_m_method_3_2 == 'w'));
	ensures (((p_m_method_3_1 == 'r') && (p_m_method_3_3 == 'Q') && (p_m_method_3_2 == 'H')) ==> ((ret_1 == 'H'))) && (((p_m_method_3_1 == 'w') && (p_m_method_3_3 == 'O') && (p_m_method_3_2 == 'w')) ==> ((ret_1 == 'w'))) && (((p_m_method_3_1 == 'y') && (p_m_method_3_3 == 'S') && (p_m_method_3_2 == 'W')) ==> ((ret_1 == 'W'))) && (((p_m_method_3_1 == 'P') && (p_m_method_3_3 == 'p') && (p_m_method_3_2 == 'w')) ==> ((ret_1 == 'w'))) && (((p_m_method_3_1 == 'v') && (p_m_method_3_3 == 'D') && (p_m_method_3_2 == 'c')) ==> ((ret_1 == 'c')));
{
	print "p_m_method_3_2", " ", (p_m_method_3_2 == 'H'), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'r'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'Q'), "\n";
	return p_m_method_3_2;
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

method m_method_2(p_m_method_2_1: char, p_m_method_2_2: char, p_m_method_2_3: char, p_m_method_2_4: char) returns (ret_1: bool, ret_2: char, ret_3: char, ret_4: char)
	requires ((p_m_method_2_2 == 'w') && (p_m_method_2_1 == 'w') && (p_m_method_2_4 == 'w') && (p_m_method_2_3 == 'c'));
	ensures (((p_m_method_2_2 == 'w') && (p_m_method_2_1 == 'w') && (p_m_method_2_4 == 'w') && (p_m_method_2_3 == 'c')) ==> ((ret_1 == true) && (ret_2 == 'c') && (ret_3 == 'w') && (ret_4 == 'w')));
{
	var v_map_1: map<char, int> := map['E' := 13, 'z' := -5, 'A' := 8];
	var v_char_1: char := 'r';
	var v_int_7: int := 12;
	var v_int_8: int := 29;
	var v_int_9: int := safe_modulus(v_int_7, v_int_8);
	print "v_char_1", " ", (v_char_1 == 'r'), " ", "p_m_method_2_1", " ", (p_m_method_2_1 == 'w'), " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "p_m_method_2_3", " ", (p_m_method_2_3 == 'c'), " ", "v_map_1", " ", (v_map_1 == map['A' := 8, 'E' := 13, 'z' := -5]), " ", "p_m_method_2_2", " ", (p_m_method_2_2 == 'w'), " ", "p_m_method_2_4", " ", (p_m_method_2_4 == 'w'), "\n";
	return ((if ((v_char_1 in v_map_1)) then (v_map_1[v_char_1]) else (29)) > v_int_9), p_m_method_2_3, p_m_method_2_4, p_m_method_2_4;
}

method m_method_1(p_m_method_1_1: char, p_m_method_1_2: int, p_m_method_1_3: int) returns (ret_1: bool)
	requires ((p_m_method_1_1 == 'H') && (p_m_method_1_3 == 28) && (p_m_method_1_2 == 11));
	ensures (((p_m_method_1_1 == 'H') && (p_m_method_1_3 == 28) && (p_m_method_1_2 == 11)) ==> ((ret_1 == true)));
{
	var v_char_2: char := 'P';
	var v_char_3: char := 'w';
	var v_char_4: char := 'p';
	var v_char_5: char := m_method_3(v_char_2, v_char_3, v_char_4);
	var v_char_6: char := v_char_5;
	var v_char_7: char := v_char_5;
	var v_char_8: char := (match 'r' {
		case 'j' => 'T'
		case _ => 'O'
	});
	var v_char_9: char := m_method_3(v_char_6, v_char_7, v_char_8);
	var v_char_14: char := v_char_9;
	var v_char_15: char := v_char_3;
	var v_char_10: char := 'v';
	var v_char_11: char := 'c';
	var v_char_12: char := 'D';
	var v_char_13: char := m_method_3(v_char_10, v_char_11, v_char_12);
	var v_char_16: char := (if (('F' in ['k', 'S'])) then ('l') else (v_char_13));
	var v_char_17: char := v_char_9;
	var v_bool_1: bool, v_char_18: char, v_char_19: char, v_char_20: char := m_method_2(v_char_14, v_char_15, v_char_16, v_char_17);
	v_bool_1, v_char_20, v_char_19, v_char_9 := v_bool_1, v_char_18, v_char_19, v_char_20;
	var v_map_2: map<char, bool> := map['Y' := false];
	var v_char_21: char := 'x';
	var v_map_3: map<char, char> := (map['G' := 'Q', 'q' := 'n', 'I' := 'M'] - {'j', 't'});
	var v_seq_3: seq<char> := ['E', 'G', 'w'];
	var v_int_10: int := 24;
	var v_seq_170: seq<char> := v_seq_3;
	var v_int_198: int := v_int_10;
	var v_int_199: int := safe_index_seq(v_seq_170, v_int_198);
	v_int_10 := v_int_199;
	var v_char_22: char := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_10]) else ('L'));
	v_char_17, v_char_19, v_char_14, v_char_12 := (if ((if ((v_char_21 in v_map_2)) then (v_map_2[v_char_21]) else (false))) then (p_m_method_1_1) else (v_char_18)), v_char_4, (if ((v_char_22 in v_map_3)) then (v_map_3[v_char_22]) else ((if (true) then ('r') else ('G')))), 'N';
	var v_seq_4: seq<char> := ['V'];
	var v_seq_5: seq<char> := v_seq_4;
	var v_int_12: int := 12;
	var v_int_13: int := safe_index_seq(v_seq_5, v_int_12);
	var v_int_14: int := v_int_13;
	var v_seq_6: seq<char> := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_14 := 'r']) else (v_seq_4));
	var v_map_4: map<char, int> := map['e' := 13, 'a' := 3];
	var v_char_23: char := 'F';
	var v_int_15: int := (if ((v_char_23 in v_map_4)) then (v_map_4[v_char_23]) else (-16));
	var v_int_16: int := safe_index_seq(v_seq_6, v_int_15);
	var v_int_26: int, v_int_27: int := v_int_16, p_m_method_1_3;
	for v_int_11 := v_int_26 to v_int_27 
		invariant (v_int_27 - v_int_11 >= 0) && ((((v_int_11 == 22)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 10)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 20)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 26)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 14)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 24)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 12)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 18)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 16)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 1)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 3)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 5)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 7)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 9)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 11)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 21)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 15)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 25)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 13)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 23)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 19)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 17)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 27)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 0)) ==> ((((v_char_19 == 'p')) && ((v_char_17 == 'c')) && ((v_char_8 == 'O')) && ((v_char_13 == 'c')) && ((v_char_22 == 'E'))))) && (((v_int_11 == 2)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 4)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 6)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))) && (((v_int_11 == 8)) ==> ((((v_char_19 == 'V')) && ((v_char_17 == 'W')) && ((v_char_8 == 'W')) && ((v_char_13 == 'E')) && ((v_char_22 == 'H'))))))
	{
		var v_seq_7: seq<char> := ['d'];
		var v_int_17: int := 10;
		var v_seq_171: seq<char> := v_seq_7;
		var v_int_200: int := v_int_17;
		var v_int_201: int := safe_index_seq(v_seq_171, v_int_200);
		v_int_17 := v_int_201;
		var v_char_24: char := 'y';
		var v_char_25: char := 'W';
		var v_char_26: char := 'S';
		var v_char_27: char := m_method_3(v_char_24, v_char_25, v_char_26);
		v_char_13, v_char_8, v_char_22 := (if ((match 'I' {
			case 'Y' => true
			case 'm' => true
			case _ => true
		})) then ((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_17]) else ('I'))) else (v_char_27)), v_char_27, p_m_method_1_1;
		assert ((v_seq_3 == ['E', 'G', 'w']) && (v_char_15 == 'w') && (v_int_10 == 0) && (v_int_12 == 12));
		expect ((v_seq_3 == ['E', 'G', 'w']) && (v_char_15 == 'w') && (v_int_10 == 0) && (v_int_12 == 12));
		var v_map_5: map<char, seq<char>> := map['h' := ['r', 'n', 'u', 'V'], 'X' := ['E'], 'F' := ['O', 'c', 'm'], 't' := ['e']];
		var v_char_28: char := 'g';
		var v_seq_8: seq<char> := (if ((v_char_28 in v_map_5)) then (v_map_5[v_char_28]) else (['W']));
		var v_int_18: int := (match 'j' {
			case 'V' => -17
			case _ => 12
		});
		var v_seq_173: seq<char> := v_seq_8;
		var v_int_204: int := v_int_18;
		var v_int_205: int := safe_index_seq(v_seq_173, v_int_204);
		v_int_18 := v_int_205;
		var v_seq_9: seq<char> := [];
		var v_int_19: int := 29;
		var v_seq_11: seq<char> := (['V', 'N', 'e', 'e'] + ['P', 't', 'q', 'k']);
		var v_seq_10: seq<int> := [26, 4, 6];
		var v_int_20: int := 12;
		var v_seq_172: seq<int> := v_seq_10;
		var v_int_202: int := v_int_20;
		var v_int_203: int := safe_index_seq(v_seq_172, v_int_202);
		v_int_20 := v_int_203;
		var v_int_21: int := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_20]) else (1));
		var v_seq_174: seq<char> := v_seq_11;
		var v_int_206: int := v_int_21;
		var v_int_207: int := safe_index_seq(v_seq_174, v_int_206);
		v_int_21 := v_int_207;
		var v_seq_12: seq<char> := ['o'];
		var v_seq_13: seq<char> := v_seq_12;
		var v_int_22: int := 29;
		var v_int_23: int := safe_index_seq(v_seq_13, v_int_22);
		var v_int_24: int := v_int_23;
		var v_seq_14: seq<char> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_24 := 'E']) else (v_seq_12));
		var v_map_6: map<char, int> := map['d' := 12, 'K' := 18];
		var v_char_29: char := 't';
		var v_int_25: int := (if ((v_char_29 in v_map_6)) then (v_map_6[v_char_29]) else (-16));
		var v_seq_175: seq<char> := v_seq_14;
		var v_int_208: int := v_int_25;
		var v_int_209: int := safe_index_seq(v_seq_175, v_int_208);
		v_int_25 := v_int_209;
		v_char_29, v_char_17, v_char_27, v_char_19, v_char_13 := v_char_24, (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_18]) else ((if ((|v_seq_9| > 0)) then (v_seq_9[v_int_19]) else ('a')))), v_char_16, (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_21]) else (v_char_12)), (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_25]) else ((match 'Q' {
			case _ => 'm'
		})));
		print "v_char_17", " ", (v_char_17 == 'W'), " ", "v_char_13", " ", (v_char_13 == 'E'), " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_char_19", " ", (v_char_19 == 'V'), " ", "v_int_24", " ", v_int_24, " ", "v_seq_14", " ", (v_seq_14 == ['E']), " ", "v_int_23", " ", v_int_23, " ", "v_int_22", " ", v_int_22, " ", "v_int_21", " ", v_int_21, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", (v_seq_11 == ['V', 'N', 'e', 'e', 'P', 't', 'q', 'k']), " ", "v_seq_12", " ", (v_seq_12 == ['o']), " ", "v_seq_13", " ", (v_seq_13 == ['o']), " ", "v_int_25", " ", v_int_25, " ", "v_int_20", " ", v_int_20, " ", "v_map_5", " ", (v_map_5 == map['t' := ['e'], 'F' := ['O', 'c', 'm'], 'h' := ['r', 'n', 'u', 'V'], 'X' := ['E']]), " ", "v_char_29", " ", (v_char_29 == 'y'), " ", "v_char_28", " ", (v_char_28 == 'g'), " ", "v_char_27", " ", (v_char_27 == 'c'), " ", "v_char_26", " ", (v_char_26 == 'S'), " ", "v_map_6", " ", (v_map_6 == map['d' := 12, 'K' := 18]), " ", "v_char_25", " ", (v_char_25 == 'W'), " ", "v_char_24", " ", (v_char_24 == 'y'), " ", "v_char_22", " ", (v_char_22 == 'H'), " ", "v_char_8", " ", (v_char_8 == 'W'), " ", "v_seq_9", " ", (v_seq_9 == []), " ", "v_seq_8", " ", (v_seq_8 == ['W']), " ", "v_seq_7", " ", (v_seq_7 == ['d']), " ", "v_int_11", " ", v_int_11, " ", "v_int_17", " ", v_int_17, " ", "v_bool_1", " ", v_bool_1, " ", "v_char_18", " ", (v_char_18 == 'c'), " ", "v_char_17", " ", (v_char_17 == 'W'), " ", "v_char_16", " ", (v_char_16 == 'c'), " ", "v_char_15", " ", (v_char_15 == 'w'), " ", "v_char_14", " ", (v_char_14 == 'r'), " ", "v_char_13", " ", (v_char_13 == 'E'), " ", "v_char_12", " ", (v_char_12 == 'N'), " ", "v_char_11", " ", (v_char_11 == 'c'), " ", "v_char_19", " ", (v_char_19 == 'V'), " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'H'), " ", "v_char_21", " ", (v_char_21 == 'x'), " ", "v_char_20", " ", (v_char_20 == 'c'), " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_map_4", " ", (v_map_4 == map['a' := 3, 'e' := 13]), " ", "v_char_3", " ", (v_char_3 == 'w'), " ", "v_char_2", " ", (v_char_2 == 'P'), " ", "v_char_5", " ", (v_char_5 == 'w'), " ", "v_char_4", " ", (v_char_4 == 'p'), " ", "v_char_7", " ", (v_char_7 == 'w'), " ", "v_char_23", " ", (v_char_23 == 'F'), " ", "v_char_6", " ", (v_char_6 == 'w'), " ", "v_char_22", " ", (v_char_22 == 'H'), " ", "v_char_9", " ", (v_char_9 == 'w'), " ", "v_char_8", " ", (v_char_8 == 'W'), " ", "v_map_3", " ", (v_map_3 == map['q' := 'n', 'G' := 'Q', 'I' := 'M']), " ", "v_map_2", " ", (v_map_2 == map['Y' := false]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_6", " ", (v_seq_6 == ['r']), " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", (v_seq_5 == ['V']), " ", "v_seq_4", " ", (v_seq_4 == ['V']), " ", "v_seq_3", " ", (v_seq_3 == ['E', 'G', 'w']), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_char_10", " ", (v_char_10 == 'v'), "\n";
	}
	var v_seq_16: seq<char> := v_seq_4;
	var v_seq_15: seq<int> := [];
	var v_int_28: int := 12;
	var v_int_29: int := (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_28]) else (15));
	var v_seq_176: seq<char> := v_seq_16;
	var v_int_210: int := v_int_29;
	var v_int_211: int := safe_index_seq(v_seq_176, v_int_210);
	v_int_29 := v_int_211;
	var v_map_7: map<char, map<char, char>> := map['q' := map['W' := 'S', 'C' := 'f'], 'u' := map['W' := 'V', 'g' := 'i', 'L' := 'G'], 'n' := map['P' := 'G', 'l' := 't', 'T' := 's', 'a' := 'z'], 'o' := map['J' := 'a', 'q' := 'o', 'w' := 'm', 'T' := 'M', 'v' := 't'], 'H' := map['w' := 'y', 'o' := 'P', 's' := 'C', 'E' := 'Z']];
	var v_char_30: char := 'O';
	var v_map_8: map<char, char> := (if ((v_char_30 in v_map_7)) then (v_map_7[v_char_30]) else (map['A' := 'C', 'y' := 'm', 'r' := 'N', 'S' := 'G']));
	var v_char_31: char := (if (false) then ('e') else ('E'));
	var v_map_9: map<char, char> := map['v' := 'k', 'a' := 'D', 'C' := 'S', 'b' := 'A'];
	var v_char_32: char := 'J';
	var v_map_10: map<char, char> := map['D' := 'c', 'l' := 'O', 'R' := 'E', 'e' := 'R', 'p' := 'G'];
	var v_char_33: char := 'a';
	v_char_17, v_char_21, v_char_16, v_char_12 := (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_29]) else ((match 'A' {
		case _ => 'u'
	}))), (if ((v_char_31 in v_map_8)) then (v_map_8[v_char_31]) else ((match 'e' {
		case 'K' => 'f'
		case 'l' => 'o'
		case _ => 'f'
	}))), v_char_23, (if (v_bool_1) then ((if ((v_char_32 in v_map_9)) then (v_map_9[v_char_32]) else ('V'))) else ((if ((v_char_33 in v_map_10)) then (v_map_10[v_char_33]) else ('d'))));
	if v_bool_1 {
		var v_seq_17: seq<map<char, char>> := [map['P' := 'R', 's' := 'x', 'W' := 'l'], map['g' := 'U']];
		var v_int_30: int := 8;
		var v_seq_177: seq<map<char, char>> := v_seq_17;
		var v_int_212: int := v_int_30;
		var v_int_213: int := safe_index_seq(v_seq_177, v_int_212);
		v_int_30 := v_int_213;
		var v_map_11: map<char, char> := (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_30]) else (map['U' := 'g', 't' := 'l']));
		var v_char_34: char := v_char_13;
		var v_seq_18: seq<char> := ['W', 'x'];
		var v_int_31: int := 13;
		var v_seq_178: seq<char> := v_seq_18;
		var v_int_214: int := v_int_31;
		var v_int_215: int := safe_index_seq(v_seq_178, v_int_214);
		v_int_31 := v_int_215;
		v_char_31, v_char_33, v_char_18, v_char_19, v_char_8 := v_char_3, (if ((v_char_34 in v_map_11)) then (v_map_11[v_char_34]) else ((if ((|v_seq_18| > 0)) then (v_seq_18[v_int_31]) else ('Z')))), v_char_2, v_char_21, v_char_7;
		print "v_char_18", " ", (v_char_18 == 'P'), " ", "v_seq_17", " ", (v_seq_17 == [map['P' := 'R', 's' := 'x', 'W' := 'l'], map['g' := 'U']]), " ", "v_char_34", " ", (v_char_34 == 'E'), " ", "v_char_33", " ", (v_char_33 == 'W'), " ", "v_char_31", " ", (v_char_31 == 'w'), " ", "v_char_8", " ", (v_char_8 == 'w'), " ", "v_map_11", " ", (v_map_11 == map['P' := 'R', 's' := 'x', 'W' := 'l']), " ", "v_seq_18", " ", (v_seq_18 == ['W', 'x']), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, " ", "v_char_19", " ", (v_char_19 == 'f'), " ", "v_char_33", " ", (v_char_33 == 'W'), " ", "v_map_10", " ", (v_map_10 == map['p' := 'G', 'R' := 'E', 'D' := 'c', 'e' := 'R', 'l' := 'O']), " ", "v_char_23", " ", (v_char_23 == 'F'), " ", "v_char_22", " ", (v_char_22 == 'H'), " ", "v_int_29", " ", v_int_29, " ", "v_char_32", " ", (v_char_32 == 'J'), " ", "v_char_31", " ", (v_char_31 == 'w'), " ", "v_char_30", " ", (v_char_30 == 'O'), " ", "v_bool_1", " ", v_bool_1, " ", "v_char_18", " ", (v_char_18 == 'P'), " ", "v_char_17", " ", (v_char_17 == 'V'), " ", "v_char_16", " ", (v_char_16 == 'F'), " ", "v_char_15", " ", (v_char_15 == 'w'), " ", "v_char_14", " ", (v_char_14 == 'r'), " ", "v_char_13", " ", (v_char_13 == 'E'), " ", "v_char_12", " ", (v_char_12 == 'V'), " ", "v_char_11", " ", (v_char_11 == 'c'), " ", "v_char_19", " ", (v_char_19 == 'f'), " ", "v_seq_15", " ", v_seq_15, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "v_seq_16", " ", (v_seq_16 == ['V']), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'H'), " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_char_21", " ", (v_char_21 == 'f'), " ", "v_char_20", " ", (v_char_20 == 'c'), " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_map_4", " ", (v_map_4 == map['a' := 3, 'e' := 13]), " ", "v_char_3", " ", (v_char_3 == 'w'), " ", "v_map_7", " ", (v_map_7 == map['q' := map['C' := 'f', 'W' := 'S'], 'u' := map['W' := 'V', 'g' := 'i', 'L' := 'G'], 'H' := map['s' := 'C', 'E' := 'Z', 'w' := 'y', 'o' := 'P'], 'n' := map['P' := 'G', 'a' := 'z', 'T' := 's', 'l' := 't'], 'o' := map['q' := 'o', 'T' := 'M', 'v' := 't', 'w' := 'm', 'J' := 'a']]), " ", "v_char_2", " ", (v_char_2 == 'P'), " ", "v_char_5", " ", (v_char_5 == 'w'), " ", "v_map_9", " ", (v_map_9 == map['a' := 'D', 'b' := 'A', 'C' := 'S', 'v' := 'k']), " ", "v_char_4", " ", (v_char_4 == 'p'), " ", "v_map_8", " ", (v_map_8 == map['A' := 'C', 'r' := 'N', 'S' := 'G', 'y' := 'm']), " ", "v_char_7", " ", (v_char_7 == 'w'), " ", "v_char_6", " ", (v_char_6 == 'w'), " ", "v_char_9", " ", (v_char_9 == 'w'), " ", "v_char_8", " ", (v_char_8 == 'w'), " ", "v_map_3", " ", (v_map_3 == map['q' := 'n', 'G' := 'Q', 'I' := 'M']), " ", "v_map_2", " ", (v_map_2 == map['Y' := false]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_6", " ", (v_seq_6 == ['r']), " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", (v_seq_5 == ['V']), " ", "v_seq_4", " ", (v_seq_4 == ['V']), " ", "v_seq_3", " ", (v_seq_3 == ['E', 'G', 'w']), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_char_10", " ", (v_char_10 == 'v'), "\n";
	} else {
		var v_seq_19: seq<bool> := [false, false, false];
		var v_int_32: int := 23;
		if (match 'Y' {
			case _ => ([] == ['q', 'Q'])
		}) {
			var v_seq_20: seq<bool> := [false, true];
			var v_seq_21: seq<bool> := v_seq_20;
			var v_int_33: int := -12;
			var v_int_34: int := safe_index_seq(v_seq_21, v_int_33);
			var v_int_35: int := v_int_34;
			var v_seq_22: seq<bool> := (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_35 := true]) else (v_seq_20));
			var v_int_36: int := v_int_35;
			if (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_36]) else ((if (false) then (true) else (false)))) {
				return v_bool_1;
			} else {
				
			}
			var v_seq_23: seq<bool> := [false, true, true, false];
			var v_int_37: int := 11;
			var v_map_12: map<char, char> := map['i' := 'j', 'T' := 'A'];
			var v_char_35: char := 'S';
			v_char_4, v_char_10, v_char_2 := (if ((if ((|v_seq_23| > 0)) then (v_seq_23[v_int_37]) else (false))) then ((if (true) then ('i') else ('w'))) else (v_char_30)), v_char_33, (if ((if (true) then (true) else (true))) then (v_char_19) else ((if ((v_char_35 in v_map_12)) then (v_map_12[v_char_35]) else ('q'))));
			if ((match 'V' {
				case _ => false
			}) && v_bool_1) {
				return (match 'n' {
					case _ => v_bool_1
				});
			} else {
				return (if (v_bool_1) then ((if (false) then (true) else (true))) else (v_bool_1));
			}
		} else {
			
		}
		return v_bool_1;
	}
	var v_map_14: map<char, bool> := v_map_2;
	var v_map_13: map<char, char> := map['U' := 's', 'v' := 'Y', 'R' := 'Z'];
	var v_char_36: char := 'Z';
	var v_char_37: char := (if ((v_char_36 in v_map_13)) then (v_map_13[v_char_36]) else ('b'));
	var v_seq_24: seq<bool> := [true, true, false, false];
	var v_int_38: int := -28;
	var v_seq_179: seq<bool> := v_seq_24;
	var v_int_216: int := v_int_38;
	var v_int_217: int := safe_index_seq(v_seq_179, v_int_216);
	v_int_38 := v_int_217;
	if (if ((v_char_37 in v_map_14)) then (v_map_14[v_char_37]) else ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_38]) else (true)))) {
		var v_map_15: map<char, char> := map['N' := 'c'];
		var v_char_38: char := 'N';
		var v_map_16: map<char, map<char, char>> := map['q' := map['r' := 'Z', 'Y' := 'q', 's' := 'o']];
		var v_char_39: char := 'P';
		print "v_char_39", " ", (v_char_39 == 'P'), " ", "v_char_38", " ", (v_char_38 == 'N'), " ", "v_map_15", " ", (v_map_15 == map['N' := 'c']), " ", "v_map_16", " ", (v_map_16 == map['q' := map['r' := 'Z', 's' := 'o', 'Y' := 'q']]), " ", "v_char_37", " ", (v_char_37 == 'b'), " ", "v_char_36", " ", (v_char_36 == 'Z'), " ", "v_char_33", " ", (v_char_33 == 'W'), " ", "v_map_13", " ", (v_map_13 == map['R' := 'Z', 'U' := 's', 'v' := 'Y']), " ", "v_map_14", " ", (v_map_14 == map['Y' := false]), " ", "v_map_10", " ", (v_map_10 == map['p' := 'G', 'R' := 'E', 'D' := 'c', 'e' := 'R', 'l' := 'O']), " ", "v_char_23", " ", (v_char_23 == 'F'), " ", "v_char_22", " ", (v_char_22 == 'H'), " ", "v_int_29", " ", v_int_29, " ", "v_int_38", " ", v_int_38, " ", "v_seq_24", " ", v_seq_24, " ", "v_char_32", " ", (v_char_32 == 'J'), " ", "v_char_31", " ", (v_char_31 == 'w'), " ", "v_char_30", " ", (v_char_30 == 'O'), " ", "v_bool_1", " ", v_bool_1, " ", "v_char_18", " ", (v_char_18 == 'P'), " ", "v_char_17", " ", (v_char_17 == 'V'), " ", "v_char_16", " ", (v_char_16 == 'F'), " ", "v_char_15", " ", (v_char_15 == 'w'), " ", "v_char_14", " ", (v_char_14 == 'r'), " ", "v_char_13", " ", (v_char_13 == 'E'), " ", "v_char_12", " ", (v_char_12 == 'V'), " ", "v_char_11", " ", (v_char_11 == 'c'), " ", "v_char_19", " ", (v_char_19 == 'f'), " ", "v_seq_15", " ", v_seq_15, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "v_seq_16", " ", (v_seq_16 == ['V']), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'H'), " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_char_21", " ", (v_char_21 == 'f'), " ", "v_char_20", " ", (v_char_20 == 'c'), " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_map_4", " ", (v_map_4 == map['a' := 3, 'e' := 13]), " ", "v_char_3", " ", (v_char_3 == 'w'), " ", "v_map_7", " ", (v_map_7 == map['q' := map['C' := 'f', 'W' := 'S'], 'u' := map['W' := 'V', 'g' := 'i', 'L' := 'G'], 'H' := map['s' := 'C', 'E' := 'Z', 'w' := 'y', 'o' := 'P'], 'n' := map['P' := 'G', 'a' := 'z', 'T' := 's', 'l' := 't'], 'o' := map['q' := 'o', 'T' := 'M', 'v' := 't', 'w' := 'm', 'J' := 'a']]), " ", "v_char_2", " ", (v_char_2 == 'P'), " ", "v_char_5", " ", (v_char_5 == 'w'), " ", "v_map_9", " ", (v_map_9 == map['a' := 'D', 'b' := 'A', 'C' := 'S', 'v' := 'k']), " ", "v_char_4", " ", (v_char_4 == 'p'), " ", "v_map_8", " ", (v_map_8 == map['A' := 'C', 'r' := 'N', 'S' := 'G', 'y' := 'm']), " ", "v_char_7", " ", (v_char_7 == 'w'), " ", "v_char_6", " ", (v_char_6 == 'w'), " ", "v_char_9", " ", (v_char_9 == 'w'), " ", "v_char_8", " ", (v_char_8 == 'w'), " ", "v_map_3", " ", (v_map_3 == map['q' := 'n', 'G' := 'Q', 'I' := 'M']), " ", "v_map_2", " ", (v_map_2 == map['Y' := false]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_seq_6", " ", (v_seq_6 == ['r']), " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", (v_seq_5 == ['V']), " ", "v_seq_4", " ", (v_seq_4 == ['V']), " ", "v_seq_3", " ", (v_seq_3 == ['E', 'G', 'w']), " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_char_10", " ", (v_char_10 == 'v'), "\n";
		return ((if ((v_char_38 in v_map_15)) then (v_map_15[v_char_38]) else ('R')) !in (if ((v_char_39 in v_map_16)) then (v_map_16[v_char_39]) else (map['d' := 'A', 'H' := 'm'])));
	}
	assert true;
	expect true;
	v_char_3, v_char_15 := v_char_36, v_char_20;
	var v_map_17: map<char, bool> := map['x' := false, 'R' := false, 'X' := false, 'X' := true];
	var v_char_40: char := 't';
	var v_map_18: map<char, bool> := map['B' := true, 'Z' := false];
	var v_char_41: char := 'g';
	return (match 't' {
		case _ => (if ((v_char_41 in v_map_18)) then (v_map_18[v_char_41]) else (false))
	});
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_25: seq<char> := [];
	var v_int_39: int := 29;
	var v_char_43: char := (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_39]) else ('r'));
	var v_seq_26: seq<char> := [];
	var v_int_40: int := 8;
	var v_char_44: char := (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_40]) else ('H'));
	var v_map_19: map<char, char> := map['I' := 'k'];
	var v_char_42: char := 'K';
	var v_char_45: char := (if ((v_char_42 in v_map_19)) then (v_map_19[v_char_42]) else ('Q'));
	var v_char_46: char := m_method_3(v_char_43, v_char_44, v_char_45);
	var v_char_48: char := v_char_46;
	var v_seq_27: seq<int> := (if (true) then ([11]) else ([]));
	var v_int_41: int := (-13.51).Floor;
	var v_seq_169: seq<int> := v_seq_27;
	var v_int_196: int := v_int_41;
	var v_int_197: int := safe_index_seq(v_seq_169, v_int_196);
	v_int_41 := v_int_197;
	var v_int_43: int := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_41]) else ((match 'B' {
		case _ => 1
	})));
	var v_seq_28: seq<int> := (match 'I' {
		case 'x' => [25, 5, 24, 18]
		case _ => []
	});
	var v_int_42: int := v_int_39;
	var v_map_20: map<char, int> := map['g' := 7, 'C' := 19];
	var v_char_47: char := 'I';
	var v_int_44: int := (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_42]) else ((if ((v_char_47 in v_map_20)) then (v_map_20[v_char_47]) else (28))));
	var v_bool_2: bool := m_method_1(v_char_48, v_int_43, v_int_44);
	var v_DT_1_1_1: DT_1<DT_2<bool, int>> := DT_1_1;
	var v_DT_1_1_2: DT_1<DT_2<bool, int>> := DT_1_1;
	var v_DT_1_1_3: DT_1<DT_2<bool, int>> := DT_1_1;
	var v_DT_1_1_4: DT_1<DT_2<bool, int>> := DT_1_1;
	var v_DT_1_1_5: DT_1<DT_2<bool, int>> := DT_1_1;
	var v_map_23: map<char, DT_1<DT_2<bool, int>>> := (map['G' := v_DT_1_1_1, 'Q' := v_DT_1_1_2, 'T' := v_DT_1_1_3, 'W' := v_DT_1_1_4]['X' := v_DT_1_1_5] - ({'t'} * {'t', 'p', 'p', 'g'}));
	var v_map_22: map<char, char> := v_map_19;
	var v_seq_29: seq<char> := ['h', 'a', 'r'];
	var v_int_45: int := 15;
	var v_seq_180: seq<char> := v_seq_29;
	var v_int_218: int := v_int_45;
	var v_int_219: int := safe_index_seq(v_seq_180, v_int_218);
	v_int_45 := v_int_219;
	var v_char_50: char := (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_45]) else ('W'));
	var v_map_21: map<char, char> := map['l' := 'g'];
	var v_char_49: char := 'd';
	var v_char_51: char := (if ((v_char_50 in v_map_22)) then (v_map_22[v_char_50]) else ((if ((v_char_49 in v_map_21)) then (v_map_21[v_char_49]) else ('o'))));
	var v_bool_3: bool, v_DT_1_1_6: DT_1<DT_2<bool, int>>, v_bool_4: bool := v_bool_2, (if ((v_char_51 in v_map_23)) then (v_map_23[v_char_51]) else (v_DT_1_1_3)), v_bool_2;
	var v_map_24: map<char, char> := (match 'L' {
		case 'L' => map['z' := 'n', 'e' := 'Z', 'q' := 'T', 's' := 't', 'i' := 'i']
		case 'x' => map['G' := 'G']
		case _ => map['F' := 'K', 'B' := 'u']
	});
	var v_char_52: char := (if (false) then ('W') else ('c'));
	var v_seq_30: seq<char> := ['A', 'K', 'r', 'g'];
	var v_int_46: int := 25;
	match (match 'd' {
		case 'F' => v_char_42
		case 't' => (if ((v_char_52 in v_map_24)) then (v_map_24[v_char_52]) else ((if (false) then ('S') else ('Z'))))
		case _ => (match 'G' {
			case 'W' => v_char_46
			case 'o' => (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_46]) else ('a'))
			case _ => v_char_42
		})
	}) {
		case 'J' => {
			var v_seq_31: seq<char> := ['l'];
			var v_seq_32: seq<char> := ['w'];
			var v_seq_33: seq<char> := (match 'I' {
				case _ => (['G', 'z', 'a', 'M'] + [])
			});
			var v_int_47: int := ((20 - 0) % v_int_43);
			v_char_44 := (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_47]) else ((match 'V' {
				case _ => v_char_49
			})));
		}
			case _ => {
			var v_map_25: map<char, set<char>> := map['r' := {'Q'}];
			var v_char_53: char := 'a';
			var v_map_26: map<char, char> := map['I' := 'i', 'V' := 'e', 'y' := 'a', 'F' := 'J'];
			var v_char_54: char := 'p';
			var v_seq_34: seq<bool> := [true];
			var v_int_48: int := -16;
			var v_map_27: map<char, bool> := map['p' := true, 'y' := false, 'm' := false, 'Y' := false, 'Q' := true];
			var v_char_55: char := 'E';
			if (if (((if ((v_char_53 in v_map_25)) then (v_map_25[v_char_53]) else ({'y'})) != (match 'i' {
				case 'b' => {}
				case 'v' => {'c', 'J'}
				case _ => {'e', 'K', 'm'}
			}))) then (((if ((v_char_54 in v_map_26)) then (v_map_26[v_char_54]) else ('c')) !in (map['C' := 'O', 'W' := 'b', 'U' := 'a'] - {'P', 'g', 'b'}))) else ((if (({'d', 'i'} > {'R'})) then ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_48]) else (true))) else ((if ((v_char_55 in v_map_27)) then (v_map_27[v_char_55]) else (false)))))) {
				var v_seq_35: seq<char> := (match 'h' {
					case 'U' => ['Q', 'K', 'B']
					case _ => []
				});
				var v_seq_36: seq<char> := v_seq_35;
				var v_int_49: int := v_int_44;
				var v_int_50: int := safe_index_seq(v_seq_36, v_int_49);
				var v_int_51: int := v_int_50;
				var v_seq_38: seq<char> := (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_51 := (match 'M' {
					case _ => 't'
				})]) else (v_seq_35));
				var v_seq_37: seq<int> := [];
				var v_int_52: int := 16;
				var v_int_53: int := (match 'w' {
					case 'W' => (if (true) then (19) else (3))
					case 'q' => v_int_42
					case _ => (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_52]) else (26))
				});
				var v_map_28: map<char, bool> := map['Z' := true, 'C' := true, 'D' := false, 'J' := true];
				var v_char_56: char := 'u';
				var v_seq_39: seq<char> := ['X', 'd', 'N'];
				var v_int_54: int := 9;
				match (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_53]) else ((if ((if ((v_char_56 in v_map_28)) then (v_map_28[v_char_56]) else (false))) then ((if ((|v_seq_39| > 0)) then (v_seq_39[v_int_54]) else ('P'))) else (v_char_51)))) {
					case 'x' => {
						
					}
						case _ => {
						var v_seq_40: seq<seq<char>> := [[]];
						var v_int_55: int := 17;
						var v_seq_181: seq<seq<char>> := v_seq_40;
						var v_int_220: int := v_int_55;
						var v_int_221: int := safe_index_seq(v_seq_181, v_int_220);
						v_int_55 := v_int_221;
						var v_seq_41: seq<char> := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_55]) else (['Y']));
						var v_int_56: int := (6 % 11);
						var v_map_29: map<char, char> := map['O' := 'a', 'b' := 'l'];
						var v_char_57: char := 'R';
						var v_seq_42: seq<char> := ['k', 'C'];
						var v_int_57: int := 28;
						var v_map_30: map<char, char> := map['a' := 'H', 't' := 'z', 'L' := 'L']['l' := 'c'];
						var v_char_58: char := (if (false) then ('o') else ('V'));
						var v_seq_43: seq<seq<char>> := v_seq_40;
						var v_int_58: int := (if (true) then (13) else (24));
						var v_seq_182: seq<seq<char>> := v_seq_43;
						var v_int_222: int := v_int_58;
						var v_int_223: int := safe_index_seq(v_seq_182, v_int_222);
						v_int_58 := v_int_223;
						var v_seq_44: seq<char> := [];
						var v_seq_45: seq<char> := v_seq_44;
						var v_int_59: int := 22;
						var v_int_60: int := safe_index_seq(v_seq_45, v_int_59);
						var v_int_61: int := v_int_60;
						var v_seq_48: seq<char> := (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_58]) else ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_61 := 'Z']) else (v_seq_44))));
						var v_seq_46: seq<int> := [23];
						var v_seq_183: seq<int> := v_seq_46;
						var v_int_226: int := 15;
						var v_int_227: int := 0;
						var v_int_228: int, v_int_229: int := safe_subsequence(v_seq_183, v_int_226, v_int_227);
						var v_int_224: int, v_int_225: int := v_int_228, v_int_229;
						var v_seq_47: seq<int> := (if ((|v_seq_46| > 0)) then (v_seq_46[v_int_224..v_int_225]) else (v_seq_46));
						var v_int_62: int := (match 'J' {
							case 'b' => 12
							case _ => 4
						});
						var v_int_63: int := (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_62]) else ((28.25).Floor));
						v_char_54, v_char_42, v_char_53, v_char_44, v_char_49 := (if ((if ((multiset({'h', 'b', 'k'}) != multiset{'E', 'k', 'G'})) then (!(false)) else ((if (true) then (true) else (false))))) then ((if ((|v_seq_41| > 0)) then (v_seq_41[v_int_56]) else ((if (true) then ('k') else ('W'))))) else ((if ((false ==> false)) then ((if ((v_char_57 in v_map_29)) then (v_map_29[v_char_57]) else ('q'))) else ((if ((|v_seq_42| > 0)) then (v_seq_42[v_int_57]) else ('d')))))), (match 'x' {
							case 'k' => v_char_54
							case 'o' => v_char_56
							case _ => (if ((v_char_58 in v_map_30)) then (v_map_30[v_char_58]) else ((match 'U' {
								case 'G' => 'C'
								case _ => 'Y'
							})))
						}), v_char_48, v_char_43, (if ((|v_seq_48| > 0)) then (v_seq_48[v_int_63]) else (v_char_57));
						var v_seq_50: seq<char> := v_seq_44;
						var v_map_31: map<char, int> := map['c' := 12, 'g' := -20, 'p' := 0, 'e' := 24, 'm' := 13]['g' := 23];
						var v_seq_49: seq<char> := ['H', 'c'];
						var v_int_64: int := 0;
						var v_char_59: char := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_64]) else ('c'));
						var v_int_65: int := (if ((v_char_59 in v_map_31)) then (v_map_31[v_char_59]) else ((match 'h' {
							case 'k' => 25
							case 'F' => 7
							case _ => 13
						})));
						var v_seq_51: seq<char> := ['W', 'L', 'G', 't'];
						var v_seq_52: seq<char> := (if ((|v_seq_51| > 0)) then (v_seq_51[1..2]) else (v_seq_51));
						var v_int_66: int := v_int_54;
						var v_seq_186: seq<char> := v_seq_52;
						var v_int_234: int := v_int_66;
						var v_int_235: int := safe_index_seq(v_seq_186, v_int_234);
						v_int_66 := v_int_235;
						var v_seq_53: seq<char> := ['d', 'n', 'Y'];
						var v_seq_54: seq<char> := v_seq_53;
						var v_int_67: int := 3;
						var v_int_68: int := safe_index_seq(v_seq_54, v_int_67);
						var v_int_69: int := v_int_68;
						var v_seq_55: seq<char> := (if ((|v_seq_53| > 0)) then (v_seq_53[v_int_69 := 'x']) else (v_seq_53));
						var v_int_70: int := |{'N', 'e', 'd', 'u'}|;
						var v_seq_56: seq<char> := [];
						var v_int_71: int := 28;
						var v_map_32: map<char, char> := map['q' := 'P', 'h' := 'V', 'p' := 'n', 'X' := 'Q'];
						var v_char_60: char := 'X';
						var v_seq_57: seq<map<char, char>> := [map['k' := 'S', 'U' := 'M', 'E' := 'O', 'B' := 'Y'], map['T' := 'N', 'l' := 'U', 'g' := 'd', 'n' := 'f', 'm' := 'i'], map['D' := 'H', 'h' := 'G', 'Q' := 'X']];
						var v_int_72: int := 23;
						var v_seq_184: seq<map<char, char>> := v_seq_57;
						var v_int_230: int := v_int_72;
						var v_int_231: int := safe_index_seq(v_seq_184, v_int_230);
						v_int_72 := v_int_231;
						var v_map_33: map<char, char> := (if ((|v_seq_57| > 0)) then (v_seq_57[v_int_72]) else (map['Q' := 'Z', 'E' := 'X', 'F' := 'z', 'm' := 'D']));
						var v_seq_58: seq<char> := ['B', 'E'];
						var v_int_73: int := 23;
						var v_seq_185: seq<char> := v_seq_58;
						var v_int_232: int := v_int_73;
						var v_int_233: int := safe_index_seq(v_seq_185, v_int_232);
						v_int_73 := v_int_233;
						var v_char_61: char := (if ((|v_seq_58| > 0)) then (v_seq_58[v_int_73]) else ('t'));
						var v_seq_59: seq<bool> := [];
						var v_int_74: int := 13;
						var v_map_34: map<char, char> := map['Q' := 'q'];
						var v_char_62: char := 'n';
						var v_map_35: map<char, char> := map['t' := 'E', 'I' := 'B', 'P' := 'K', 'g' := 's'];
						var v_char_63: char := 'a';
						v_char_53, v_char_54, v_char_49 := (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_65]) else ((if ((|v_seq_52| > 0)) then (v_seq_52[v_int_66]) else (v_char_50)))), (if ((v_char_50 == v_char_42)) then ((if ((|v_seq_55| > 0)) then (v_seq_55[v_int_70]) else ((if ((|v_seq_56| > 0)) then (v_seq_56[v_int_71]) else ('h'))))) else ((if (v_bool_3) then ((match 'H' {
							case 'h' => 'K'
							case 'k' => 'Z'
							case _ => 'y'
						})) else ((if ((v_char_60 in v_map_32)) then (v_map_32[v_char_60]) else ('E')))))), (match 'o' {
							case 'k' => (match 'M' {
								case _ => v_char_53
							})
							case 'i' => (if ((v_char_61 in v_map_33)) then (v_map_33[v_char_61]) else ((if (false) then ('n') else ('m'))))
							case _ => (if ((if ((|v_seq_59| > 0)) then (v_seq_59[v_int_74]) else (false))) then ((if ((v_char_62 in v_map_34)) then (v_map_34[v_char_62]) else ('f'))) else ((if ((v_char_63 in v_map_35)) then (v_map_35[v_char_63]) else ('P'))))
						});
						var v_DT_1_1_7: DT_1<DT_2<bool, int>> := DT_1_1;
						assert ((v_seq_39 == ['X', 'd', 'N']) && (v_char_60 == 'X') && (v_DT_1_1_4 == v_DT_1_1_7) && (v_int_68 == 0));
						expect ((v_seq_39 == ['X', 'd', 'N']) && (v_char_60 == 'X') && (v_DT_1_1_4 == v_DT_1_1_7) && (v_int_68 == 0));
						var v_seq_60: seq<char> := ['P', 'X'];
						var v_seq_61: seq<char> := ['t'];
						var v_seq_62: seq<char> := v_seq_61;
						var v_int_75: int := 21;
						var v_int_76: int := safe_index_seq(v_seq_62, v_int_75);
						var v_int_77: int := v_int_76;
						if (if ((v_bool_3 || (if (true) then (true) else (false)))) then (v_bool_3) else (((if ((|v_seq_60| > 0)) then (v_seq_60[4..-14]) else (v_seq_60)) == (if ((|v_seq_61| > 0)) then (v_seq_61[v_int_77 := 'J']) else (v_seq_61))))) {
							
						} else {
							
						}
						assert ((v_char_49 == 'P') && (v_seq_44 == []) && (v_seq_35 == []) && (v_int_49 == 28));
						expect ((v_char_49 == 'P') && (v_seq_44 == []) && (v_seq_35 == []) && (v_int_49 == 28));
						var v_DT_1_1_8: DT_1<DT_2<bool, int>> := DT_1_1;
						var v_DT_1_1_9: DT_1<DT_2<bool, int>> := DT_1_1;
						var v_DT_1_1_10: DT_1<DT_2<bool, int>> := DT_1_1;
						var v_DT_1_1_11: DT_1<DT_2<bool, int>> := DT_1_1;
						var v_DT_1_1_12: DT_1<DT_2<bool, int>> := DT_1_1;
						print "v_char_42", " ", (v_char_42 == 'Y'), " ", "v_int_77", " ", v_int_77, " ", "v_int_76", " ", v_int_76, " ", "v_map_29", " ", (v_map_29 == map['b' := 'l', 'O' := 'a']), " ", "v_int_71", " ", v_int_71, " ", "v_seq_61", " ", (v_seq_61 == ['t']), " ", "v_int_70", " ", v_int_70, " ", "v_seq_62", " ", (v_seq_62 == ['t']), " ", "v_int_75", " ", v_int_75, " ", "v_seq_60", " ", (v_seq_60 == ['P', 'X']), " ", "v_char_59", " ", (v_char_59 == 'H'), " ", "v_char_57", " ", (v_char_57 == 'R'), " ", "v_map_31", " ", (v_map_31 == map['p' := 0, 'c' := 12, 'e' := 24, 'g' := 23, 'm' := 13]), " ", "v_map_32", " ", (v_map_32 == map['p' := 'n', 'q' := 'P', 'h' := 'V', 'X' := 'Q']), " ", "v_int_68", " ", v_int_68, " ", "v_int_67", " ", v_int_67, " ", "v_int_66", " ", v_int_66, " ", "v_int_65", " ", v_int_65, " ", "v_seq_54", " ", (v_seq_54 == ['d', 'n', 'Y']), " ", "v_seq_55", " ", (v_seq_55 == ['x', 'n', 'Y']), " ", "v_seq_56", " ", (v_seq_56 == []), " ", "v_int_69", " ", v_int_69, " ", "v_int_60", " ", v_int_60, " ", "v_seq_50", " ", (v_seq_50 == []), " ", "v_seq_51", " ", (v_seq_51 == ['W', 'L', 'G', 't']), " ", "v_seq_52", " ", (v_seq_52 == ['L']), " ", "v_seq_53", " ", (v_seq_53 == ['d', 'n', 'Y']), " ", "v_int_64", " ", v_int_64, " ", "v_int_63", " ", v_int_63, " ", "v_char_60", " ", (v_char_60 == 'X'), " ", "v_int_62", " ", v_int_62, " ", "v_int_61", " ", v_int_61, " ", "v_char_49", " ", (v_char_49 == 'P'), " ", "v_char_44", " ", (v_char_44 == 'r'), " ", "v_int_57", " ", v_int_57, " ", "v_seq_47", " ", v_seq_47, " ", "v_int_56", " ", v_int_56, " ", "v_seq_48", " ", (v_seq_48 == []), " ", "v_int_55", " ", v_int_55, " ", "v_seq_49", " ", (v_seq_49 == ['H', 'c']), " ", "v_seq_43", " ", (v_seq_43 == [[]]), " ", "v_seq_44", " ", (v_seq_44 == []), " ", "v_seq_45", " ", (v_seq_45 == []), " ", "v_int_59", " ", v_int_59, " ", "v_int_58", " ", v_int_58, " ", "v_seq_46", " ", v_seq_46, " ", "v_char_54", " ", (v_char_54 == 'y'), " ", "v_seq_40", " ", (v_seq_40 == [[]]), " ", "v_char_53", " ", (v_char_53 == 'L'), " ", "v_seq_41", " ", (v_seq_41 == []), " ", "v_seq_42", " ", (v_seq_42 == ['k', 'C']), " ", "v_seq_36", " ", (v_seq_36 == []), " ", "v_seq_38", " ", (v_seq_38 == []), " ", "v_seq_39", " ", (v_seq_39 == ['X', 'd', 'N']), " ", "v_int_54", " ", v_int_54, " ", "v_map_28", " ", (v_map_28 == map['C' := true, 'D' := false, 'Z' := true, 'J' := true]), " ", "v_int_49", " ", v_int_49, " ", "v_char_56", " ", (v_char_56 == 'u'), " ", "v_seq_35", " ", (v_seq_35 == []), " ", "v_int_53", " ", v_int_53, " ", "v_int_51", " ", v_int_51, " ", "v_int_50", " ", v_int_50, " ", "v_map_26", " ", (v_map_26 == map['V' := 'e', 'F' := 'J', 'I' := 'i', 'y' := 'a']), " ", "v_seq_34", " ", v_seq_34, " ", "v_int_48", " ", v_int_48, " ", "v_map_27", " ", (v_map_27 == map['p' := true, 'Q' := true, 'y' := false, 'Y' := false, 'm' := false]), " ", "v_char_55", " ", (v_char_55 == 'E'), " ", "v_char_54", " ", (v_char_54 == 'y'), " ", "v_map_25", " ", (v_map_25 == map['r' := {'Q'}]), " ", "v_char_53", " ", (v_char_53 == 'L'), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_bool_4", " ", v_bool_4, " ", "v_int_45", " ", v_int_45, " ", "v_map_19", " ", (v_map_19 == map['I' := 'k']), " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_char_43", " ", (v_char_43 == 'r'), " ", "v_char_42", " ", (v_char_42 == 'Y'), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_49", " ", (v_char_49 == 'P'), " ", "v_char_48", " ", (v_char_48 == 'H'), " ", "v_char_47", " ", (v_char_47 == 'I'), " ", "v_char_46", " ", (v_char_46 == 'H'), " ", "v_char_45", " ", (v_char_45 == 'Q'), " ", "v_char_44", " ", (v_char_44 == 'r'), " ", "v_map_22", " ", (v_map_22 == map['I' := 'k']), " ", "v_map_23", " ", (v_map_23 == map['Q' := v_DT_1_1_8, 'T' := v_DT_1_1_9, 'G' := v_DT_1_1_10, 'W' := v_DT_1_1_11, 'X' := v_DT_1_1_12]), " ", "v_map_20", " ", (v_map_20 == map['C' := 19, 'g' := 7]), " ", "v_seq_29", " ", (v_seq_29 == ['h', 'a', 'r']), " ", "v_map_21", " ", (v_map_21 == map['l' := 'g']), " ", "v_seq_25", " ", (v_seq_25 == []), " ", "v_seq_26", " ", (v_seq_26 == []), " ", "v_seq_27", " ", v_seq_27, " ", "v_seq_28", " ", v_seq_28, " ", "v_int_39", " ", v_int_39, " ", "v_char_51", " ", (v_char_51 == 'o'), " ", "v_char_50", " ", (v_char_50 == 'h'), "\n";
					}
					
				}
				
				var v_int_78: int := v_int_40;
				var v_int_79: int := |(map['E' := 'a', 'X' := 'C', 'x' := 'U']['c' := 'a']).Values|;
				while (v_int_78 < v_int_79) 
					decreases v_int_79 - v_int_78;
					invariant (v_int_78 <= v_int_79);
				{
					v_int_78 := (v_int_78 + 1);
				}
				var v_DT_1_1_13: DT_1<DT_2<bool, int>> := DT_1_1;
				var v_DT_1_1_14: DT_1<DT_2<bool, int>> := DT_1_1;
				var v_DT_1_1_15: DT_1<DT_2<bool, int>> := DT_1_1;
				var v_DT_1_1_16: DT_1<DT_2<bool, int>> := DT_1_1;
				var v_DT_1_1_17: DT_1<DT_2<bool, int>> := DT_1_1;
				print "v_char_56", " ", (v_char_56 == 'u'), " ", "v_seq_36", " ", (v_seq_36 == []), " ", "v_int_79", " ", v_int_79, " ", "v_int_78", " ", v_int_78, " ", "v_seq_38", " ", (v_seq_38 == []), " ", "v_seq_39", " ", (v_seq_39 == ['X', 'd', 'N']), " ", "v_int_54", " ", v_int_54, " ", "v_map_28", " ", (v_map_28 == map['C' := true, 'D' := false, 'Z' := true, 'J' := true]), " ", "v_int_49", " ", v_int_49, " ", "v_seq_35", " ", (v_seq_35 == []), " ", "v_int_53", " ", v_int_53, " ", "v_int_51", " ", v_int_51, " ", "v_int_50", " ", v_int_50, " ", "v_map_26", " ", (v_map_26 == map['V' := 'e', 'F' := 'J', 'I' := 'i', 'y' := 'a']), " ", "v_seq_34", " ", v_seq_34, " ", "v_int_48", " ", v_int_48, " ", "v_map_27", " ", (v_map_27 == map['p' := true, 'Q' := true, 'y' := false, 'Y' := false, 'm' := false]), " ", "v_char_55", " ", (v_char_55 == 'E'), " ", "v_char_54", " ", (v_char_54 == 'y'), " ", "v_map_25", " ", (v_map_25 == map['r' := {'Q'}]), " ", "v_char_53", " ", (v_char_53 == 'L'), " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_DT_1_1_5", " ", v_DT_1_1_5, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_bool_4", " ", v_bool_4, " ", "v_int_45", " ", v_int_45, " ", "v_map_19", " ", (v_map_19 == map['I' := 'k']), " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_char_43", " ", (v_char_43 == 'r'), " ", "v_char_42", " ", (v_char_42 == 'Y'), " ", "v_DT_1_1_1", " ", v_DT_1_1_1, " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_49", " ", (v_char_49 == 'P'), " ", "v_char_48", " ", (v_char_48 == 'H'), " ", "v_char_47", " ", (v_char_47 == 'I'), " ", "v_char_46", " ", (v_char_46 == 'H'), " ", "v_char_45", " ", (v_char_45 == 'Q'), " ", "v_char_44", " ", (v_char_44 == 'r'), " ", "v_map_22", " ", (v_map_22 == map['I' := 'k']), " ", "v_map_23", " ", (v_map_23 == map['Q' := v_DT_1_1_13, 'T' := v_DT_1_1_14, 'G' := v_DT_1_1_15, 'W' := v_DT_1_1_16, 'X' := v_DT_1_1_17]), " ", "v_map_20", " ", (v_map_20 == map['C' := 19, 'g' := 7]), " ", "v_seq_29", " ", (v_seq_29 == ['h', 'a', 'r']), " ", "v_map_21", " ", (v_map_21 == map['l' := 'g']), " ", "v_seq_25", " ", (v_seq_25 == []), " ", "v_seq_26", " ", (v_seq_26 == []), " ", "v_seq_27", " ", v_seq_27, " ", "v_seq_28", " ", v_seq_28, " ", "v_int_39", " ", v_int_39, " ", "v_char_51", " ", (v_char_51 == 'o'), " ", "v_char_50", " ", (v_char_50 == 'h'), "\n";
				return ;
			}
		}
		
	}
	
	assert true;
	expect true;
	var v_seq_63: seq<map<char, int>> := [map['x' := 29, 'K' := 6]];
	var v_seq_65: seq<map<char, int>> := (if ((|v_seq_63| > 0)) then (v_seq_63[5..0]) else (v_seq_63));
	var v_seq_64: seq<int> := [];
	var v_int_81: int := 23;
	var v_int_82: int := (if ((|v_seq_64| > 0)) then (v_seq_64[v_int_81]) else (19));
	var v_map_37: map<char, int> := (if ((|v_seq_65| > 0)) then (v_seq_65[v_int_82]) else (v_map_20));
	var v_char_65: char := (if (v_bool_3) then (v_char_49) else ((if (false) then ('s') else ('m'))));
	var v_array_1: array<char> := new char[3] ['k', 'M', 'j'];
	var v_map_36: map<char, int> := map['o' := 13, 'P' := 29, 'q' := 26, 'w' := 12, 'x' := 24];
	var v_char_64: char := 'I';
	var v_map_39: map<char, int> := map['L' := 24, 'J' := 4, 'Y' := 25, 'c' := 3, 'g' := 10]['D' := 22];
	var v_map_38: map<char, char> := map['w' := 'w', 'w' := 'H', 'U' := 'Q', 'Z' := 'A'];
	var v_char_66: char := 'z';
	var v_char_67: char := (if ((v_char_66 in v_map_38)) then (v_map_38[v_char_66]) else ('X'));
	var v_int_93: int, v_int_94: int := (if ((v_char_65 in v_map_37)) then (v_map_37[v_char_65]) else ((if ((if (false) then (false) else (true))) then (v_array_1.Length) else ((if ((v_char_64 in v_map_36)) then (v_map_36[v_char_64]) else (-19)))))), ((if ((v_char_67 in v_map_39)) then (v_map_39[v_char_67]) else ((if (true) then (23) else (23)))) - v_array_1.Length);
	for v_int_80 := v_int_93 to v_int_94 
		invariant (v_int_94 - v_int_80 >= 0)
	{
		var v_map_40: map<char, char> := (match 'd' {
			case _ => map['W' := 'l', 't' := 'z', 'H' := 't', 'J' := 'Z', 'A' := 'F']
		});
		var v_char_68: char := v_array_1[0];
		var v_seq_66: seq<char> := ['E'];
		var v_int_83: int := 13;
		var v_seq_67: seq<char> := [];
		var v_int_84: int := 11;
		var v_seq_69: seq<map<char, char>> := (if (false) then ([map['o' := 'W'], map['P' := 'H'], map['M' := 'Y', 'e' := 'p', 'o' := 'K', 'X' := 't']]) else ([map['J' := 'M', 'r' := 'u'], map['h' := 'q', 'Q' := 'Y', 'v' := 'w'], map['M' := 'z', 'k' := 'z', 'I' := 'T', 'I' := 'm']]));
		var v_seq_68: seq<int> := [26, 7, -9, 13];
		var v_int_85: int := 6;
		var v_int_86: int := (if ((|v_seq_68| > 0)) then (v_seq_68[v_int_85]) else (29));
		var v_map_42: map<char, char> := (if ((|v_seq_69| > 0)) then (v_seq_69[v_int_86]) else (map['X' := 'n', 's' := 'Q', 'n' := 'F', 'O' := 'q']['V' := 'N']));
		var v_char_70: char := v_char_43;
		var v_seq_70: seq<char> := ['j', 'F', 'C', 'V'];
		var v_int_87: int := 15;
		var v_map_41: map<char, char> := map['T' := 'B', 'T' := 'y', 's' := 'G', 'u' := 'r', 'U' := 'I'];
		var v_char_69: char := 'R';
		var v_map_43: map<char, char> := map['N' := 'y', 'v' := 'Q', 'O' := 'a', 'h' := 'L', 'S' := 'z'];
		var v_char_71: char := 'G';
		var v_map_46: map<char, char> := map['X' := 'u', 'm' := 'r']['C' := 'q'][(if ((v_char_71 in v_map_43)) then (v_map_43[v_char_71]) else ('U')) := v_char_43];
		var v_char_74: char := v_char_49;
		var v_map_45: map<char, char> := map['R' := 'N', 'f' := 'I', 'g' := 'M']['B' := 'w'];
		var v_map_44: map<char, char> := map['n' := 'X', 'o' := 'd', 'E' := 'e', 'M' := 'G'];
		var v_char_72: char := 'D';
		var v_char_73: char := (if ((v_char_72 in v_map_44)) then (v_map_44[v_char_72]) else ('A'));
		var v_seq_71: seq<char> := ['t', 'r'];
		var v_seq_72: seq<char> := (if ((|v_seq_71| > 0)) then (v_seq_71[7..0]) else (v_seq_71));
		var v_map_47: map<char, int> := map['y' := 9, 'D' := 5];
		var v_char_75: char := 'U';
		var v_seq_73: seq<char> := (if ((|v_seq_72| > 0)) then (v_seq_72[(if ((v_char_75 in v_map_47)) then (v_map_47[v_char_75]) else (16))..0]) else (v_seq_72));
		var v_map_48: map<char, int> := map['b' := 19, 'q' := 23, 'p' := 27, 'e' := 2, 'M' := 19];
		var v_char_76: char := 'a';
		var v_int_88: int := (if ((if (false) then (false) else (false))) then ((if ((v_char_76 in v_map_48)) then (v_map_48[v_char_76]) else (22))) else ((if (false) then (2) else (11))));
		var v_seq_74: seq<char> := ['w', 'c', 'R', 'p'];
		var v_seq_75: seq<char> := v_seq_74;
		var v_int_89: int := 6;
		var v_int_90: int := safe_index_seq(v_seq_75, v_int_89);
		var v_int_91: int := v_int_90;
		var v_seq_76: seq<char> := (if ((|v_seq_74| > 0)) then (v_seq_74[v_int_91 := 'T']) else (v_seq_74));
		var v_int_92: int := (27 * 24);
		v_char_72, v_char_44, v_char_47, v_char_43, v_char_45 := (match 'J' {
			case _ => (match 'n' {
				case _ => (if (true) then ('S') else ('o'))
			})
		}), v_char_50, (if ((v_char_70 in v_map_42)) then (v_map_42[v_char_70]) else ((match 'w' {
			case _ => (if (true) then ('O') else ('d'))
		}))), (if ((v_char_74 in v_map_46)) then (v_map_46[v_char_74]) else ((if ((v_char_73 in v_map_45)) then (v_map_45[v_char_73]) else ((match 'M' {
			case _ => 'x'
		}))))), (if ((|v_seq_73| > 0)) then (v_seq_73[v_int_88]) else ((if ((|v_seq_76| > 0)) then (v_seq_76[v_int_92]) else (v_char_72))));
		var v_map_49: map<char, char> := map['U' := 'y', 'P' := 'K'];
		var v_char_77: char := 'q';
		var v_map_50: map<char, char> := map['G' := 'W', 'L' := 'V', 'D' := 'l'];
		var v_char_78: char := 'l';
		var v_map_51: map<char, char> := map['l' := 'Q', 'F' := 'C', 'E' := 'K', 'A' := 'o', 'Z' := 'r'];
		var v_char_79: char := 'a';
		match (match 'h' {
			case _ => v_char_76
		}) {
			case _ => {
				return ;
			}
			
		}
		
		return ;
	}
	var v_map_54: map<char, bool> := map['C' := false, 'w' := true];
	var v_char_82: char := 'r';
	var v_map_55: map<char, bool> := map['w' := true, 'D' := false, 'V' := false]['g' := true];
	var v_char_83: char := (match 'D' {
		case _ => 'D'
	});
	var v_seq_77: seq<bool> := [];
	var v_int_95: int := -17;
	if (if (!((if ((v_char_82 in v_map_54)) then (v_map_54[v_char_82]) else (false)))) then ((if ((v_char_83 in v_map_55)) then (v_map_55[v_char_83]) else ((if ((|v_seq_77| > 0)) then (v_seq_77[v_int_95]) else (false))))) else ((if (v_bool_4) then ((if (true) then (false) else (true))) else ((match 'g' {
		case _ => true
	}))))) {
		if v_bool_2 {
			var v_seq_78: seq<char> := ['L', 'b', 'U', 'a'];
			var v_int_96: int := 13;
			var v_seq_79: seq<char> := [];
			var v_seq_80: seq<char> := (if ((|v_seq_79| > 0)) then (v_seq_79[13..13]) else (v_seq_79));
			var v_int_97: int := (match 'g' {
				case _ => 6
			});
			match (match 'l' {
				case _ => v_char_50
			}) {
				case _ => {
					return ;
				}
				
			}
			
		}
		var v_seq_81: seq<int> := [12];
		var v_seq_83: seq<int> := (if ((|v_seq_81| > 0)) then (v_seq_81[5..0]) else (v_seq_81));
		var v_seq_82: seq<int> := [17, 24];
		var v_int_99: int := 24;
		var v_seq_85: seq<int> := (if ((|v_seq_83| > 0)) then (v_seq_83[(if ((|v_seq_82| > 0)) then (v_seq_82[v_int_99]) else (18))..(match 'u' {
			case _ => 19
		})]) else (v_seq_83));
		var v_map_59: map<char, int> := (if (true) then (map['i' := 27, 'A' := -21, 'X' := 25, 'q' := 3]) else (map['X' := 9, 'T' := 5]));
		var v_seq_84: seq<char> := ['n', 'a'];
		var v_int_100: int := 12;
		var v_char_87: char := (if ((|v_seq_84| > 0)) then (v_seq_84[v_int_100]) else ('b'));
		var v_int_101: int := (if ((v_char_87 in v_map_59)) then (v_map_59[v_char_87]) else (v_int_42));
		var v_seq_86: seq<bool> := [true, false, true];
		var v_int_102: int := 5;
		var v_seq_87: seq<int> := [-1, 14, 24];
		var v_int_103: int := 10;
		var v_int_104: int, v_int_105: int := (if ((|v_seq_85| > 0)) then (v_seq_85[v_int_101]) else ((v_int_82 * (match 'w' {
			case _ => 11
		})))), ((if ((if ((|v_seq_86| > 0)) then (v_seq_86[v_int_102]) else (true))) then (v_int_40) else ((if ((|v_seq_87| > 0)) then (v_seq_87[v_int_103]) else (23)))) - v_int_82);
		for v_int_98 := v_int_104 to v_int_105 
			invariant (v_int_105 - v_int_98 >= 0)
		{
			
		}
		return ;
	}
	var v_seq_88: seq<char> := ['n', 'k', 't'];
	var v_seq_90: seq<char> := (if ((|v_seq_88| > 0)) then (v_seq_88[21..26]) else (v_seq_88));
	var v_seq_89: seq<int> := [];
	var v_int_106: int := 14;
	var v_int_107: int := (if ((|v_seq_89| > 0)) then (v_seq_89[v_int_106]) else (1));
	var v_map_60: map<char, char> := map['Y' := 'E', 'o' := 'x', 'G' := 'M'];
	var v_char_88: char := 'Z';
	var v_map_61: map<char, char> := map['P' := 'c', 'Z' := 'X', 'h' := 'U', 'R' := 'O'];
	var v_char_89: char := 'p';
	match (match 'l' {
		case _ => (if (v_bool_4) then ((if ((v_char_88 in v_map_60)) then (v_map_60[v_char_88]) else ('N'))) else ((if ((v_char_89 in v_map_61)) then (v_map_61[v_char_89]) else ('j'))))
	}) {
		case _ => {
			var v_map_92: map<char, int> := map['D' := 27, 'L' := 26, 'Y' := 19, 'L' := 25, 'm' := -10];
			var v_char_120: char := 'N';
			var v_map_95: map<char, int> := map['w' := -13]['P' := 19][v_char_66 := (if ((v_char_120 in v_map_92)) then (v_map_92[v_char_120]) else (8))];
			var v_seq_144: seq<char> := [];
			var v_seq_145: seq<char> := v_seq_144;
			var v_int_171: int := 24;
			var v_int_172: int := safe_index_seq(v_seq_145, v_int_171);
			var v_int_173: int := v_int_172;
			var v_seq_146: seq<char> := (if ((|v_seq_144| > 0)) then (v_seq_144[v_int_173 := 'l']) else (v_seq_144));
			var v_map_93: map<char, int> := map['s' := 6, 'u' := 6, 'B' := 12, 'l' := 10];
			var v_char_121: char := 'S';
			var v_int_174: int := (if ((v_char_121 in v_map_93)) then (v_map_93[v_char_121]) else (-3));
			var v_char_123: char := (if ((|v_seq_146| > 0)) then (v_seq_146[v_int_174]) else ((if (true) then ('d') else ('d'))));
			var v_map_94: map<char, int> := map['K' := 1, 'B' := 18, 'O' := 4, 'e' := 20, 'k' := 28]['s' := 6];
			var v_char_122: char := (match 'K' {
				case _ => 'q'
			});
			var v_int_169: int := (if ((v_char_123 in v_map_95)) then (v_map_95[v_char_123]) else ((if ((v_char_122 in v_map_94)) then (v_map_94[v_char_122]) else ((if (true) then (9) else (15))))));
			var v_seq_147: seq<multiset<char>> := [multiset({'y', 'K', 'Q'}), multiset({})];
			var v_int_175: int := 7;
			var v_map_97: map<char, int> := (map['D' := 5] - {'j', 'o', 'i'});
			var v_map_96: map<char, char> := map['L' := 'I', 'e' := 'z'];
			var v_char_124: char := 'm';
			var v_char_125: char := (if ((v_char_124 in v_map_96)) then (v_map_96[v_char_124]) else ('Q'));
			var v_seq_148: seq<int> := [3];
			var v_int_176: int := 18;
			var v_map_98: map<char, int> := map['x' := 20, 'Q' := 29, 'n' := 7, 'h' := 25, 'D' := 6];
			var v_char_126: char := 'R';
			var v_int_170: int := (if (((if ((|v_seq_147| > 0)) then (v_seq_147[v_int_175]) else (multiset{'c', 'D', 'l'})) > (match 'T' {
				case _ => multiset({'L', 'A'})
			}))) then ((if ((v_char_125 in v_map_97)) then (v_map_97[v_char_125]) else ((if ((|v_seq_148| > 0)) then (v_seq_148[v_int_176]) else (19))))) else ((match 'e' {
				case _ => (if ((v_char_126 in v_map_98)) then (v_map_98[v_char_126]) else (11))
			})));
			while (v_int_169 < v_int_170) 
				decreases v_int_170 - v_int_169;
				invariant (v_int_169 <= v_int_170);
			{
				v_int_169 := (v_int_169 + 1);
				assert true;
				expect true;
				assert true;
				expect true;
				if v_bool_4 {
					return ;
				} else {
					var v_map_99: map<char, char> := map['w' := 'u', 'a' := 'V', 'U' := 'V', 'P' := 'd', 'J' := 'i']['Q' := 'Y'];
					var v_char_127: char := v_char_44;
					var v_map_100: map<char, char> := map['V' := 'o', 'E' := 'S', 'P' := 'P', 'e' := 'l', 'E' := 'D'];
					var v_char_128: char := 'C';
					var v_map_101: map<char, char> := map['w' := 'y', 'S' := 'o', 'M' := 'E']['a' := 'h'][(if ((v_char_128 in v_map_100)) then (v_map_100[v_char_128]) else ('W')) := v_char_122];
					var v_char_129: char := (if ((if (false) then (false) else (true))) then ((if (true) then ('X') else ('Z'))) else ((match 'o' {
						case _ => 'J'
					})));
					var v_seq_149: seq<char> := v_seq_144;
					var v_int_177: int := (9 / 14);
					var v_seq_150: seq<char> := ['k', 'f', 'x', 'r'];
					var v_seq_151: seq<char> := (if ((|v_seq_150| > 0)) then (v_seq_150[8..0]) else (v_seq_150));
					var v_seq_153: seq<char> := (if ((|v_seq_151| > 0)) then (v_seq_151[(match 'e' {
						case _ => 20
					})..(if (true) then (22) else (19))]) else (v_seq_151));
					var v_seq_152: seq<int> := [];
					var v_int_178: int := 15;
					var v_map_102: map<char, int> := map['j' := 13, 'i' := 18];
					var v_char_130: char := 'f';
					var v_int_179: int := (match 'O' {
						case _ => (if ((v_char_130 in v_map_102)) then (v_map_102[v_char_130]) else (0))
					});
					var v_seq_154: seq<char> := ['X', 's', 'F'];
					var v_seq_155: seq<char> := (if ((|v_seq_154| > 0)) then (v_seq_154[25..5]) else (v_seq_154));
					var v_int_180: int := (-15 * 29);
					v_char_51, v_char_120, v_char_82, v_char_123 := v_array_1[1], (match 'r' {
						case _ => v_char_65
					}), (if ((v_char_129 in v_map_101)) then (v_map_101[v_char_129]) else ((if ((|v_seq_149| > 0)) then (v_seq_149[v_int_177]) else ((if (true) then ('P') else ('P')))))), (if ((|v_seq_153| > 0)) then (v_seq_153[v_int_179]) else ((if ((|v_seq_155| > 0)) then (v_seq_155[v_int_180]) else ((match 's' {
						case _ => 'M'
					})))));
					continue;
				}
			}
			var v_seq_156: seq<bool> := [true, true];
			var v_seq_157: seq<bool> := (if ((|v_seq_156| > 0)) then (v_seq_156[20..17]) else (v_seq_156));
			var v_map_103: map<char, int> := map['N' := 10];
			var v_char_131: char := 'N';
			var v_int_181: int := (if ((v_char_131 in v_map_103)) then (v_map_103[v_char_131]) else (27));
			var v_map_106: map<char, char> := v_map_22;
			var v_map_104: map<char, char> := map['T' := 'w', 't' := 'X', 'n' := 'h', 'g' := 'f'];
			var v_char_132: char := 'p';
			var v_char_134: char := (if ((v_char_132 in v_map_104)) then (v_map_104[v_char_132]) else ('f'));
			var v_map_105: map<char, char> := map['p' := 'e', 'R' := 'U', 'm' := 'v', 'F' := 'b'];
			var v_char_133: char := 'l';
			var v_seq_158: seq<char> := ['j', 'V'];
			var v_seq_159: seq<char> := v_seq_158;
			var v_int_182: int := 13;
			var v_int_183: int := safe_index_seq(v_seq_159, v_int_182);
			var v_int_184: int := v_int_183;
			var v_seq_161: seq<char> := (if ((|v_seq_158| > 0)) then (v_seq_158[v_int_184 := 'x']) else (v_seq_158));
			var v_seq_162: seq<char> := v_seq_161;
			var v_int_186: int := (if (false) then (5) else (29));
			var v_int_187: int := safe_index_seq(v_seq_162, v_int_186);
			var v_int_188: int := v_int_187;
			var v_seq_160: seq<char> := ['Y'];
			var v_int_185: int := 17;
			var v_seq_166: seq<char> := (if ((|v_seq_161| > 0)) then (v_seq_161[v_int_188 := (if ((|v_seq_160| > 0)) then (v_seq_160[v_int_185]) else ('a'))]) else (v_seq_161));
			var v_seq_163: seq<int> := [4, 28];
			var v_seq_164: seq<int> := v_seq_163;
			var v_int_189: int := 14;
			var v_int_190: int := safe_index_seq(v_seq_164, v_int_189);
			var v_int_191: int := v_int_190;
			var v_seq_165: seq<int> := (if ((|v_seq_163| > 0)) then (v_seq_163[v_int_191 := 24]) else (v_seq_163));
			var v_array_3: array<char> := new char[5] ['O', 'y', 'j', 'N', 'e'];
			var v_int_192: int := v_array_3.Length;
			var v_int_193: int := (if ((|v_seq_165| > 0)) then (v_seq_165[v_int_192]) else ((0 % 6)));
			var v_map_107: map<char, char> := map['k' := 'n', 'g' := 'h', 'w' := 'B', 'E' := 'f', 'M' := 'G'];
			var v_char_135: char := 'N';
			var v_map_108: map<char, bool> := map['M' := false, 'L' := false, 'm' := true, 'L' := true]['q' := false];
			var v_seq_167: seq<char> := ['K', 'Z'];
			var v_int_194: int := 22;
			var v_char_136: char := (if ((|v_seq_167| > 0)) then (v_seq_167[v_int_194]) else ('o'));
			var v_map_109: map<char, char> := map['Q' := 'c', 'V' := 'A', 'I' := 'w', 'd' := 'r']['T' := 'D'];
			var v_char_137: char := (if (true) then ('P') else ('J'));
			var v_seq_168: seq<char> := ['f', 'p'];
			var v_int_195: int := 9;
			v_char_121, v_char_132, v_array_3[4], v_char_136, v_char_67 := (if ((if ((|v_seq_157| > 0)) then (v_seq_157[v_int_181]) else (v_bool_4))) then (v_char_67) else ((if ((v_char_134 in v_map_106)) then (v_map_106[v_char_134]) else ((if ((v_char_133 in v_map_105)) then (v_map_105[v_char_133]) else ('M')))))), v_char_49, (if ((|v_seq_166| > 0)) then (v_seq_166[v_int_193]) else (v_char_47)), (match 'P' {
				case _ => v_array_3[3]
			}), (if ((if ((v_char_136 in v_map_108)) then (v_map_108[v_char_136]) else ((match 'k' {
				case _ => true
			})))) then ((if ((v_char_137 in v_map_109)) then (v_map_109[v_char_137]) else ((if ((|v_seq_168| > 0)) then (v_seq_168[v_int_195]) else ('T'))))) else ((match 'k' {
				case _ => (if (true) then ('M') else ('z'))
			})));
			return ;
		}
		
	}
	
}
