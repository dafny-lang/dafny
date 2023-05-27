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

method m_method_5(p_m_method_5_1: char) returns (ret_1: seq<char>)
{
	var v_int_8: int, v_int_9: int := 3, 19;
	for v_int_7 := v_int_8 to v_int_9 
		invariant (v_int_9 - v_int_7 >= 0)
	{
		return ['P', 'X', 'r'];
	}
	var v_char_18: char, v_char_19: char, v_char_20: char, v_char_21: char, v_char_22: char := 'z', 'Y', 't', 'G', 'Y';
	var v_int_10: int := 7;
	var v_int_11: int := -10;
	while (v_int_10 < v_int_11) 
		decreases v_int_11 - v_int_10;
		invariant (v_int_10 <= v_int_11);
	{
		v_int_10 := (v_int_10 + 1);
		return ['W'];
	}
	v_char_21, v_char_18, v_char_22, v_char_20, v_char_19 := 'P', 'R', 'I', 'e', 'w';
	v_char_20 := 'Z';
	return ['G', 'B'];
}

method m_method_4(p_m_method_4_1: char) returns (ret_1: char, ret_2: char, ret_3: char, ret_4: char)
	requires ((p_m_method_4_1 == 'k'));
	ensures (((p_m_method_4_1 == 'k')) ==> ((ret_1 == 'r') && (ret_2 == 'P') && (ret_3 == 'z') && (ret_4 == 'j')));
{
	match 'l' {
		case 'H' => {
			return 'q', 'd', 'q', 'S';
		}
			case 'G' => {
			return 'L', 'D', 'F', 'a';
		}
			case _ => {
			print "p_m_method_4_1", " ", (p_m_method_4_1 == 'k'), "\n";
			return 'r', 'P', 'z', 'j';
		}
		
	}
	
}

method m_method_3(p_m_method_3_1: char, p_m_method_3_2: char, p_m_method_3_3: char, p_m_method_3_4: char) returns (ret_1: bool)
	requires ((p_m_method_3_1 == 'O') && (p_m_method_3_3 == 'D') && (p_m_method_3_2 == 'g') && (p_m_method_3_4 == 'Z')) || ((p_m_method_3_1 == 'j') && (p_m_method_3_3 == 's') && (p_m_method_3_2 == 'q') && (p_m_method_3_4 == 'G'));
	ensures (((p_m_method_3_1 == 'j') && (p_m_method_3_3 == 's') && (p_m_method_3_2 == 'q') && (p_m_method_3_4 == 'G')) ==> ((ret_1 == false))) && (((p_m_method_3_1 == 'O') && (p_m_method_3_3 == 'D') && (p_m_method_3_2 == 'g') && (p_m_method_3_4 == 'Z')) ==> ((ret_1 == false)));
{
	var v_char_9: char := 'k';
	var v_char_10: char, v_char_11: char, v_char_12: char, v_char_13: char := m_method_4(v_char_9);
	v_char_12, v_char_9, v_char_13, v_char_10 := v_char_10, v_char_11, v_char_12, v_char_13;
	print "v_char_13", " ", (v_char_13 == 'z'), " ", "v_char_12", " ", (v_char_12 == 'r'), " ", "v_char_11", " ", (v_char_11 == 'P'), " ", "v_char_9", " ", (v_char_9 == 'P'), " ", "v_char_10", " ", (v_char_10 == 'j'), " ", "p_m_method_3_2", " ", (p_m_method_3_2 == 'g'), " ", "p_m_method_3_1", " ", (p_m_method_3_1 == 'O'), " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 'Z'), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == 'D'), "\n";
	return false;
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

method m_method_2(p_m_method_2_1: char) returns (ret_1: char)
	requires ((p_m_method_2_1 == 'l')) || ((p_m_method_2_1 == 'B')) || ((p_m_method_2_1 == 't'));
	ensures (((p_m_method_2_1 == 'B')) ==> ((ret_1 == 'R'))) && (((p_m_method_2_1 == 'l')) ==> ((ret_1 == 'R'))) && (((p_m_method_2_1 == 't')) ==> ((ret_1 == 'R')));
{
	var v_char_2: char := 'p';
	if true {
		if true {
			print "p_m_method_2_1", " ", (p_m_method_2_1 == 'B'), " ", "v_char_2", " ", (v_char_2 == 'p'), "\n";
			return 'R';
		}
		return 'L';
	}
	return 'V';
}

method m_method_1(p_m_method_1_1: char, p_m_method_1_2: char) returns (ret_1: seq<char>)
	requires ((p_m_method_1_1 == 'R') && (p_m_method_1_2 == 'R'));
	ensures (((p_m_method_1_1 == 'R') && (p_m_method_1_2 == 'R')) ==> (|ret_1| == 2 && (ret_1[0] == 'm') && (ret_1[1] == 'O')));
{
	var v_char_1: char := p_m_method_1_1;
	var v_char_3: char := 'l';
	var v_char_4: char := m_method_2(v_char_3);
	var v_char_5: char, v_char_6: char, v_char_7: char, v_char_8: char := (if (false) then ('F') else ('D')), v_char_4, 'y', (if (true) then ('F') else ('A'));
	var v_char_14: char := 'O';
	var v_char_15: char := 'g';
	var v_char_16: char := 'D';
	var v_char_17: char := 'Z';
	var v_bool_1: bool := m_method_3(v_char_14, v_char_15, v_char_16, v_char_17);
	if v_bool_1 {
		var v_char_23: char := 'O';
		var v_seq_3: seq<char> := m_method_5(v_char_23);
		return v_seq_3;
	} else {
		var v_char_24: char := 't';
		var v_char_25: char := m_method_2(v_char_24);
		match v_char_25 {
			case 'N' => {
				var v_char_26: char := 'P';
				var v_char_27: char := m_method_2(v_char_26);
				v_char_26, v_char_4, v_char_1 := v_char_5, (if (true) then ('D') else ('q')), v_char_27;
				return (['I'] + []);
			}
				case 'm' => {
				if v_bool_1 {
					return (['N'] + ['v']);
				} else {
					var v_seq_4: seq<seq<char>> := [];
					var v_int_12: int := 27;
					return (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_12]) else (['d']));
				}
			}
				case _ => {
				print "v_char_25", " ", (v_char_25 == 'R'), " ", "v_char_24", " ", (v_char_24 == 't'), " ", "v_char_1", " ", (v_char_1 == 'R'), " ", "v_bool_1", " ", v_bool_1, " ", "v_char_17", " ", (v_char_17 == 'Z'), " ", "v_char_3", " ", (v_char_3 == 'l'), " ", "v_char_16", " ", (v_char_16 == 'D'), " ", "v_char_15", " ", (v_char_15 == 'g'), " ", "v_char_5", " ", (v_char_5 == 'D'), " ", "v_char_14", " ", (v_char_14 == 'O'), " ", "v_char_4", " ", (v_char_4 == 'R'), " ", "v_char_7", " ", (v_char_7 == 'y'), " ", "v_char_6", " ", (v_char_6 == 'R'), " ", "v_char_8", " ", (v_char_8 == 'F'), " ", "p_m_method_1_2", " ", (p_m_method_1_2 == 'R'), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'R'), "\n";
				return (match 'u' {
					case 'E' => ['Q', 'e', 'a']
					case _ => ['m', 'O']
				});
			}
			
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
	if true {
		
	}
	var v_char_28: char := 'B';
	var v_char_29: char := m_method_2(v_char_28);
	var v_char_30: char := v_char_29;
	var v_char_31: char := v_char_29;
	var v_seq_5: seq<char> := m_method_1(v_char_30, v_char_31);
	var v_seq_6: seq<char> := v_seq_5;
	var v_int_13: int := 9;
	var v_int_14: int := 3;
	var v_int_15: int := safe_modulus(v_int_13, v_int_14);
	var v_int_16: int := (if ((true <== false)) then (v_int_15) else (v_int_14));
	var v_char_32: char := 'j';
	var v_char_33: char := 'q';
	var v_char_34: char := 's';
	var v_char_35: char := 'G';
	var v_bool_2: bool := m_method_3(v_char_32, v_char_33, v_char_34, v_char_35);
	v_char_35, v_char_30, v_bool_2, v_char_28 := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_16]) else (v_char_30)), v_char_28, ((if ((22 < -20)) then (v_bool_2) else (v_bool_2)) <== v_bool_2), v_char_28;
	var v_seq_7: seq<char> := v_seq_6;
	var v_map_1: map<char, int> := map['a' := 21, 'x' := 17, 'v' := 3];
	var v_char_36: char := 'D';
	var v_int_17: int := (if (({'B', 'Q', 'c'} < {'V', 'y'})) then ((if ((v_char_36 in v_map_1)) then (v_map_1[v_char_36]) else (11))) else ((match 'Y' {
		case 's' => 7
		case _ => 12
	})));
	var v_seq_38: seq<char> := v_seq_7;
	var v_int_62: int := v_int_17;
	var v_int_63: int := safe_index_seq(v_seq_38, v_int_62);
	v_int_17 := v_int_63;
	var v_seq_10: seq<char> := v_seq_7;
	var v_seq_8: seq<char> := [];
	var v_int_18: int := -6;
	var v_int_19: int := safe_index_seq(v_seq_8, v_int_18);
	var v_seq_9: seq<int> := [23, 26];
	var v_int_20: int := 6;
	var v_seq_37: seq<int> := v_seq_9;
	var v_int_60: int := v_int_20;
	var v_int_61: int := safe_index_seq(v_seq_37, v_int_60);
	v_int_20 := v_int_61;
	var v_int_21: int := (v_int_19 % (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_20]) else (2)));
	v_char_36, v_char_29, v_char_35, v_char_30, v_char_28 := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_17]) else (v_char_35)), v_char_32, v_char_34, v_char_32, (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_21]) else (v_char_34));
	var v_int_38: int, v_int_39: int := v_int_19, v_int_16;
	for v_int_22 := v_int_38 downto v_int_39 
		invariant (v_int_22 - v_int_39 >= 0) && ((((v_int_22 == 0)) ==> ((((v_char_36 == 'm')) && ((v_char_33 == 'q')) && ((v_char_32 == 'j')) && ((v_char_31 == 'R')) && ((v_char_30 == 'j'))))))
	{
		var v_seq_11: seq<char> := (['P', 'Z'] + ['n', 'g']);
		var v_int_23: int := (-20 + 28);
		var v_seq_12: seq<char> := (['Z'] + ['o', 'o', 'X']);
		var v_seq_13: seq<char> := v_seq_12;
		var v_int_24: int := (26 + 26);
		var v_int_25: int := safe_index_seq(v_seq_13, v_int_24);
		var v_int_26: int := v_int_25;
		var v_map_2: map<char, char> := map['F' := 'l', 'Y' := 't', 'L' := 'C', 'b' := 'R'];
		var v_char_37: char := 'C';
		var v_seq_14: seq<char> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_26 := (if ((v_char_37 in v_map_2)) then (v_map_2[v_char_37]) else ('h'))]) else (v_seq_12));
		var v_map_3: map<char, int> := v_map_1;
		var v_char_38: char := (match 'L' {
			case _ => 'Z'
		});
		var v_int_27: int := (if ((v_char_38 in v_map_3)) then (v_map_3[v_char_38]) else ((if (false) then (8) else (20))));
		v_char_31, v_char_36, v_char_30 := (match 'N' {
			case _ => (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_23]) else ((match 'V' {
				case _ => 'Y'
			})))
		}), v_char_31, (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_27]) else (v_char_29));
		v_char_32, v_char_33 := v_char_37, v_char_32;
		var v_seq_15: seq<multiset<char>> := [];
		var v_int_30: int := 6;
		var v_seq_16: seq<array<char>> := [];
		var v_int_31: int := 24;
		var v_array_1: array<char> := new char[4] ['s', 'i', 'O', 'G'];
		var v_int_28: int := (if (v_bool_2) then (|(if ((|v_seq_15| > 0)) then (v_seq_15[v_int_30]) else (multiset({'N', 'U', 'o', 'z'})))|) else ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_31]) else (v_array_1)).Length));
		var v_int_29: int := v_int_26;
		while (v_int_28 < v_int_29) 
			decreases v_int_29 - v_int_28;
			invariant (v_int_28 <= v_int_29);
		{
			v_int_28 := (v_int_28 + 1);
			assert true;
			expect true;
			var v_map_4: map<char, bool> := map['g' := true, 'j' := true, 'h' := false];
			var v_char_39: char := 'p';
			var v_seq_17: seq<bool> := [];
			var v_int_32: int := 18;
			if (match 'w' {
				case _ => (if (('h' != 'v')) then (v_bool_2) else ((if ((|v_seq_17| > 0)) then (v_seq_17[v_int_32]) else (false))))
			}) {
				assert true;
				expect true;
			}
		}
		if v_bool_2 {
			
		} else {
			return ;
		}
		var v_map_5: map<char, seq<int>> := map['T' := [22, 4, 0], 'c' := [7, 15, 18, 9], 'R' := [28, 14], 'Q' := [4]];
		var v_char_40: char := 'k';
		var v_seq_18: seq<int> := (if ((v_char_40 in v_map_5)) then (v_map_5[v_char_40]) else ([]));
		var v_array_2: array<char> := new char[4] ['Z', 'h', 'M', 'x'];
		var v_int_34: int := v_array_2.Length;
		var v_array_3: array<char> := new char[5] ['p', 'X', 'B', 'u', 'C'];
		var v_map_6: map<char, real> := map['Q' := -10.21];
		var v_char_41: char := 'g';
		var v_map_7: map<char, int> := map['T' := 24, 'm' := 22, 'd' := -4]['P' := 23];
		var v_char_42: char := (match 'I' {
			case _ => 'I'
		});
		var v_map_8: map<char, map<char, int>> := (map['m' := map['O' := -14, 'c' := 19, 'a' := 20, 'j' := 0, 'E' := 0]] - {});
		var v_char_43: char := v_char_30;
		var v_seq_19: seq<map<char, int>> := [map['T' := -11, 'c' := 6, 'q' := 21, 'W' := 4], map['n' := 25, 'w' := 14]];
		var v_int_35: int := 29;
		var v_map_9: map<char, int> := (if ((v_char_43 in v_map_8)) then (v_map_8[v_char_43]) else ((if ((|v_seq_19| > 0)) then (v_seq_19[v_int_35]) else (map['L' := 15, 'U' := 7, 'v' := 7, 'K' := -24]))));
		var v_char_44: char := v_char_36;
		var v_int_36: int, v_int_37: int := (match 'e' {
			case _ => (if ((v_char_42 in v_map_7)) then (v_map_7[v_char_42]) else (v_int_27))
		}), (if ((v_char_44 in v_map_9)) then (v_map_9[v_char_44]) else (v_int_15));
		for v_int_33 := v_int_36 to v_int_37 
			invariant (v_int_37 - v_int_33 >= 0)
		{
			continue;
		}
		break;
	}
	var v_seq_20: seq<bool> := ([true, false, true, false] + [true]);
	var v_int_40: int := v_int_17;
	var v_seq_21: seq<bool> := [];
	var v_int_41: int := 24;
	var v_map_10: map<char, map<char, char>> := map['t' := map['s' := 'G', 'T' := 'Z', 'o' := 'B', 'k' := 'u']];
	var v_char_45: char := 'f';
	var v_map_11: map<char, char> := (if ((v_char_45 in v_map_10)) then (v_map_10[v_char_45]) else (map['q' := 'K', 'z' := 'd']));
	var v_char_46: char := (if (true) then ('y') else ('G'));
	var v_seq_22: seq<set<char>> := [{'z', 'O', 'i'}, {}, {'K', 'Y'}, {}];
	var v_int_42: int := 0;
	var v_map_12: map<char, char> := ((map['Y' := 'K'] + map['s' := 'w', 'g' := 'G']) - (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_42]) else ({})));
	var v_seq_23: seq<char> := [];
	var v_int_43: int := -11;
	var v_seq_24: seq<char> := ['T', 'A', 'b'];
	var v_int_44: int := 23;
	var v_seq_39: seq<char> := v_seq_24;
	var v_int_64: int := v_int_44;
	var v_int_65: int := safe_index_seq(v_seq_39, v_int_64);
	v_int_44 := v_int_65;
	var v_char_47: char := (match 'S' {
		case 'U' => (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_43]) else ('Y'))
		case _ => (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_44]) else ('A'))
	});
	v_char_47, v_char_45 := (if ((if ((|v_seq_20| > 0)) then (v_seq_20[v_int_40]) else ((if ((|v_seq_21| > 0)) then (v_seq_21[v_int_41]) else (true))))) then ((if ((v_char_46 in v_map_11)) then (v_map_11[v_char_46]) else (v_char_28))) else (v_char_29)), (if ((v_char_47 in v_map_12)) then (v_map_12[v_char_47]) else (v_char_30));
	var v_seq_25: seq<map<char, char>> := [map['D' := 'C'], map['r' := 'd'], map['r' := 'f', 'w' := 'c', 'c' := 'O', 'X' := 'q', 'T' := 'X'], map['L' := 'u', 't' := 'a', 'C' := 'L', 'u' := 'l']];
	var v_seq_26: seq<map<char, char>> := v_seq_25;
	var v_int_45: int := 17;
	var v_int_46: int := safe_index_seq(v_seq_26, v_int_45);
	var v_int_47: int := v_int_46;
	var v_seq_27: seq<map<char, char>> := (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_47 := map['B' := 'y', 'j' := 'N', 'p' := 'c', 'm' := 'e']]) else (v_seq_25));
	var v_int_48: int := v_int_17;
	var v_map_14: map<char, char> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_48]) else (map['I' := 'T', 'V' := 'G', 'g' := 'k', 'v' := 'A', 'L' := 'S']['k' := 'd']));
	var v_seq_28: seq<char> := (['u', 'j', 'o', 'D'] + ['P', 'M']);
	var v_map_13: map<char, int> := map['Q' := 7, 'H' := 26, 'D' := 29, 'C' := 7];
	var v_char_48: char := 'U';
	var v_int_49: int := (if ((v_char_48 in v_map_13)) then (v_map_13[v_char_48]) else (6));
	var v_seq_40: seq<char> := v_seq_28;
	var v_int_66: int := v_int_49;
	var v_int_67: int := safe_index_seq(v_seq_40, v_int_66);
	v_int_49 := v_int_67;
	var v_char_49: char := (if ((|v_seq_28| > 0)) then (v_seq_28[v_int_49]) else ((if (false) then ('t') else ('b'))));
	var v_seq_29: seq<char> := ['f', 'Y'];
	var v_seq_30: seq<char> := v_seq_29;
	var v_int_50: int := 5;
	var v_int_51: int := safe_index_seq(v_seq_30, v_int_50);
	var v_int_52: int := v_int_51;
	var v_seq_31: seq<char> := ['s', 'e', 'h', 'J'];
	var v_seq_32: seq<char> := v_seq_31;
	var v_int_53: int := 26;
	var v_int_54: int := safe_index_seq(v_seq_32, v_int_53);
	var v_int_55: int := v_int_54;
	var v_seq_33: seq<char> := (match 'x' {
		case 'Y' => (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_52 := 'e']) else (v_seq_29))
		case 'D' => ([] + ['S', 'c'])
		case _ => (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_55 := 'q']) else (v_seq_31))
	});
	var v_int_56: int := v_int_13;
	var v_seq_41: seq<char> := v_seq_33;
	var v_int_68: int := v_int_56;
	var v_int_69: int := safe_index_seq(v_seq_41, v_int_68);
	v_int_56 := v_int_69;
	var v_map_15: map<char, char> := (if (true) then (map['L' := 'F']) else (map['u' := 'C']));
	var v_char_50: char := (match 'y' {
		case 'f' => 'x'
		case 'P' => 'e'
		case _ => 'w'
	});
	var v_seq_34: seq<char> := ['c'];
	var v_int_57: int := 9;
	var v_seq_35: seq<char> := v_seq_34;
	var v_map_16: map<char, int> := (map['g' := 21] + map['x' := 8]);
	var v_char_51: char := (match 'k' {
		case 'B' => 'm'
		case _ => 'Q'
	});
	var v_int_58: int := (if ((v_char_51 in v_map_16)) then (v_map_16[v_char_51]) else ((20 / 23)));
	var v_map_17: map<char, char> := map['O' := 'O', 'I' := 'j']['u' := 'h'];
	var v_char_52: char := (if (false) then ('I') else ('G'));
	var v_seq_36: seq<char> := ['d'];
	var v_int_59: int := 12;
	v_char_35, v_char_52, v_char_46, v_char_47, v_char_48 := (if ((v_char_49 in v_map_14)) then (v_map_14[v_char_49]) else (v_char_28)), v_char_32, (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_56]) else ((if ((v_char_50 in v_map_15)) then (v_map_15[v_char_50]) else ((if ((|v_seq_34| > 0)) then (v_seq_34[v_int_57]) else ('j')))))), v_char_35, (if ((|v_seq_35| > 0)) then (v_seq_35[v_int_58]) else ((if ((v_char_52 in v_map_17)) then (v_map_17[v_char_52]) else ((if ((|v_seq_36| > 0)) then (v_seq_36[v_int_59]) else ('p'))))));
	print "v_char_36", " ", (v_char_36 == 'm'), " ", "v_char_35", " ", (v_char_35 == 'm'), " ", "v_char_34", " ", (v_char_34 == 's'), " ", "v_char_33", " ", (v_char_33 == 'q'), " ", "v_map_13", " ", (v_map_13 == map['Q' := 7, 'C' := 7, 'D' := 29, 'H' := 26]), " ", "v_map_14", " ", (v_map_14 == map['p' := 'c', 'B' := 'y', 'j' := 'N', 'm' := 'e']), " ", "v_map_11", " ", (v_map_11 == map['q' := 'K', 'z' := 'd']), " ", "v_map_12", " ", (v_map_12 == map['s' := 'w', 'g' := 'G', 'Y' := 'K']), " ", "v_map_10", " ", (v_map_10 == map['t' := map['s' := 'G', 'T' := 'Z', 'k' := 'u', 'o' := 'B']]), " ", "v_int_46", " ", v_int_46, " ", "v_seq_36", " ", (v_seq_36 == ['d']), " ", "v_int_45", " ", v_int_45, " ", "v_map_17", " ", (v_map_17 == map['u' := 'h', 'I' := 'j', 'O' := 'O']), " ", "v_int_49", " ", v_int_49, " ", "v_seq_33", " ", (v_seq_33 == ['q', 'e', 'h', 'J']), " ", "v_int_48", " ", v_int_48, " ", "v_seq_34", " ", (v_seq_34 == ['c']), " ", "v_map_15", " ", (v_map_15 == map['L' := 'F']), " ", "v_int_47", " ", v_int_47, " ", "v_map_16", " ", (v_map_16 == map['g' := 21, 'x' := 8]), " ", "v_seq_35", " ", (v_seq_35 == ['c']), " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_29", " ", (v_char_29 == 'j'), " ", "v_char_28", " ", (v_char_28 == 'm'), " ", "v_seq_25", " ", (v_seq_25 == [map['D' := 'C'], map['r' := 'd'], map['r' := 'f', 'c' := 'O', 'T' := 'X', 'w' := 'c', 'X' := 'q'], map['C' := 'L', 't' := 'a', 'u' := 'l', 'L' := 'u']]), " ", "v_seq_26", " ", (v_seq_26 == [map['D' := 'C'], map['r' := 'd'], map['r' := 'f', 'c' := 'O', 'T' := 'X', 'w' := 'c', 'X' := 'q'], map['C' := 'L', 't' := 'a', 'u' := 'l', 'L' := 'u']]), " ", "v_seq_27", " ", (v_seq_27 == [map['p' := 'c', 'B' := 'y', 'j' := 'N', 'm' := 'e'], map['r' := 'd'], map['r' := 'f', 'c' := 'O', 'T' := 'X', 'w' := 'c', 'X' := 'q'], map['C' := 'L', 't' := 'a', 'u' := 'l', 'L' := 'u']]), " ", "v_seq_28", " ", (v_seq_28 == ['u', 'j', 'o', 'D', 'P', 'M']), " ", "v_int_39", " ", v_int_39, " ", "v_seq_21", " ", v_seq_21, " ", "v_int_38", " ", v_int_38, " ", "v_seq_22", " ", (v_seq_22 == [{'i', 'z', 'O'}, {}, {'Y', 'K'}, {}]), " ", "v_char_32", " ", (v_char_32 == 'j'), " ", "v_char_31", " ", (v_char_31 == 'R'), " ", "v_char_30", " ", (v_char_30 == 'j'), " ", "v_seq_20", " ", v_seq_20, " ", "v_bool_2", " ", v_bool_2, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_int_21", " ", v_int_21, " ", "v_seq_10", " ", (v_seq_10 == ['m', 'O']), " ", "v_int_20", " ", v_int_20, " ", "v_char_49", " ", (v_char_49 == 'u'), " ", "v_char_48", " ", (v_char_48 == 'c'), " ", "v_char_47", " ", (v_char_47 == 's'), " ", "v_char_46", " ", (v_char_46 == 'q'), " ", "v_char_45", " ", (v_char_45 == 'j'), " ", "v_map_1", " ", (v_map_1 == map['a' := 21, 'v' := 3, 'x' := 17]), " ", "v_seq_9", " ", v_seq_9, " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", (v_seq_8 == []), " ", "v_int_57", " ", v_int_57, " ", "v_seq_7", " ", (v_seq_7 == ['m', 'O']), " ", "v_int_56", " ", v_int_56, " ", "v_seq_6", " ", (v_seq_6 == ['m', 'O']), " ", "v_seq_5", " ", (v_seq_5 == ['m', 'O']), " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_59", " ", v_int_59, " ", "v_int_14", " ", v_int_14, " ", "v_int_58", " ", v_int_58, " ", "v_char_52", " ", (v_char_52 == 'j'), " ", "v_char_51", " ", (v_char_51 == 'Q'), " ", "v_char_50", " ", (v_char_50 == 'w'), "\n";
}
