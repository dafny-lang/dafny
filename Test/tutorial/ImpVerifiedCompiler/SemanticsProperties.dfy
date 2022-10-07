include "Semantics.dfy"

lemma star_one_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires R(conf1,conf2)
	ensures star(R,conf1,conf2)
{
}

lemma star_one<T(!new)>()
	ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(R,conf1,conf2)
{
}

least lemma star_trans_pre<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2)
	ensures  star(R,conf2,conf3) ==> star(R,conf1,conf3)
{
	if conf1 == conf2 {}
	else {
		var confi :| R(conf1, confi) && star(R,confi, conf2);
		assert star(R,confi,conf2);
		star_trans_pre(R,confi,conf2,conf3); 
	}
}

lemma star_trans_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2) 
	requires star(R,conf2,conf3)
	ensures star(R,conf1,conf3)
{
	star_trans_pre(R,conf1,conf2,conf3);
}

lemma star_trans<T(!new)>()
	ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3)
{
	forall R, conf1, conf2, conf3: T ensures (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3) {
		if star(R,conf1,conf2) {
			star_trans_pre(R,conf1,conf2,conf3);
		}
	}
}

lemma combine_reductions<T(!new)>()
	ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(R,conf1,conf2)
	ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3)
{
	star_one<T>();
	star_trans<T>();
}

lemma plus_star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires plus(R,conf1,conf2)
	ensures star(R,conf1,conf2)
{
	var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
	star_one_sequent(R,conf1,conf1');
	star_trans_sequent(R,conf1,conf1',conf2);
}

lemma star_plus_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2)
	requires plus(R,conf2,conf3)
	ensures plus(R,conf1,conf3)
{
	if conf1 == conf2 {
	} else {
		var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
		var conf2' :| R(conf2, conf2') && star(R,conf2', conf3);
		star_one_sequent(R,conf2,conf2');
		star_trans_sequent(R,conf1',conf2,conf2');
		star_trans_sequent(R,conf1',conf2',conf3);
	}
}

least lemma star_inf_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires star(R,conf1,conf2)
	requires inf(R,conf2)
	ensures inf(R,conf1)
{
	if conf1 == conf2 {}
	else {
		var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
		star_inf_trans(R,conf1',conf2);
	}
}
	
greatest lemma infseq_if_all_seq_inf_pre<T(!new)>(R: (T,T) -> bool, conf: T)
	requires forall conf2: T :: star(R,conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
	ensures inf(R,conf)
{
	assert star(R,conf,conf);
	var B :| R(conf,B);
	assert R(conf,B);
	assert inf(R,B) by { infseq_if_all_seq_inf_pre(R,B); }
}

lemma infseq_if_all_seq_inf<T(!new)>(R: (T,T) -> bool, conf: T)
	requires all_seq_inf(R,conf)
	ensures inf(R,conf)
{
	infseq_if_all_seq_inf_pre(R,conf);
}
