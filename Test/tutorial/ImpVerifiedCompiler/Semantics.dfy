least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

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

predicate all_seq_inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	forall conf2: T :: star(R,conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
}

greatest predicate inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	exists confi: T :: R(conf,confi) && inf(R,confi)
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


