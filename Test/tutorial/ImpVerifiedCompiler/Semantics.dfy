least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

least predicate plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	(exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

predicate all_seq_inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	forall conf2: T :: star(R,conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
}

greatest predicate inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	exists confi: T :: R(conf,confi) && inf(R,confi)
}




