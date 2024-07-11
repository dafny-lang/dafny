DAFNY=../../../Scripts/dafny

all: DafnyPrelude.bpl

DafnyPrelude.bpl: PreludeSeq.bpl
	# cpp is allergic to primes, so we have to do a song and dance around it
	sed -e "s|'|PRIME|g" -i "" DafnyPreludeCore.bpl PreludeSeq.bpl
	# also, we need to disable preprocessing of Boogie things
	sed -e "s|^#if|//#if|" -i "" DafnyPreludeCore.bpl
	sed -e "s|^#e|//#e|" -i "" DafnyPreludeCore.bpl
	cpp -C -P DafnyPreludeCore.bpl DafnyPrelude.bpl
	sed -e "s|^//#|#|" -i "" DafnyPreludeCore.bpl DafnyPrelude.bpl
	sed -e "s|PRIME|'|g" -i "" DafnyPreludeCore.bpl PreludeSeq.bpl DafnyPrelude.bpl

PreludeSeq.bpl: SequenceModel.dfy
	$(DAFNY) verify SequenceModel.dfy --extract:PreludeSeq.bpl
