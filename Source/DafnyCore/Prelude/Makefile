DAFNY=../../../Scripts/dafny

all: DafnyPrelude.bpl

DafnyPrelude.bpl: Sequences.bpl
	# cpp is allergic to primes, so we have to do a song and dance around it
	sed -e "s|'|PRIME|g" -i "" PreludeCore.bpl Sequences.bpl
	# also, we need to disable preprocessing of Boogie things
	sed -e "s|^#if|//#if|" -i "" PreludeCore.bpl
	sed -e "s|^#e|//#e|" -i "" PreludeCore.bpl
	# Extract Boogie from the model verified in Dafny
	cpp -C -P PreludeCore.bpl DafnyPrelude.bpl
	# Undo the song and dance with primes and Boogie preprocessing directives
	sed -e "s|^//#|#|" -i "" PreludeCore.bpl DafnyPrelude.bpl
	sed -e "s|PRIME|'|g" -i "" PreludeCore.bpl Sequences.bpl DafnyPrelude.bpl

Sequences.bpl: Sequences.dfy
	$(DAFNY) verify Sequences.dfy --extract:Sequences.bpl
	# Remove trailing spaces that the Boogie pretty printer emits
	sed -e "s| *$$||" -i "" Sequences.bpl
