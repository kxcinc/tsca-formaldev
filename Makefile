include Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.tz: %.v Makefile.coq
	./maketz $(basename $<) $@