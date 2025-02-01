
docs:
	coq2html -short-names -no-css -d docs lib/*.v lib/*.glob types/*.v types/*.glob
	perl -pi -e 's@/title>@/title><script src="coq2html.js"></script>@' docs/types.Logic.html
	# [[ $$OSTYPE == 'darwin'* ]] && open docs/types.Logic.html || true

alectryon:
	alectryon -R slf SLF -R lib Lib -R types Types --frontend coqdoc --backend webpage types/*.v --output-directory docs

coqdoc: install-doc

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

-include Makefile.coq

.PHONY: build clean docs
