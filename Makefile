
docs:
	coq2html -short-names -no-css -d docs lib/*.glob lib/*.v future/*.v future/*.glob
	perl -pi -e 's@/title>@/title><script src="coq2html.js"></script>@' docs/future.Logic.html
	# [[ $$OSTYPE == 'darwin'* ]] && open docs/future.Logic.html || true

alectryon:
	alectryon -R slf SLF -R lib Lib -R future Future --frontend coqdoc --backend webpage types/*.v lib/*.v --output-directory docs

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
