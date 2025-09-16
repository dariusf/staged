
docs:
	coq2html -short-names -no-css -d docs staged/*.glob staged/*.v shiftreset/*.glob shiftreset/*.v future/*.v future/*.glob types/*.v types/*.glob
	perl -pi -e 's@/title>@/title><script src="coq2html.js"></script>@' docs/future.Logic.html docs/shiftreset.Logic.html docs/types.Logic.html docs/staged.Logic.html docs/staged.Foldr.html docs/staged.Hello.html
	scripts/docgraph.py
	# [[ $$OSTYPE == 'darwin'* ]] && open docs/staged.Logic.html || true

alectryon:
	alectryon -R slf SLF -R staged Staged -R future Future -R types Types -R shiftreset ShiftReset --frontend coqdoc --backend webpage types/*.v staged/*.v shiftreset/*.v future/*.v --output-directory docs

coqdoc: install-doc

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)

Makefile.coq:
	rocq makefile -f _CoqProject -o Makefile.coq

-include Makefile.coq

.PHONY: build clean docs
