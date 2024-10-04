COQMFFLAGS := -Q . SLF  -arg "-w -implicit-core-hint-db,-ambiguous-paths"

ALLVFILES := LibAxioms.v LibTactics.v LibEqual.v LibLogic.v LibOperation.v LibBool.v LibReflect.v LibProd.v LibSum.v LibRelation.v LibOrder.v LibNat.v LibEpsilon.v LibInt.v LibMonoid.v LibContainer.v LibOption.v LibWf.v LibList.v LibListExec.v LibListZ.v LibMin.v LibSet.v LibChoice.v LibUnit.v LibFun.v LibString.v LibMultiset.v LibCore.v LibSepTLCbuffer.v LibSepFmap.v LibSepVar.v LibSepSimpl.v LibSepMinimal.v LibSepReference.v Preface.v Basic.v Repr.v Hprop.v Himpl.v Triples.v Rules.v Wand.v WPsem.v WPgen.v WPsound.v Affine.v Arrays.v Records.v Postscript.v Bib.v Tactics.v Heap.v Extra.v Staged.v StagedErr.v

docs:
	coq2html -base SLF -short-names -no-css -d docs *.glob *.v
	perl -pi -e 's@/title>@/title><script src="coq2html.js"></script>@' docs/SLF.Staged.html
	[[ $$OSTYPE == 'darwin'* ]] && open docs/SLF.Staged.html || true

alectryon:
	alectryon -R . SLF --frontend coqdoc --backend webpage Staged*.v --output-directory docs

coqdoc: install-doc

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean docs
