STDLIB=${HOME}/build/agda/lib/current/src
SRC=src
TRGBYTECODE=$(SRC)
TRGLATEX=latex

all: bytecode tex

bytecode: \
    $(TRGBYTECODE)/Data/CausalStream.agdai \
	$(TRGBYTECODE)/PiWare/Atom.agdai \
	$(TRGBYTECODE)/PiWare/Atom/Bool.agdai \
	$(TRGBYTECODE)/PiWare/Padding.agdai \
	$(TRGBYTECODE)/PiWare/Synthesizable.agdai \
	$(TRGBYTECODE)/PiWare/Synthesizable/Bool.agdai \
	$(TRGBYTECODE)/PiWare/Gates.agdai \
	$(TRGBYTECODE)/PiWare/Gates/BoolTrio.agdai \
	$(TRGBYTECODE)/PiWare/Circuit/Core.agdai \
	$(TRGBYTECODE)/PiWare/Circuit.agdai \
	$(TRGBYTECODE)/PiWare/Simulation/Core.agdai \
	$(TRGBYTECODE)/PiWare/Simulation.agdai
#$(TRGBYTECODE)/PiWare/Samples/BoolTrio.agdai \
#$(TRGBYTECODE)/PiWare/ProofSamples/BoolTrio.agdai \
#$(TRGBYTECODE)/PiWare/Correctness.agdai

tex: \
	$(TRGLATEX)/Report/ChapterIntroduction.tex \
	$(TRGLATEX)/Report/ChapterBackground.tex \
	$(TRGLATEX)/Data/CausalStream.tex \
	$(TRGLATEX)/PiWare/Atom.tex \
	$(TRGLATEX)/PiWare/Atom/Bool.tex \
	$(TRGLATEX)/PiWare/Padding.tex \
	$(TRGLATEX)/PiWare/Synthesizable.tex \
	$(TRGLATEX)/PiWare/Synthesizable/Bool.tex \
	$(TRGLATEX)/PiWare/Gates.tex \
	$(TRGLATEX)/PiWare/Gates/BoolTrio.tex \
	$(TRGLATEX)/PiWare/Circuit/Core.tex \
	$(TRGLATEX)/PiWare/Circuit.tex


$(TRGBYTECODE)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

$(TRGLATEX)/%.tex: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) --latex-dir=$(TRGLATEX) --latex $<

clean:
	find -L $(TRGBYTECODE) -name '*.agdai' -delete
	find -L $(TRGLATEX) -name '*.tex' -delete

.PHONY: clean bytecode tex
