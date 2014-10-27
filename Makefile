STDLIB=${HOME}/build/agda/lib/current/src
SRC=src

AGDA_MODULES=Data/CausalStream \
             PiWare/Utils \
             PiWare/Atom \
             PiWare/Atom/Bool \
             PiWare/Padding \
             PiWare/Synthesizable \
             PiWare/Synthesizable/Bool \
             PiWare/Gates \
             PiWare/Gates/BoolTrio \
             PiWare/Circuit/Core \
             PiWare/Circuit \
             PiWare/Plugs/Core \
             PiWare/Plugs \
             PiWare/Simulation/Core \
             PiWare/Simulation \
             PiWare/Samples/BoolTrioComb \
             PiWare/Samples/BoolTrioSeq \
             PiWare/Patterns/Core \
             PiWare/Patterns \
             PiWare/Samples/RippleCarry \
             PiWare/ProofSamples/BoolTrioComb \
             PiWare/Samples/AndN \
             PiWare/ProofSamples/AndN


all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda -i $(STDLIB) -i $(SRC) $<

clean:
	find -L $(TRGBYTECODE) -name '*.agdai' -delete

.PHONY: clean

