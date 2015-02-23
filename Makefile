STDLIB=${HOME}/build/agda/lib/current/src
SRC=src

AGDA_MODULES=Data/CausalStream \
			 Data/List/Extra \
			 Data/List/NonEmpty/Extra \
			 Data/Vec/Extra \
             PiWare/Atom \
             PiWare/Atom/Bool \
             PiWare/Padding \
             PiWare/Synthesizable \
             PiWare/Synthesizable/Bool \
             PiWare/Gates \
             PiWare/Gates/BoolTrio \
             PiWare/Circuit \
             PiWare/Circuit/Typed \
             PiWare/Plugs/Functions \
             PiWare/Plugs \
             PiWare/Plugs/Typed \
             PiWare/Simulation \
             PiWare/Simulation/Typed \
             PiWare/Patterns \
             PiWare/Patterns/Typed \
             PiWare/Samples/BoolTrioComb \
             PiWare/Samples/BoolTrioComb/Typed \
			 PiWare/Samples/Muxes \
			 PiWare/Samples/Muxes/Typed \
             PiWare/Samples/BoolTrioSeq \
             PiWare/Samples/BoolTrioSeq/Typed \
             PiWare/Samples/AndN \
             PiWare/Samples/AndN/Typed \
             PiWare/Samples/RippleCarry \
             PiWare/Samples/RippleCarry/Typed \
             PiWare/ProofSamples/BoolTrioComb \
             PiWare/ProofSamples/AndN




all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda -i $(STDLIB) -i $(SRC) $<

clean:
	find -L $(TRGBYTECODE) -name '*.agdai' -delete

.PHONY: clean

