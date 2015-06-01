STDLIB=${HOME}/build/agda/lib/current/src
SRC=src

AGDA_MODULES=Category/NaturalT \
			 Category/Functor/Extra \
             Data/CausalStream \
			 Data/List/Extra \
			 Data/List/NonEmpty/Extra \
			 Data/Vec/Extra \
			 Data/Vec/Padding \
			 Data/Vec/Properties/Extra \
			 Data/HVec \
			 Data/IVec \
			 Data/RVec \
			 Function/Bijection/Sets \
			 Relation/Binary/Indexed/Core/Extra \
			 Relation/Binary/Indexed/Extra \
			 Relation/Binary/Indexed/Equality/Core \
			 Relation/Binary/Indexed/PreorderReasoning \
			 Relation/Binary/Indexed/EqReasoning \
             PiWare/Atom \
             PiWare/Atom/Bool \
             PiWare/Synthesizable \
             PiWare/Synthesizable/Bool \
			 PiWare/Interface \
             PiWare/Gates \
             PiWare/Gates/BoolTrio \
             PiWare/Circuit \
             PiWare/Circuit/Algebra \
             PiWare/Plugs/Core \
             PiWare/Plugs \
             PiWare/Simulation \
             PiWare/Simulation/Equality \
             PiWare/Simulation/Properties \
			 PiWare/AreaAnalysis \
             PiWare/Patterns \
             PiWare/Samples/BoolTrioComb \
			 PiWare/Samples/Muxes \
             PiWare/Samples/BoolTrioSeq \
             PiWare/Samples/AndN \
             PiWare/Samples/RippleCarry \
             PiWare/ProofSamples/BoolTrioComb \
             PiWare/ProofSamples/AndN \
             PiWare/Circuit/Typed \
             PiWare/Plugs/Typed \
             PiWare/Simulation/Typed \
             PiWare/Patterns/Typed \
             PiWare/Samples/BoolTrioComb/Typed \
			 PiWare/Samples/Muxes/Typed \
             PiWare/Samples/BoolTrioSeq/Typed \
             PiWare/Samples/AndN/Typed \
             PiWare/Samples/RippleCarry/Typed \
			 PiWare/ProofSamples/AndN/Typed



all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda -i $(STDLIB) -i $(SRC) $<

clean:
	find -L $(TRGBYTECODE) -name '*.agdai' -delete

.PHONY: clean

