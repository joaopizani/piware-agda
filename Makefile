STDLIB=${HOME}/build/agda/lib/current/src
SRC=src

AGDA_MODULES=Category/NaturalT \
			 Category/Functor/Extra \
             Data/CausalStream \
			 Data/HVec \
			 Data/IVec \
			 Data/List/Extra \
			 Data/List/NonEmpty/Extra \
			 Data/RVec \
			 Data/Vec/Extra \
			 Data/Vec/Padding \
			 Data/Vec/Properties/Extra \
			 Data/Fin/Properties/Extra \
			 Data/FiniteTypes/Base \
			 Data/ElimFinite \
			 Function/Bijection/Sets \
			 PiWare/AreaAnalysis \
             PiWare/Atom \
             PiWare/Atom/Bool \
             PiWare/Circuit \
             PiWare/Circuit/Algebra \
             PiWare/Circuit/Typed \
             PiWare/Gates \
             PiWare/Gates/BoolTrio \
			 PiWare/Interface \
             PiWare/Patterns \
             PiWare/Patterns/Typed \
             PiWare/Plugs/Core \
             PiWare/Plugs \
             PiWare/Plugs/Typed \
             PiWare/ProofSamples/AndN \
			 PiWare/ProofSamples/AndN/Typed \
             PiWare/ProofSamples/BoolTrioComb \
			 PiWare/ProofSamples/BoolTrioSeq \
             PiWare/Samples/AndN \
             PiWare/Samples/AndN/Typed \
             PiWare/Samples/BoolTrioComb \
             PiWare/Samples/BoolTrioComb/Typed \
             PiWare/Samples/BoolTrioSeq \
             PiWare/Samples/BoolTrioSeq/Typed \
			 PiWare/Samples/Muxes \
			 PiWare/Samples/Muxes/Typed \
             PiWare/Samples/RippleCarry \
             PiWare/Samples/RippleCarry/Typed \
             PiWare/Simulation \
             PiWare/Simulation/Equality \
             PiWare/Simulation/Properties \
			 PiWare/Simulation/Properties/Plugs \
             PiWare/Simulation/Typed \
             PiWare/Synthesizable \
             PiWare/Synthesizable/Bool \
			 Relation/Binary/Indexed/Extra \
			 Relation/Binary/Indexed/Core/Extra \
			 Relation/Binary/Indexed/Equality/Core \
			 Relation/Binary/Indexed/PreorderReasoning \
			 Relation/Binary/Indexed/EqReasoning


all: $(AGDA_MODULES:%=$(SRC)/%.agdai)


$(SRC)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

$(SRC)/%.agdai: $(SRC)/%.agda
	agda -i $(STDLIB) -i $(SRC) $<

clean:
	find -L $(TRGBYTECODE) -name '*.agdai' -delete

.PHONY: clean

