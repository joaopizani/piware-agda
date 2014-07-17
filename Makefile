
STDLIB=${HOME}/build/agda/lib/current/src
SRC=src
TRG=$(SRC)


bytecode: $(TRG)/Data/CausalStream.agdai \
	$(TRG)/PiWare/Atom.agdai \
	$(TRG)/PiWare/Atom/Bool.agdai \
	$(TRG)/PiWare/Padding.agdai \
	$(TRG)/PiWare/Synthesizable.agdai \
	$(TRG)/PiWare/Synthesizable/Bool.agdai \
	$(TRG)/PiWare/Gates.agdai \
	$(TRG)/PiWare/Gates/BoolTrio.agdai \
	$(TRG)/PiWare/Circuit/Core.agdai \
	$(TRG)/PiWare/Circuit.agdai \
	$(TRG)/PiWare/Samples/BoolTrio.agdai \
	$(TRG)/PiWare/Simulation/Core.agdai \
	$(TRG)/PiWare/Simulation.agdai \
	$(TRG)/PiWare/ProofSamples/BoolTrio.agdai \
	$(TRG)/PiWare/Correctness.agdai


$(TRG)/%.agdai: $(SRC)/%.lagda
	agda -i $(STDLIB) -i $(SRC) $<

clean:
	find $(TRG) -name '*.agdai' -delete

.PHONY: clean bytecode
