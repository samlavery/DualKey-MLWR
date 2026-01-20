EC       := easycrypt
EC_FLAGS := -timeout 600 -I . 
# EasyCrypt roots we actually care about
EC_ROOTS := DualPKSig.ec DualPKSig_SimMain.ec DualPKSig_Simulation.ec DualPKSig_Extraction.ec DualPKSig_Reductions.ec

# Phony targets
.PHONY: all ec-check clean

all: ec-check crt_coupled_sig.c

# Type-check each EC root once and drop a .ok stamp file
ec-check: $(EC_ROOTS:.ec=.ok)

%.ok: %.ec
	$(EC) $(EC_FLAGS) $< && touch $@

# Your C module build (adjust CC/CFLAGS/LDFLAGS as needed)
CC      := cc
CFLAGS  := -O2 -Wall -Wextra
LDFLAGS := -lcrypto   # plus any -I/-L for OpenSSL if needed

module_lwr_256_256: crt_coupled_sig.c.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

paper: 
	pdflatex euf_cma_proof_dual_pk.tex

clean:
	rm -f *.ok crt_coupled_sig.c *.eco 
