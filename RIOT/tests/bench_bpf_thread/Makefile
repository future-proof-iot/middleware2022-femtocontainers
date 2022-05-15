include ../Makefile.tests_common

BLOBS += bpf/thread_log.bin

USEMODULE += embunit
USEMODULE += bpf

USEMODULE += xtimer
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default

CFLAGS += -I$(CURDIR)

include $(RIOTBASE)/Makefile.include
