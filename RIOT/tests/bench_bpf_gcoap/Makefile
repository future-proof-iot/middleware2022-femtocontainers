include ../Makefile.tests_common

BLOBS += bpf/counter_fetch_gcoap.bin

USEMODULE += gcoap
USEMODULE += fmt
USEMODULE += embunit
USEMODULE += bpf
USEMODULE += gnrc_ipv6_default

USEMODULE += xtimer
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default

CFLAGS += -I$(CURDIR)

include $(RIOTBASE)/Makefile.include
