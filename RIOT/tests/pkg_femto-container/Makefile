include ../Makefile.tests_common

F12R_DIRS += $(CURDIR)/application
F12R_BLOBS += application/fletcher32_fc.bin

USEMODULE += embunit
USEPKG += femto-container

USEMODULE += xtimer
USEMODULE += saul
USEMODULE += saul_reg
USEMODULE += saul_default

CFLAGS += -I$(CURDIR)

include $(RIOTBASE)/Makefile.include
