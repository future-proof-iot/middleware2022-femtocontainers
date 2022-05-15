F12R_SOURCES ?= $(wildcard $(CURDIR)/*.c)
F12R_GENFEMTOC ?= $(RIOTBASE)/build/pkg/femto-container/tools/gen_rbf.py

F12R_BINS = $(F12R_SOURCES:.c=.bin)
F12R_OBJS = $(F12R_SOURCES:.c=.o)

LLC ?= llc
CLANG ?= clang
INC_FLAGS = -nostdinc -isystem `$(CLANG) -print-file-name=include`
EXTRA_CFLAGS ?= -Os -emit-llvm

F12RINCLUDE =  -I$(RIOTBASE)/build/pkg/femto-container/include \
               -I$(RIOTBASE)/sys/include \
	       #

all: $(F12R_BINS)

.PHONY: clean

clean:
	rm -f $(F12R_OBJS) $(F12R_BINS)

INC_FLAGS = -nostdinc -isystem `$(CLANG) -print-file-name=include`

$(F12R_OBJS): %.o:%.c
	$(CLANG) $(INC_FLAGS) \
	        $(F12RINCLUDE) \
	        -Wno-unused-value -Wno-pointer-sign -g3\
	        -Wno-compare-distinct-pointer-types \
	        -Wno-gnu-variable-sized-type-not-at-end \
	        -Wno-address-of-packed-member -Wno-tautological-compare \
	        -Wno-unknown-warning-option \
	        $(EXTRA_CFLAGS) -c $< -o -| $(LLC) -march=bpf -mcpu=v2 -filetype=obj -o $@

$(F12R_BINS): %.bin:%.o
	$(Q)$(F12R_GENFEMTOC) generate $< $@
