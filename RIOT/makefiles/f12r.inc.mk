.PHONY: f12r/%

f12r/%: $$(if $$(filter f123/clean,$$@),,pkg-prepare)
	$(Q)for app in $(F12R_DIRS); do \
    /usr/bin/env -i RIOTBASE=$(RIOTBASE) \
    	Q=$(Q) QQ=$(QQ) "$(MAKE)" --no-print-directory -C $${app} $*; \
    done;

clean: f12r/clean

# Make the F12R_BLOBS depend on the APPS
$(F12R_BLOBS): $(F12R_DIRS)
# Make sure they are all built
$(F12R_DIRS): f12r/all

# Make sure the BLOBS are built
BUILDDEPS += $(F12R_BLOBS)
# Add the femto-container blobs to BLOBS
BLOBS += $(F12R_BLOBS)

