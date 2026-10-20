CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra
TARGET = pager_tx

ifeq ($(shell pkg-config --exists uhd && echo yes),yes)
UHD_FLAGS = -DWITH_UHD $(shell pkg-config --cflags --libs uhd)
endif

$(TARGET): pager_tx.c
	$(CC) $(CFLAGS) -o $@ $< $(UHD_FLAGS) -lm

clean:
	rm -f $(TARGET)

.PHONY: clean
