LIBCILKPROF = $(LIB_DIR)/libcilkprof.a

CILKPROF_SRC = cilkprof.c cc_hashtable.c strand_hashtable.c util.c
CILKPROF_OBJ = $(CILKPROF_SRC:.c=.o)

-include $(CILKPROF_OBJ:.o=.d)

CFLAGS += $(TOOL_CFLAGS)
LDFLAGS += $(TOOL_LDFLAGS)
LDLIBS += $(TOOL_LDLIBS)

ifeq ($(PARALLEL),1)
CFLAGS += -DSERIAL_TOOL=0 -fcilkplus
endif

ifeq ($(TOOL),cilkprof)
LDFLAGS += -lrt
endif

.PHONY : cleancilkprof

default : $(LIBCILKPROF)
clean : cleancilkprof

$(LIBCILKPROF) : $(CILKPROF_OBJ)

cilkprof.o : # CFLAGS += -flto
cilkprof.o : # LDFLAGS += -lrt

cleancilkprof :
	rm -f $(LIBCILKPROF) $(CILKPROF_OBJ) $(CILKPROF_OBJ:.o=.d*) *~
