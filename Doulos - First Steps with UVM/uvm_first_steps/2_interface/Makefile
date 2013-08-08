
##############################################################################
##
##  Makefile for First Steps with UVM
##  
##############################################################################

EXNAME = uvm_interface

SRCS = uvm_interface.sv

INCDIRS = +incdir+..

EXTRA_RUNOPTS = +UVM_NO_RELNOTES

EXTRA_IUS_RUNOPTS    = $(EXTRA_RUNOPTS)
EXTRA_QUESTA_RUNOPTS = $(EXTRA_RUNOPTS)
EXTRA_VCS_RUNOPTS    = $(EXTRA_RUNOPTS)

##############################################################################
##
##  Edit the following to select your version of UVM and installation path
##
##############################################################################

UVM_VER = uvm-1.1
UVM_HOME = /apps/uvm
START_DIR = ${shell pwd}
TARGET_ARCH = linux
SHELL = /bin/sh
MKDIR = mkdir
RM    = rm -rf

##############################################################################
##
##  Variables that point to specific tool installations and options
##
##############################################################################


QUESTA_HOME     = ${shell which vsim | sed -e's/\/$(TARGET_ARCH)\/vsim//'}
QUESTA_LIBS     = $(QUESTA_HOME)/$(UVM_VER)/$(TARGET_ARCH)/uvm_dpi
QUESTA_OPTS     = -novopt  $(EXTRA_QUESTA_OPTS)

IUS_HOME	= ${shell ncroot}
IUS_OPTS        = $(EXTRA_IUS_OPTS)


VCS_OPTS        = -sverilog +acc +vpi -timescale=1ns/1ns $(EXTRA_VCS_OPTS)

##############################################################################
##
##  Compile and run target
##
##############################################################################

.PHONY:	clean

default:
	 #
	 # This make file compiles and runs the code for $(EXNAME)
	 # To use with Incisive, enter:
	 #   make ius	or	make ius_debug
	 #
	 # To use with QuestaSim, enter:
	 #   make questa	or	make questa_debug
	 #
	 # To use with VCS, enter:
	 #   make vcs	or	make vcs_debug
	 #
	 # To remove old simulation files and libraries, enter:
	 #   make clean
	 #
	 #
	exit 1;

ius:
	irun $(IUS_OPTS) -uvmhome $(IUS_HOME)/tools/$(UVM_VER) $(INCDIRS) $(SRCS) $(EXTRA_IUS_RUNOPTS)


ius_debug:
	irun $(IUS_OPTS) -uvmhome $(IUS_HOME)/tools/$(UVM_VER) $(INCDIRS) $(SRCS) +access+rwc -gui $(EXTRA_IUS_RUNOPTS)

ius_std:
	g++ -I$(IUS_HOME)/tools/include -shared -g -o uvm_dpi.so $(UVM_HOME)/src/dpi/uvm_dpi.cc
	irun $(IUS_OPTS) $(INCDIRS) +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv $(SRCS) -sv_lib uvm_dpi $(EXTRA_IUS_RUNOPTS)

ius_std_debug:
	g++ -I$(IUS_HOME)/tools/include -shared -g -o uvm_dpi.so $(UVM_HOME)/src/dpi/uvm_dpi.cc
	irun $(IUS_OPTS) $(INCDIRS) +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv  $(SRCS) +access+rwc -gui -sv_lib uvm_dpi $(EXTRA_IUS_RUNOPTS)

questa:
	qverilog $(QUESTA_OPTS) $(INCDIRS)+$(QUESTA_HOME)/verilog_src/$(UVM_VER)/src $(SRCS) -R -sv_lib $(QUESTA_LIBS) $(EXTRA_QUESTA_RUNOPTS)

questa_debug:
	qverilog $(QUESTA_OPTS) $(INCDIRS)+$(QUESTA_HOME)/verilog_src/$(UVM_VER)/src $(SRCS) -R -sv_lib $(QUESTA_LIBS) -gui $(EXTRA_QUESTA_RUNOPTS)

questa_std:
	g++ -I$(QUESTA_HOME)/include -shared -g -o uvm_dpi.so $(UVM_HOME)/src/dpi/uvm_dpi.cc
	qverilog $(QUESTA_OPTS) $(INCDIRS) +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv $(SRCS) -R -sv_lib uvm_dpi $(EXTRA_QUESTA_RUNOPTS)

questa_std_debug:
	g++ -I$(QUESTA_HOME)/include -shared -g -o uvm_dpi.so $(UVM_HOME)/src/dpi/uvm_dpi.cc
	qverilog $(QUESTA_OPTS) $(INCDIRS) +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv $(SRCS) -R -sv_lib uvm_dpi -gui $(EXTRA_QUESTA_RUNOPTS)

vcs:
	vcs $(VCS_OPTS) -ntb_opts uvm $(INCDIRS) $(SRCS) -R $(EXTRA_VCS_RUNOPTS)

vcs_debug:
	vcs $(VCS_OPTS) -ntb_opts uvm $(INCDIRS) $(SRCS) -R -gui $(EXTRA_VCS_RUNOPTS)

vcs_std:
	vcs $(VCS_OPTS) +acc +vpi $(INCDIRS) +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv  $(SRCS) \
	$(UVM_HOME)/src/dpi/uvm_dpi.cc -CFLAGS -DVCS -R $(EXTRA_VCS_RUNOPTS)

clean:
	@echo cleaning old simulation files and libraries...
	@ -$(RM) INCA_libs csrc simv* work vlog.opt *.bak *.log .simvision ncsim* *.vpd transcript \
	waves.shm *.wlf mylib lib DVEfiles ucli.key irun.key modelsim.ini *.vstf .restart* \
	urgReport cov_work *.so vc_hdrs.h
