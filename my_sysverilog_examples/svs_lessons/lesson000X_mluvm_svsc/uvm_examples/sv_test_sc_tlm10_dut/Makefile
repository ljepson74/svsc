#
# For the definition of the possible targets and macros, 
# please see the README in `ncroot`/tools/systemc/files/make 
#

# Whichever line below is not commented is the default. Override 
# by specifying on the make command line. For example 
#  "make dynamic COMPILER=gnu"

GCC_VERS =
#GCC_VERS = 4.1

COMPILER = native
#COMPILER = gnu

#user can put their own ncsc, elaborator and simulator options
USER_SIM_OPTIONS = 
USER_ELAB_OPTIONS = 
USER_NCSC_OPTIONS = 

# User should list the systemc source files on this macro
SYSTEMC_SOURCES = tbtop.cpp

# User should list the Verilog source files on this macro
VERILOG_SOURCES = test.sv

# User should list the VHDL source files on this macro
VHDL_SOURCES = 

# User should name top level module in the hdl hierarchy
DESIGN_TOP = 

# For user to add their own -D on the compiler command line.
USER_DFLAGS =

# For user to add their own -I on the compiler command line.
USER_IFLAGS =

# For user to add their own -L on the compiler command line.
USER_LFLAGS = 

# For user to add their own libraries to link with the simulation. 
USER_LIBS = 

# Do not modify. Location of the SystemC make files. 
SYSTEMC_MAKEFILES = `ncroot`/tools/systemc/files/make

# User should modify this to point at their own dependency file.
DEPENDENCIES_FILE = Makefile.depends

# Build a shared object to be linked into NC.
dynamic: 
	make -f ${SYSTEMC_MAKEFILES}/Makefile.sc 		        \
	   "SYSTEMC_MAKEFILES=${SYSTEMC_MAKEFILES}"                     \
	   "USER_NCSC_OPTIONS=${USER_NCSC_OPTIONS}"                     \
	   "USER_IFLAGS=${USER_IFLAGS}"                                 \
	   "USER_LFLAGS=${USER_LFLAGS}"                                 \
	   "USER_DFLAGS=${USER_DFLAGS}"                                 \
	   "USER_LIBS=${USER_LIBS}"                                     \
           "DEPENDENCIES_FILE=${DEPENDENCIES_FILE}"                     \
	   "NC_ROOT=`ncroot`" "ARCH=`cds_plat`" "GCC_VERS=${GCC_VERS}" "COMPILER=${COMPILER}"	\
	   "SYSTEMC_SOURCES=${SYSTEMC_SOURCES}" dynamic

# Build a version of the elaborator and the simulator that 
# contain the user's SystemC model statically linked in.
static:
	make -f ${SYSTEMC_MAKEFILES}/Makefile.sc 		        \
	   "SYSTEMC_MAKEFILES=${SYSTEMC_MAKEFILES}"                     \
	   "USER_NCSC_OPTIONS=${USER_NCSC_OPTIONS}"                     \
	   "USER_IFLAGS=${USER_IFLAGS}"                                 \
	   "USER_LFLAGS=${USER_LFLAGS}"                                 \
	   "USER_DFLAGS=${USER_DFLAGS}"                                 \
	   "USER_LIBS=${USER_LIBS}"                                     \
	   "NC_ROOT=`ncroot`" "ARCH=`cds_plat`" "GCC_VERS=${GCC_VERS}" "COMPILER=${COMPILER}" 	\
           "DEPENDENCIES_FILE=${DEPENDENCIES_FILE}"                     \
	   "SYSTEMC_SOURCES=${SYSTEMC_SOURCES}" static

simulate_dynamic: 
	-make -f ${SYSTEMC_MAKEFILES}/Makefile.sc            		\
	   "SYSTEMC_MAKEFILES=${SYSTEMC_MAKEFILES}" 			\
	   "USER_NCSC_OPTIONS=${USER_NCSC_OPTIONS}"                     \
	   "USER_IFLAGS=${USER_IFLAGS}"                                 \
	   "USER_LFLAGS=${USER_LFLAGS}"                                 \
	   "USER_DFLAGS=${USER_DFLAGS}"                                 \
	   "USER_LIBS=${USER_LIBS}"                                     \
	   "NC_ROOT=`ncroot`" "ARCH=`cds_plat`" "GCC_VERS=${GCC_VERS}" "COMPILER=${COMPILER}"  \
	   "DESIGN_TOP=${DESIGN_TOP}"					\
	   "VERILOG_SOURCES=${VERILOG_SOURCES}"				\
	   "USER_NCVERILOG_OPTIONS=${USER_NCVERILOG_OPTIONS}"		\
	   "USER_ELAB_OPTIONS=${USER_ELAB_OPTIONS}"			\
	   "USER_SIM_OPTIONS=${USER_SIM_OPTIONS}"			\
	   "DEPENDENCIES_FILE=${DEPENDENCIES_FILE}"                     \
	   "SYSTEMC_SOURCES=${SYSTEMC_SOURCES}" simulate_dynamic

simulate_static: 
	-make -f ${SYSTEMC_MAKEFILES}/Makefile.sc             		\
	   "SYSTEMC_MAKEFILES=${SYSTEMC_MAKEFILES}" 			\
	   "USER_NCSC_OPTIONS=${USER_NCSC_OPTIONS}"                     \
	   "USER_IFLAGS=${USER_IFLAGS}"                                 \
	   "USER_LFLAGS=${USER_LFLAGS}"                                 \
	   "USER_DFLAGS=${USER_DFLAGS}"                                 \
	   "USER_LIBS=${USER_LIBS}"                                     \
	   "NC_ROOT=`ncroot`" "ARCH=`cds_plat`" "GCC_VERS=${GCC_VERS}" "COMPILER=${COMPILER}"  \
	   "DESIGN_TOP=${DESIGN_TOP}"					\
	   "USER_NCVERILOG_OPTIONS=${USER_NCVERILOG_OPTIONS}"		\
	   "USER_SIM_OPTIONS=${USER_SIM_OPTIONS}"			\
	   "USER_ELAB_OPTIONS=${USER_ELAB_OPTIONS}"			\
	   "VERILOG_SOURCES=${VERILOG_SOURCES}"				\
           "DEPENDENCIES_FILE=${DEPENDENCIES_FILE}"                     \
	   "SYSTEMC_SOURCES=${SYSTEMC_SOURCES}" simulate_static


TARGET_TEST_INSTALL	= simulate_dynamic

test_install: clean use_irun 

use_irun:
	@echo "############################"
	@echo "Use with irun"
	-run_irun
	perl -i -pe 's/^(CDNS-)?(OVM|UVM)-\d+\.\d+.*\n//g' ncsim.log
	perl -i -pe 's/^\(C\).*\n//g' ncsim.log
	grep -v "ncsim> source" ncsim.log | grep -v "DEPUVM" |grep -v "CDNS" | grep -v "Mentor Graphics" | grep -v "Synopsys" | grep -v "Cadence Design" | grep -v "uvm_root.svh" | sed 's,\/.*\/tools,INST_PATH\/tools,' > ncsim_.log
	cp ncsim_.log ncsim.log
	diff ncsim.au ncsim.log > ncsim.log.df
	rm -rf *.df 
	irun -clean

clean:
	make -f ${SYSTEMC_MAKEFILES}/Makefile.sc                        \
	SYSTEMC_MAKEFILES=${SYSTEMC_MAKEFILES} NC_ROOT=`ncroot`         \
        "DEPENDENCIES_FILE=${DEPENDENCIES_FILE}"                        \
	ARCH=`cds_plat` "GCC_VERS=${GCC_VERS}" COMPILER=${COMPILER} clean 
	irun -clean

automatic:
