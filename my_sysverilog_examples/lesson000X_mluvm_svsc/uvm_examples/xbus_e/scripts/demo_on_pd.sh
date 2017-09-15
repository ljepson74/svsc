#/bin/sh -e
#------------------------------------------------------------------------------

UVM_ACCEL_DIR=`sn_which.sh uvm_accel`
YAMP_DIR=`sn_which.sh uvm_accel/examples/e/yamp`

TEST=$1
RUN_MODE=$2

# driver BFM compile
ncvlog -sv -incdir $QTHOME/etc/tba -messages -vtimescale 1ns/1ns \
  $YAMP_DIR/sv/yamp_master_driver_bfm.sv \
  $QTHOME/etc/tba/scemi_input_pipe.sv $QTHOME/etc/tba/scemi_output_pipe.sv || exit 1

# collector BFM compile
ncvlog -sv -incdir $QTHOME/etc/tba -messages -vtimescale 1ns/1ns \
  $YAMP_DIR/sv/yamp_collector_bfm.sv \
  $QTHOME/etc/tba/scemi_output_pipe.sv || exit 2

#dut compile
ncvlog -sv -messages $TBA_MODE \
  $YAMP_DIR/v/hw_top.v $YAMP_DIR/v/mem_dut.v $YAMP_DIR/v/clkgen.v \
  $YAMP_DIR/sv/yamp_if.sv $QTHOME/etc/SPDclkgen2.v || exit 3


# specman compile. adapter then UVM env
mkdir -p scemi_adapter
sn_compile.sh -h_only -o sn_scemi.h $UVM_ACCEL_DIR/e/uvm_accel_pipes_direct.e \
  || exit 4
gcc -c -m$BITMODE -fPIC -o uvm_accel_pipes.o -DSCEMI_PIPE_DIRECT_C -DIXE -I. -I$QTHOME/include -I$LDVHOME/tools/include/ $UVM_ACCEL_DIR/c/uvm_accel_pipes.c || exit 5
sn_compile.sh $UVM_ACCEL_DIR/e/uvm_accel_pipes_direct.e -D SCEMI_PIPE_DIRECT_C\
  -D IXE -t scemi_adapter -e scemi_adapter -l ./uvm_accel_pipes.o -shlib -exe \
  -o sn_scemi_adapter || exit 6

# compile the UVM env with the top referencing the adapter
sn_compile.sh -shlib -exe -s scemi_adapter/sn_scemi_adapter \
  $YAMP_DIR/e/yamp_top.e -o yamp_top || exit 7

# create specman stub
./yamp_top -c "write stubs -ncsv yamp_top.sv" || exit 8

# stub compile
ncvlog -sv ./yamp_top.sv || exit 9

# elaborate:
ncelab hw_top specman -timescale 1ns/1ns -messages \
 -afile $YAMP_DIR/examples/access.txt || exit 10

mv ncelab.log ncelab.ok.log
ln -fs $QTHOME/lib/x86-lx2-${BITMODE}/libtbadpi.so libdpi.so

#------------------------------------------------------------------------------

SPECMAN_DLIB=./libsn_yamp_top.so
SPECMAN_PRE_COMMANDS="load $YAMP_DIR/$TEST"

export SPECMAN_DLIB
export SPECMAN_PRE_COMMANDS

saDebug $YAMP_DIR/scripts/sa_run.tcl $RUN_MODE

