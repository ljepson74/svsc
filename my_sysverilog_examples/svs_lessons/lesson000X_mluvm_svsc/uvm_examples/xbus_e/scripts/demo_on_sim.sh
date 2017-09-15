#/bin/sh -e
#------------------------------------------------------------------------------

#------------------------------------------------------------------------------


UVM_ACCEL_DIR=$QTHOME/gift/uvm_accel-1.0
#UVM_ACCEL_DIR=~/code/uvm/uvm_accel
XBUS_PATH=`sn_which.sh xbus_e`
TBA=$1
TEST=$2
RUN_MODE=$3

if [ -z "$LDVHOME" ]; then
  echo "LDVHOME not set, please set up your environment"
  exit 1
fi


if [ "$TBA" = 1 ]; then
  TBA_MODE="-define TBA_MODE"
  opt=""
else
  TBA_MODE=""
  opt="-access rwc"
fi


SPECMAN_PRE_COMMANDS="config gen -default_generator=IntelliGen"

export SPECMAN_PRE_COMMANDS


# drivers compile
ncvlog -sv -incdir $QTHOME/etc/tba -messages -vtimescale 1ns/1ns \
  $XBUS_PATH/dut/xbus_bus_monitor_bfm.sv    $XBUS_PATH/dut/xbus_master_driver_bfm.sv   \
  $XBUS_PATH/dut/xbus_master_monitor_bfm.sv    $XBUS_PATH/dut/xbus_slave_driver_bfm.sv  \
  $XBUS_PATH/dut/xbus_slave_monitor_bfm.sv    \
  $QTHOME/etc/tba/scemi_input_pipe.vp $QTHOME/etc/tba/scemi_output_pipe.vp -linedebug || exit 1


cp ncvlog.log drivers_ncvlog.log

# dut compile
ncvlog -sv -messages $TBA_MODE -incdir $XBUS_PATH/dut -incdir $XBUS_PATH/sv  \
    $XBUS_PATH/dut/dut_top.v   $XBUS_PATH/examples/xbus_dut_top.sv  || exit 3


cp ncvlog.log dut_ncvlog.log

# specman compile. adapter then UVM env
mkdir -p scemi_adapter
sn_compile.sh -h_only -o sn_scemi.h  $UVM_ACCEL_DIR/e/uvm_accel_pipes_direct.e  || exit 4

gcc -c -m$BITMODE -fPIC -o uvm_accel_pipes.o -DSCEMI_PIPE_DIRECT_C -DUXE -DNO_IXCOM -I. -I$QTHOME/etc/tba  -I$LDVHOME/include/ -I$UVM_ACCEL_DIR/c  -I$CDS_INST_DIR/tools/include  $UVM_ACCEL_DIR/c/uvm_accel_pipes.c || exit 5

sn_compile.sh   $UVM_ACCEL_DIR/e/uvm_accel_pipes_direct.e -D SCEMI_PIPE_DIRECT_C \
  -D UXE -D NO_IXCOM -t scemi_adapter -e scemi_adapter -l ./uvm_accel_pipes.o -shlib -exe \
  -o sn_scemi_adapter || exit 6

 
# compile the env with the top referencing the adapter
if [  "$TBA" = 1 ]; then
sn_compile.sh  -enable_DAC -shlib -exe -s scemi_adapter/sn_scemi_adapter \
  $XBUS_PATH/examples/xbus_arbiter_dut_tba_config.e -o xbus_top || exit 7
else
sn_compile.sh  -enable_DAC -shlib -exe -s scemi_adapter/sn_scemi_adapter \
  $XBUS_PATH/examples/xbus_arbiter_dut_signal_config.e  -o xbus_top || exit 7
fi


# create specman stub
./xbus_top -c "write stubs -ncsv xbus_top.sv" || exit 8

# stub compile
ncvlog -sv ./xbus_top.sv || exit 9

# elaborate:
ncelab xbus_tb_top specman $opt -timescale 1ns/1ns -messages \
 -afile $XBUS_PATH/examples/access.txt || exit 10

mv ncelab.log ncelab.ok.log
ln -fs $QTHOME/lib/libuatba_dc.so libdpi.so



# run:

SPECMAN_DLIB=./libsn_xbus_top.so
SPECMAN_PRE_COMMANDS="load $XBUS_PATH/examples/$TEST;test"

export SPECMAN_DLIB
export SPECMAN_PRE_COMMANDS

ncsim xbus_tb_top -sv_lib libdpi.so -sv_lib libsn_xbus_top.so $RUN_MODE
