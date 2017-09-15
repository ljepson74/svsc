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

TBA_MODE="-define TBA_MODE"


xeDesignBit $BITMODE
DIR_UXE=c_uxe_$BITMODE


mkdir -p $DIR_UXE
cd  $DIR_UXE



#
# Compile and elaborate the environment
#
###########################################

ixcom +sv -incdir $AXIS_HOME/etc/tba +define+TBA_MODE \
   $XBUS_PATH/dut/dut_top.v   $XBUS_PATH/examples/xbus_dut_top.sv \
   -incdir  $XBUS_PATH/dut -incdir $XBUS_PATH/sv  \
  $QTHOME/etc/tba/scemi_input_pipe.vp $QTHOME/etc/tba/scemi_output_pipe.vp \
  +dut+xbus_tb_top +iscDelay+clkgen \
  +bc+scemi_input_pipe+scemi_output_pipe \
  +nowarn+UVM_IGNORE_DELAY -ua -$BITMODE || exit 1



irun -c -sv -uvm -sncompargs -enable_DAC -messages -I$AXIS_HOME/etc/tba \
   $XBUS_PATH/examples/xbus_arbiter_dut_tba_config.e  $XBUS_PATH/examples/test_tba.e \
  -snstage scemi_adapter $UVM_ACCEL_DIR/e/uvm_accel_pipes_direct.e \
   $UVM_ACCEL_DIR/c/uvm_accel_pipes.c -snheader sn_scemi.h -endsnstage \
  -defineall SCEMI_PIPE_DIRECT_C \
  -f xc_work/irun.f -afile $XBUS_PATH/examples/access.txt -Intelligen || exit 2

mv ixcom.log uxe.ok.log || exit 3

ln -fs $AXIS_HOME/lib/${BITMODE}bit/libuatba.so libdpi.so






#
# Run
#
###########################################

xeDebug  $RUN_MODE --ncsim -sv_lib libdpi.so -- $XBUS_PATH/scripts/xc_run.tcl


