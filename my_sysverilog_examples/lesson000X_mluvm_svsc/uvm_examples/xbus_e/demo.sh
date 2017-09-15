
#!/bin/sh -f
#
# Script for running xbus demo
# 
#   demo.sh mti|vcs|nc[sim] verilog|vhdl
# =============================================================================

#----------------------------------------------------------------------
# Editable Section
#----------------------------------------------------------------------
package_name="XBus"

uvm_lib_path=`sn_which.sh xbus_e`
if [ -n "$uvm_lib_path" ]; then
   # uvm_lib is already in path
   echo ""
else
   # add uvm_lib to path
   echo "Adding UVM_LIB examples to specman path, for running the demo"
   SPECMAN_PATH=$UVM_LIB/uvm_examples:$SPECMAN_PATH
fi


package_path=`sn_which.sh xbus_e`
xbus_path=`sn_which.sh xbus_e`
demo_file="test_1.e" 
vlg_hdl_files="$xbus_path/v/tb_xbus.v"
vhd_hdl_files="$xbus_path/vhdl/tb_xbus.vhd"
debussy_do_file="$package_path/examples/debussy_cmd.txt"
mti_do_file="$package_path/examples/sv.do"
vcs_do_file="$package_path/examples/vcs.i"   
nc_do_file="$package_path/examples/nc.i"    
nc_waves="$package_path/examples/xbus.sv"
vtop="xbus_evc_demo"
abstract_l=SIGNAL

#----------------------------------------------------------------------


usage() {
   echo "Usage: $script "
   echo "       $script [ACCEL_SIM] -test test_name"
   echo "       $script -h[elp]"
}

script=`basename $0`

# =============================================================================
# Find package path
# =============================================================================
export package_path
if [ -n "$package_path" ]; then
   if [ -h $package_path ]; then  # Replace link name with dereference name
      package_path=`\ls -l $package_path | sed -e 's/ \+/ /g' | cut -d" " -f11`
   fi
else
   echo "$script: Package $package_name  not found"
	exit 1
fi

# =============================================================================
# Default args
# =============================================================================
sim=nc
hdl=verilog
gui_flag="-gui"
run_mode=interactive
tcl_flag=""

# =============================================================================
# Get args
# =============================================================================
while [ "$#" -gt 0 ]; do
   case $1 in
      -h|-help)
         usage
         exit 1
         ;;

      ACCEL_SIM)
         abstract_l=ACCEL_SIM
         clib=$CLIBDIR/libuatba_dc.so
         demo_file="test_tba.e"
        ;;
      ACCEL_PXP)
         abstract_l=ACCEL_PXP
         clib=$CLIBDIR/libuatba.so
         demo_file="test_tba.e"
      ;;
      -test)
		        demo_file="$2"
                        shift
                        ;;
      -mode)
                        run_mode=$2
                        shift
                        ;;
      -run)
                        run_file="$2"
                        shift
                        ;;
   
      esac
	shift       
done


do_file="$nc_do_file"


if [ -n "$run_file" ]; then
   cat $do_file > sim_cmd.txt
   cat $run_file >> sim_cmd.txt 
   do_file="sim_cmd.txt"
fi

hdl_files="$vlg_hdl_files"

echo ""  >> ./ncsim_run.tcl

if [ $run_mode = batch ]; then
    gui_flag=""
    echo "run"  >> ./ncsim_run.tcl
    echo "exit" >> ./ncsim_run.tcl 

fi


if [ $abstract_l = ACCEL_SIM ]; then    
  $package_path/scripts/demo_on_sim.sh 1 $demo_file $gui_flag
  exit
fi


if [ $abstract_l = ACCEL_PXP ]; then
   $package_path/scripts/demo_on_pxp.sh $demo_file $gui_flag
   exit
fi

demo_file=`sn_which.sh $package_path/examples/$demo_file`
 
cat $nc_waves > xbus.sv    


 irun \
    -input $nc_do_file \
    $vlg_hdl_files  \
    $demo_file \
    -NBASYNC \
    -timescale 1ns/1ns \
    $gui_flag \
    $tcl_flag \
    -nosncomp  \
    -input ./ncsim_run.tcl \
    -defineall SPECMAN_INCLUDED 
 


exit
