
#!/bin/sh -v
#
# Script for running xserial demo
# 
#   demo.sh mti|vcs|nc[sim]|xl verilog|vhdl
# =============================================================================

#----------------------------------------------------------------------
# Editable Section
#----------------------------------------------------------------------
package_name="XSerial"

uvm_aop_path=`sn_which.sh xserial`
if [ -n "$uvm_aop_path" ]; then
   # uvm_aop is already in path
   echo ""
else
   echo "Adding UVM_LIB examples library to specman path, for running the demo"
   SPECMAN_PATH=$UVM_LIB/uvm_examples:$SPECMAN_PATH
fi

package_path=`sn_which.sh xserial`
xserial_path=`sn_which.sh xserial`
demo_file="test_1.e"
vlg_hdl_files="$xserial_path/v/*.v"
vhd_hdl_files="$xserial_path/vhdl/in_chan.vhd $xserial_path/vhdl/out_chan.vhd $xserial_path/vhdl/dut.vhd $xserial_path/vhdl/tb_xserial.vhd"
debussy_do_file="$package_path/examples/debussy_cmd.txt"
mti_do_file="$package_path/examples/sv.do"
nc_do_file="$package_path/examples/nc.i"      
vcs_do_file="$package_path/examples/vcs.i"    
vtop="xserial_evc_demo"
#----------------------------------------------------------------------

usage() {
   echo "Usage: $script "
   echo "       $script -test test_name"
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
while [ $# -gt 0 ]; do
   case `echo $1 | tr "[A-Z]" "[a-z]"` in
      -h|-help)
         usage
         exit 1
         ;;
      modelsim|mti|vsim|nc|vcs|xl )
			sim=$1
			;;
      verilog|vhdl)
                        hdl=$1
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


if [ $run_mode = batch ]; then
    gui_flag=""
    echo "run"  >> ./ncsim_run.tcl
    echo "exit" >> ./ncsim_run.tcl 

fi

demo_file=`sn_which.sh $package_path/examples/$demo_file`

 irun \
    -input $nc_do_file \
    $hdl_files \
    $demo_file \
    -NBASYNC \
    -timescale 1ns/1ns \
    $gui_flag \
    $tcl_flag \
    -nosncomp \
    -input ./ncsim_run.tcl \
    -defineall SPECMAN_INCLUDED 



exit
