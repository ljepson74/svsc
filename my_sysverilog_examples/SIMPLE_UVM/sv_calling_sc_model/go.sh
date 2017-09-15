#!/bin/sh -f
#
#package_path=${ML_LKJ3}
package_path=.
gui="-gui -access +rw"


# ?? what is -uvmtop SV: , SC: for?  Can't compiler figure that out.
# ?? also, Do we need a module to be the top,  eg:  -top <a module> ?

irun \
    $package_path/p_env.cpp  \
    $package_path/xunit_testbench_and_test.sv \
    -sysc -scsynceverydelta on -tlm2 \
    -top xunit_testbench_and_test \
    -uvmtop SV:xunit_tb \
    -uvmtop SC:sc_p_env \
    $*

