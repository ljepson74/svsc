Incisive Plan-to-Closure Methodology 
Version 2.0.1, November 2008
Copyright (c) 2007-2010 Cadence Design Systems, Inc. All rights reserved worldwide.
******************************************************************************
* Title: Cadence's XSerial Golden eVC - Examples directory
* Description: 

This directory contains example files that demonstrate the correct usage of
the XSerial eVC

* Demo:

For instructions on how to run the demo in this directory, see the
PACKAGE_README.txt file at the top level of this package.

* Files:

EXAMPLES_README.txt
    This file.
xserial_config_template.e
    Template configuration file - users should start here when writing
    configuration files for real verification environments.
    XSerial eVC configuration file for demonstration
test_1.e
    test-case file for demonstration.
test_multi_reset.e
    test-case example showing multiple resets during a test.
test_error_injection.e
    test-case example demonstrating how to inject errors into a DUT
out_chan.vhd out_chan.v
    Part of example DUT for demonstration. This file contains an output FIFO
    and XSerial output channel core.
in_chan.vhd in_chan.v
    Part of example DUT for demonstration.
dut.vhd dut.v
    Example DUT for demonstration. This DUT is a 3 input, 3 output XSerial
    router. See comments in this file for more details.
tb_xserial.vhd tb_xserial.v
    Example VHDL testbench for demonstration.
sv.do
    Modelsim Macro file for demonstration - initializes Modelsim & creates
    waveform window.
load.do
    Modelsim Macro file for demonstration - performs load and test of e files.
debussy_cmd.txt
    Debussy initialization file for the demo
modelsim.ini
    Modelsim initialization file
vcs.i
    Macro file for vcs demo

