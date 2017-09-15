******************************************************************************
* Title: Cadence's XBus Golden eVC
* Name: xbus_e
* Version: 2.1
* Requires:
  specman {8.20..}
  uvm_e {1.0..}
* Modified: 2011
* Category: Golden UVC
* Support: Online Support : http://sourcelink.cadence.com, 
* Documentation: docs/xbus_evc.pdf
* Release notes: docs/xbus_release_notes.txt

* Description:

This is the XBus UVC - one of Cadence 'Golden UVCs'. Golden UVCs serve
as small, golden examples of UVCs, to teach UVC construction and methodology.


* Directory structure:

This package contains the following directories:
 
  e/         - e sources
  docs/      - Documents
  examples/  - Testcase files
  v/         - Verilog implementation of DUT

* Installation:

    1) Make sure UVM-e is installed - uvm_lib should be in SPECMAN_PATH

         For example:

            setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_lib

           (this is done automatically to Specman users)

    2) Make sure uvm_examples is in SPECMAN_PATH
  
         For example:
             
           setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_examples


* To demo:

1. Install the xbus_e package (see Installation)

  
   If running the acceleration demo, 

      1. Add to SPECMAN_PATH

      2. Make sure these environment variables are defined correctly:

             CDS_TOOLS
	     LDVHOME

      3. Edit scripts/setup.csh, setting environment variables, and run 
         the script

   
2. In a suitable simulation directory, enter the following command:

   `sn_which.sh xbus_e/demo.sh`

3. If running in NC, source the command script 'xbus.sv' to add signals 
   to Simvision. This file can be copied from xbus/examples to the 
   local directory.

4. Issue the simulator's "run" command to run the test.

5. For acceleration demo, running on the simuator, run:

    `sn_which.sh xbus_e/demo.sh` ACCEL_SIM


   
6. For acceleration demo, running on the emulator, run:

    `sn_which.sh xbus_e/demo.sh` ACCEL_PXP
