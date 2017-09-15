* Title: Cadence's XSerial Golden eVC
* Name: xserial
* Version: 2.0.1
* Requires:
  specman {8.20..}
  uvm_e {1.0..}
* Modified: 2008
* Category: Golden eVC
* Support: Online Support : http://sourcelink.cadence.com, 
* Documentation: docs/xserial_spec.pdf, 
                 docs/xserial_overview.pdf
* Release notes: docs/xserial_release_notes.txt

* Description:

This is the XSerial eVC - one of the Cadence 'Golden eVCs'. Golden eVCs
serve as small, golden examples of eVCs, to teach eVC construction and
methodology.

XSerial is a simple point to point synchronous serial protocol.

* Directory structure:

This package contains the following directories:
 
  e/         - e sources
  docs/      - Documents
  examples/  - Test-case files
  misc/      - Miscellaneous files

* Installation:

      1) Make sure UVM-e is installed - uvm_lib should be in SPECMAN_PATH

         For example:

            setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_lib

           (this is done automatically to Specman users)

      2) Make sure uvm_examples is in SPECMAN_PATH
  
         For example:
             
           setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_examples

* To demo:

1. Install the xserial package eVC (see Installation)

2. In a suitable simulation directory, enter the following command:

   `sn_which.sh xserial/demo.sh` 

    where <language> is one of vhdl or verilog and <sim> is one of mti, 
    vcs, nc or xl

3. If running in NC, source the command script 'xserial.sv' to add signals 
   to Simvision. This file is copied from xserial/examples to the 
   local directory.

4. Issue the simulator's "run" command to run the test.

