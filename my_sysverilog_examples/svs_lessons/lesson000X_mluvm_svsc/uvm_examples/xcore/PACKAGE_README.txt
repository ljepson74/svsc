* Title: Cadence XCore Example eVC
* Name: xcore
* Version: 2.0.1
* Requires:
  specman {8.20..}
  xbus_e {2.0..}
  xserial {2.0..}
  uvm_e {1.0..}
* Modified: August-2008
* Category: Golden eVC
* Support: Online Support : http://sourcelink.cadence.com, 
* Documentation: docs/xcore_evc.pdf
* Release notes: docs/xcore_release_notes.txt
* Description:

This is the XCore eVC - one of the Cadence "Golden eVCs". Golden eVCs serve
as small but good examples of eVCs.

The XCore eVC can be used for block-level testing (as demonstrated in the 
main_sve verification environment example) and in system-level testing.

For documentation of the XCore eVC, see docs/xcore_evc.pdf.

* Directory structure:

This package contains the following directories:
 
  e/               - e sources
  docs/            - Documents
  examples/        - Examples of using the XCore eVC
  main_sve/        - Example of a verification environment
  misc/            - Miscellaneous files

* Installation:

      1) Make sure UVM-e is installed - uvm_lib should be in SPECMAN_PATH

         For example:

            setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_lib

           (this is done automatically to Specman users)

      2) Make sure uvm_examples is in SPECMAN_PATH
  
         For example:
             
           setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_examples


* Demo:


For a walkthrough of the demo, see docs/xcore_evc.pdf. 

To run the demo: 

1. Install the XCore package (see Installation). 

2. In a suitable simulation directory, enter the following command:
     `sn_which.sh xcore/demo.sh`   
   
3. If running in NC, source the command script 'xcore.sv' to add signals 
   to SimVision. This file is copied from xcore/examples to the 
   local directory.

4. Issue the simulator's "run" command to run the test.

