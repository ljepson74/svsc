* Title: Sequences layering example, many-to-many layering 
* Name: ex_mtm_layering
* Version: 2.0.1
* Requires: 
  specman {8.20..}
  uvm_e {2.0.1..}
* Category: Example package
* Modified: 2008
* Documentation: UVM-e Methodology manual 
* Comments to: support@cadence.com
* Description:

  Demonstrates implementation of Many-to-Many layering - Several upper-layer
  items are concatenated into one lower-layer item. An upper-layer can also 
  be fragmented over two lower-layer item.


  Read the details of layering methodology in the UVM-e Methodology manual.

* Installation:
 

      1) Make sure UVM-e is installed - uvm_lib should be in SPECMAN_PATH

         For example:

            setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_lib

           (this is done automatically to Specman users)

      2) Make sure uvm_examples is in SPECMAN_PATH
  
         For example:
             
           setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm/uvm_examples

* To demo:

1. Install the ex_mtm_layering package (see Installation)

2. In a suitable simulation directory, enter the following command:

   `sn_which.sh ex_mtm_layering`/demo.sh

3. Issue the "test" command to run the test.



