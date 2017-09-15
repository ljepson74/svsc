//create a datatype which contains
// 1) the plusarg
// 2) comment describing it
// z) min,max, legal values

`include "test_base.svh"
module top;
   import uvm_pkg::*;

   test_base test_base;
   initial begin
      $display(">>>> START TEST.");
      test_base = new(); //use create

      #1000;
      $display(">>>> END TEST.");
   end

   initial begin
      run_test();
   end
endmodule : top
