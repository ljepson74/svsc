module svs_top ();
   import uvm_pkg::*;

//   svs_test svs_test_u = new();

// * WHY DOESN'T THIS WORK
   svs_test svs_test_u;
   initial               //w/ initial works!
     svs_test_u = new();
// * /
   
   initial begin
      run_test("");//svs_test");      
   end
endmodule // svs_top
