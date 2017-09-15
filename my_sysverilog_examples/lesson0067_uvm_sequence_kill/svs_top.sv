module svs_top ();
   import uvm_pkg::*;

   svs_test svs_test_u = new();
   //svs_test2 svs_test_u2 = new();

   initial begin
      run_test("");//svs_test");
   end
endmodule // svs_top
