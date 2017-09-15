module d_top;

   import uvm_pkg::*;

   logic clk;

   initial begin
      clk = 1'b0;
      #80 $finish;
   end

   always begin      clk = #5 ~clk;         end

   d_dut d_dut_inst( .clk(clk), .d_bus(d_if_inst.interface_bus) );

   d_if d_if_inst(.clk(clk));

   initial begin
      uvm_config_db#(virtual d_if)::set(uvm_root::get(),"*","d_if_inst_handle",d_if_inst);      
      run_test("d_test");      
   end
endmodule // d_top
