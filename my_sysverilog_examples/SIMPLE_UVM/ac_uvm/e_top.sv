module e_top;
   import uvm_pkg::*;   

   logic clk;      

   initial begin
      clk = 1'b0;      
      #80 $finish;  
   end

   always begin      clk = #5 ~clk;         end

   e_dut e_dut_inst( .clk(clk), .e_bus(d_if_inst.interface_bus) );

   //UVM stuff
   e_if e_if_inst(.clk(clk));

   initial begin
      uvm_config_db#(virtual d_if)::set(uvm_root::get(),"*","e_driver_inst_handle", e_if_inst);
      run_test("e_test");      
   end
endmodule