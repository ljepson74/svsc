module f_top;
   import uvm_pkg::*;   
   logic clk;

   initial begin
      clk  = 1'b0;
      #80 $finish;      
   end

   f_if  f_if_inst(.clk(clk));      
   f_dut f_dut_inst(.clk(clk), .f_bus(f_if_inst.interface_bus));
   
   always begin clk  = #5 ~clk;  end

   initial begin
      uvm_config_db#(virtual f_if)::set(uvm_root::get(),"*","f_driver_inst_handle", f_if_inst);
      run_test("f_test");
   end
endmodule // f_top
