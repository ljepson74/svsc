module c_top();

   import uvm_pkg::*;

   logic sab_clk;
   logic sab_rst_n;


   initial begin
      waves_task;        //do this first
      sab_clk 	 = 'b0;
      sab_rst_n  = 'b0;

      reset_task;
      fork
	 clk_task;
	 watchdog_task;
      join_any;
   end

   task reset_task;
      begin
	 #5;
	 sab_rst_n  = 'b1;
	 #20;
	 sab_rst_n  = 'b0;
      end
   endtask

   task waves_task;
      $display($time," %m: get me some waves");
      $recordfile("c_waves_top.trn");
      $recordvars("depth=0",c_top);
   endtask

   task clk_task;
      forever begin
	 #10;
	 sab_clk  = ~sab_clk;
      end
   endtask

   task watchdog_task;
      $display($time," %m:  starting watchdog.");
      #1400;
      $display($time," %m:  Finishing now.");
      $finish;
   endtask


   c_dut c_dut_inst(.clk(sab_clk), .rst_n(sab_rst_n), .my_signal(c_if_inst.my_signal));

   //UVM STUFF
   //interface for them to talk
   c_if c_if_inst(.clk(sab_clk));

   initial begin
      uvm_config_db#(virtual c_if)::set(uvm_root::get(), "*", "c_driver_inst", c_top.c_if_inst);
      run_test("c_test");
   end

endmodule // sab_top
