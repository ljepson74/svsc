module a_top;

   import uvm_pkg::*;

   logic clk;
   logic reset;

   a_if a_if_inst(clk);

   a_dut a_dut(.clk(clk),
	   .reset(reset),
	   .my_input(a_if_inst.a_signal)
	   );

   initial begin
      clk    = 0;
      reset  = 1;
      fork : top_stuff
	 begin
	    forever begin 	
//	       $display(" %m: clk toggled clk=%0b",clk);
	       #5ns clk = ~clk;
	    end
	 end
	 begin
	    #20;
	    reset  = 0;
	    #110;
	    $finish;
	 end // fork branch
      join_any
   end // initial begin

   initial begin
      uvm_config_db#(virtual a_if)::set(uvm_root::get(), "*", "this_is_my_tag", a_top.a_if_inst);
      run_test("a_test");
   end

   initial begin
      $display($time," Record waves for this simple uvm testbench");
      $recordfile("a_waves_top.trn");
      $recordvars("depth=0", a_top);
   end

endmodule // top
