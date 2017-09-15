module f_dut(
	     input clk,
	     input [3:0] f_bus
	     );
   always@(posedge clk) begin
      $display($time, " f_bus=%4b",f_bus);   
   end   
endmodule // f_dut
