module d_dut(
	     input clk,
	     input [3:0] d_bus
	     );   

   always@(posedge clk) begin
      $display($time,
	       " d_bus=%4b",
	       d_bus);
   end

endmodule