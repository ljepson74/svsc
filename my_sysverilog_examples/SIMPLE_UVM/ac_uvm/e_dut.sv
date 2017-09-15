module e_dut(
	     input clk,
	     input [3:0] d_bus
	     );   

   always@(posedge clk) begin
      $display($time,
	       " e_bus=%4b",
	       e_bus);
   end

endmodule