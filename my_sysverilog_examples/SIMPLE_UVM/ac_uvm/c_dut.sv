module c_dut(
	      input clk,
	      input rst_n,
	      input my_signal
	      );

   logic 	    the_other;

   assign the_other  = my_signal;

   always@(my_signal) begin
      $display($time," my_signal=%0b",my_signal);
   end

endmodule // c_dut
