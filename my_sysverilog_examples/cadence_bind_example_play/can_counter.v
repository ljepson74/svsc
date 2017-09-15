// Verilog HDL for gdglib, can_counter _functional

module can_counter( clk, load, count, dispense, empty);

	input       clk, load, dispense;
	input [7:0] count;
	output      empty;

	reg [7:0]   left; 

	wire        empty = |left;

	always @(negedge clk)
		if (load && !dispense)
			left <= count;
		else if(!load && dispense)
			left <= left - 1;
//Y_2_cycles_after_X_embed_sva: assert property (
 //       @(posedge clk) disable iff (load)
  //      left |-> ##2 left);

endmodule
