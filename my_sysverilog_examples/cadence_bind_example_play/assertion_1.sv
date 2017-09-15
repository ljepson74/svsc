module assertion( clk, load, count, dispense, empty);

	input       clk, load, dispense;
	input [7:0] count;
	output      empty;



sva_1: assert property (
        @(posedge clk) disable iff (load)
        count |-> ##4 count);

endmodule
