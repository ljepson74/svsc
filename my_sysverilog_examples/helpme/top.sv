module top();

   bit          clk;
   logic [31:0] data_bus;
   logic [7:0]  result;

   initial begin
      clk = 0;
      $monitor("-> in:%0x. then %0x. out got %0x", data_bus, dut.bus_data, result);
      #50;
      $finish;
   end
   always begin
      #5 clk = !clk;
      data_bus = {$urandom};
   end

   in_if in_if_u(.clk(clk));

   dut dut(.clk(clk),
	   .data_bus(data_bus),
	   .result(result)
	   );
endmodule : top

