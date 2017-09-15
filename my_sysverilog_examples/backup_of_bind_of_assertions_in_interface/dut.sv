module dut(
	   input  logic        clk,
	   input  logic [31:0] data_bus,
	   output logic [7:0]  result
	   );

   logic [31:0] bus_data;

   assign bus_data = ~data_bus;
   
   always@(posedge clk) begin
      result = bus_data % 32'h8;   //implicit casting going on
   end
endmodule : dut