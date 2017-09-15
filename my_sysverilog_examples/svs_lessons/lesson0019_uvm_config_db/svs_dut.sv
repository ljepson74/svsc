module svs_dut(
	       input logic clk,
	       input logic resetn,
	       input logic [31:0] inbus3,
	       input logic [31:0] inbus2,
	       input logic [31:0] inbus1,
	       input logic [31:0] inbus0,
	       output logic [31:0] outbus
	       );

   always@(posedge clk) begin
      if (!resetn) 
	outbus <= 32'd0;
      else begin
	 outbus <= inbus3 | inbus2 | inbus1 | inbus0;	 
	 $display(" inbus 0=%8x 1=%8x 2=%8x 3=%8x",inbus0, inbus1, inbus2, inbus3);
      end
   end
endmodule