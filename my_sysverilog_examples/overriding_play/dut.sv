//imitates punit.v

module dut
  (
   input            rst,
   
   input      [7:0] in_a,
   input      [7:0] in_b,
   output reg [8:0] out_ab
   );
   
	   
   assign out_ab = in_a + in_b;
   
endmodule
