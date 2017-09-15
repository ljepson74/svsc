`timescale 1ns/1ns

module ram(input  bit         clk,
           input  logic [7:0] din,
           output logic [7:0] dout,
           input  logic [7:0] addr,
           input  logic       ce,
           input  logic       we
          );

   reg [7:0] memory [0:255];

   // Simple ram model
   always @ (posedge clk)
    if (ce)
      if (we)
        memory[addr] <= din;
      else
        dout <= memory[addr];

endmodule
