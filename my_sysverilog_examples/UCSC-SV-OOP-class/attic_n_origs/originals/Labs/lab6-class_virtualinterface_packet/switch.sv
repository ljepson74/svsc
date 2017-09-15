module switch(//inputs
              input  bit	 clk,
              input  wire [47:0] src_addr,
	      input  wire [31:0] src_data,

              //outputs
	      output reg  [47:0] dst_addr,
	      output reg  [31:0] dst_data
	     );

   always @(posedge clk) begin
      dst_addr <= src_addr + 1;
      dst_data <= src_data + 1;
   end

endmodule
