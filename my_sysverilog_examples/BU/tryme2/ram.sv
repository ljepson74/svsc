module ram(memory mif);

   reg [7:0] memr [0:255];

   //read
   assign mif.data_o 	  = (~mif.rw && mif.ce) ? memr[mif.addr] : 8'h00;   

   //write
   always@(posedge mif.clk) begin
      if (mif.ce && mif.rw) begin
	 memr[mif.addr]  = mif.data_i;
      end
   end

   initial begin
      $monitor($time, " mif.addr=%2x ", mif.addr);
   end  

 endmodule // ram
