module top;

   //logic [7:0][1:0] packed2d;
   logic [1:0][7:0] packed2d;


   initial begin
      packed2d[0] = 8'hFF;
      packed2d[1] = 8'h11;
      packed2d[2] = 8'h55;
      packed2d[7] = 8'hAA;

      $display("packed2d[0]=%0h packed2d[1]=%0h packed2d[7]=%0h",
	       packed2d[0],packed2d[1],packed2d[7]);
   end

endmodule : top
