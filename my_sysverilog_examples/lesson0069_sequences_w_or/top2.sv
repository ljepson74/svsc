module top;
   bit clk;
   bit req, ack;
   initial begin
      clk=0; req=1;
      repeat(20) begin
         #10;
         clk=~clk;
      end
      $finish;
   end
   initial begin
      ack=0;
      #24;
      ack=1;
   end
   initial begin
      $monitor($time,"*** req=%1b ack=%1b",req,ack);
   end

   sequence request;
      req;
   endsequence
   sequence acknowledge;
      ##1 (ack==1'bZ);
   endsequence

   property handshake;
      @(posedge clk) request |-> acknowledge;
   endproperty

   assert property (handshake) begin
      $display($time, "Property hit. * ** ***");
   end else begin
      $display($time, "Property NO hit. * ** ***");
   end

endmodule
