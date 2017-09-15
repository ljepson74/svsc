module top;
   bit clk;
   bit [3:0] bus;
   initial begin
      clk=0;
      repeat(10) begin #10; clk=~clk; end
   end

   sequence tuesday;
      bus==6;
   endsequence
   sequence tuesday2;
      ##1 bus!=6;
   endsequence

   property night;
      @(bus) tuesday |-> tuesday2;
      //bus!=4'hF;
   endproperty

   initial begin
      $monitor($time,"*** bus=%1h",bus);
      repeat (19) begin
         bus=$urandom();
         assert property (night) begin
            $display("Property hit. * ** ***");
         end else begin
            $display("Property NO hit. * ** ***");
         end
         //@(posedge clk);
         #10;
      end
      $finish;
   end

endmodule
