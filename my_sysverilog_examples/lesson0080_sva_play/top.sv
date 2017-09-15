module top;
   parameter SIZE=3;

   logic [(SIZE-1):0] setme;
   bit clk;

   always begin
      clk = #5 ~clk;
   end
   initial begin
      $monitor($time," setme=%0b",setme);
      clk =0;
      setme=3'b000;
      repeat (10) @(posedge clk);
      setme=3'b111;
      repeat (5) @(posedge clk);
      setme=3'b101;
      repeat (10) @(posedge clk);
      $finish;
   end

   generate begin : cp_length
      for (genvar numbr=0;numbr<SIZE;numbr++) begin
	 cp_high10clks : cover property (@(posedge clk) setme[numbr][*9]);
      end
   end
   endgenerate
endmodule : top


/*
   as0_i : assert property (@(posedge clk) !sig0);
      
   cp0_ii  :  cover property (@(posedge clk) sig0 [*4]);
   cp0_iii :  cover property (@(posedge clk) sig0 [*5]);

   cp0_busses :  cover property (@(posedge clk) |{bus1,bus2} [*3]);

   as0_iv  : assert property (@(posedge clk) sig0 [*4]);
   as0_v   : assert property (@(posedge clk) sig0 [*5]);
*/
