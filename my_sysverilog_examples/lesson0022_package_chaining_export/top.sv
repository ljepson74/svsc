//example showing package chaining with export
module top;
   trunk m_trunk;
   logic a_signal, clk;

   initial begin
      m_trunk = new();
      clk = 1'b0;
      a_signal = 1'b0;
      #21;
      a_signal = 1'bX;
      #20;
      $finish;
   end

   always begin  clk = #2 ~clk;   end

   mod mod(.*);
   
endmodule // top
