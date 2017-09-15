module top;
   logic clk;
   int   count=10;

   initial
      clk=0;
   always
     #1 clk = ~clk;

   initial begin
      $display($time," ************* START");
      repeat (10) @(posedge clk);
      $display($time," ************* START main now");

      fork
         begin
            repeat(33) begin
               $display($time," Tine1:       waiting for posedge clk. count=%0d",count);
               @(posedge clk);
               count++;
            end
         end
         begin
            $display($time,"       Tine2: waiting for count>=10");
            @(posedge clk iff (count>=10));
            $display($time,"       Tine2: waited for count>=10.  count=%0d",count);
         end
      join_any

      $display($time," ************* END");
      $finish;
   end
endmodule
