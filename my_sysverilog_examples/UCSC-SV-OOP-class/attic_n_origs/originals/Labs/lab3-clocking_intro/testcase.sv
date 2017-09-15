program testcase();

   bit clk;
   bit system_clk;

   //Free running clock


   //Specify the default clocking
   clocking cb @ (posedge clk);
   endclocking


   initial begin
      $display("t=%5d: Current time is %5t ns", $time, $time);

      #10; // <--- this is 10ns!
      $display("t=%5d: Current time is %5t ns", $time, $time);

      //##10; // <--- this is not 100ns!
      //$display("t=%5d: Current time is %5t ns", $time, $time);

      repeat(10) @(cb); // <--- same as ##10 
      $display("t=%5d: Current time is %5t ns", $time, $time);

      repeat(10) @(posedge clk); // <--- same as ##10 
      $display("t=%5d: Current time is %5t ns", $time, $time);

      $finish;
   end

endprogram
