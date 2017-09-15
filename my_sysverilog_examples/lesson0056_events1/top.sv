module top;

   event tuesday;

   initial begin      
      repeat(3) begin
         #20;
         ->tuesday;
         $display("          triggered %0t",$time);
      end
   end

   initial begin
      #100;
      $finish;
   end
   
   always begin
      //#10;
      @(tuesday);  //goes 3 times
      //@(tuesday.triggered); // 1 time 
      //wait(tuesday.triggered); // infinite times
      //if(tuesday.triggered)
        $display("tuesday is TRUE %0t",$time);
      //    else
    //    $display("tuesday is FALSE %0t",$time);
   end

endmodule