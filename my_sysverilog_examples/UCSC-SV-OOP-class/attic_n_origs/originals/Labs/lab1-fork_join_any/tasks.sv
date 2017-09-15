task show(input int   delay,
          input [7:0] count
         );

       if(delay < 5)
            #(delay) $display("time=%2t: Delay=%2d Count=%2d. Short Process Running...", $time, delay, count);
       else if(delay >= 5 && delay < 10)
            #(delay) $display("time=%2t: Delay=%2d Count=%2d. Medium Process Running...", $time, delay, count);
       else if(delay >= 10 && delay < 15)
            #(delay) $display("time=%2t: Delay=%2d Count=%2d. Long Process Running...", $time, delay, count);
       else #(delay) $display("time=%2t: Delay=%2d Count=%2d. Zombie Process Running...", $time, delay, count);
    
endtask
