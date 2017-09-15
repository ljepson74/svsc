`include "./tasks.sv"

module testcase();

   initial begin
     fork 
       show(3,2);	
       show(5,8);	
       show(10,25);
       show(23,0);
       show(6,1);	
     join_any
     $display("time=%2t: Exiting fork-join...\n", $time);

     //disbale all in-flight threads
     disable fork;
     $display("time=%2t: All in-flight threads are disabled...\n", $time);

     show(5, 3);	

     #100 $finish;
   end

endmodule
