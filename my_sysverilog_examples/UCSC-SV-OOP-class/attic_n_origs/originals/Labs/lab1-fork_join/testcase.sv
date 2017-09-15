`include "./tasks.sv"

module testcase();

   initial begin
     fork 
       show(3,2);	
       show(5,8);	
       show(10,25);	
       show(23,0);	
       show(6,1);	
     join
     $display("time=%2t: Exiting fork-join...\n", $time);

     show(5, 3);

     #100 $finish;
   end

endmodule
