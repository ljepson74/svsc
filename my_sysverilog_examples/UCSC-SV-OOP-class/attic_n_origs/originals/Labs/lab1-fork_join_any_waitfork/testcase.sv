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

     //Wait until all in-flight threads complete
     wait fork;
     $display("time=%2t: All in-flight threads completed\n", $time);

     show(5, 3);	

     #100 $finish;
   end

endmodule
