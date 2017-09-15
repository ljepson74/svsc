module testcase();

   task automatic print(input int   delay, 
                        input [7:0] count
                       );

       #(delay) $display("time=%2t: Delay=%2d Count=%2d", $time, delay, count);
   endtask

   initial begin
     fork 
       print(3,2);	//process_a
       print(5,8);	//process_b
       print(6,1);	//process_c
     join_none

     #10;

     fork 
       print(2,5);	//process_c
       print(4,7);	//process_d
       print(9,8);	//process_e
     join_any
     
     $display("time=%2t: Exiting fork-join...\n", $time);

     //Wait until all in-flight threads complete
     wait fork;
     $display("time=%2t: All in-flight threads completed\n", $time);

     print(5, 3);	//process_f

     #100 $finish;
   end

     final begin
           //$display("time=%2t: Right before finishing...\n", $time);
           end

     final begin
           //$display("Inside the final block. Executing the print() task...\n");
           //print(5, 8);
     end

endmodule
