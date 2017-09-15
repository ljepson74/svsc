//bounded, 
module queue2;
   string my_string;
   string q_queue[$:3];

   initial begin
      q_queue  = {"A","L","O","E"};
      show_q();
      q_queue.push_front("G");        
      show_q();                      //{"G","A","L","O","E"}
      my_string  = q_queue.pop_front();

      show_q();                      //{"A","L","O","E"}
      q_queue.push_front("H");
      show_q();                      //{"H","A","L","O","E"}
      
      $display("left   =%0d",$left(q_queue));  
      $display("right  =%0d",$right(q_queue));     
      $display("low    =%0d",$low(q_queue));      
      $display("high   =%0d",$high(q_queue));      
      $display("size                =%0d",$size(q_queue));      
      $display("dimensions          =%0d",$dimensions(q_queue));      
      $display("unpacked_dimensions =%0d",$unpacked_dimensions(q_queue));      
 
   end

   function void show_q();
      $write("q_queue=");
      for (int iii=0; iii<q_queue.size(); iii++) begin
	 $write("[%3d]",iii);
      end
      $display("");  $write("         ");
      for (int iii=0; iii<q_queue.size(); iii++) begin
	 $write("%3s  ",       q_queue[iii]);
      end
      $display(" (my_string=%0s)\n",my_string);
   endfunction
endmodule // my_queue

