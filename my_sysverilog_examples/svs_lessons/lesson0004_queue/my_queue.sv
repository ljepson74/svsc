module my_queue;
   int my_int;   
   int q_queue[$];
   
   initial begin
      q_queue  = {8,6};
      show_q();
      q_queue.push_back(1);
      show_q();
      q_queue.push_back(4);
      show_q();
      q_queue.push_back(5);
      my_int  = q_queue.pop_front();
      show_q();
      
   end

   function void show_q();
      for (int iii=0; iii<q_queue.size(); iii++) begin
	 $write("q_queue[%0d]=%0d, ",iii, q_queue[iii]);
      end // for (int iii=0; iii<q_queue.size(); iii++)
      $display(" (my_int=%0d)",my_int);      
   endfunction
   
endmodule // my_queue

