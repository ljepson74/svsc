//delete, insert, shuffle, sort
module queue1;
   int my_int;   
   int q_queue[$];
   
   initial begin
      q_queue  = {1,2,3,4,5,6,7};
      show_q();
      q_queue  = {q_queue[0:2],333, q_queue[3:$]};      
      show_q();      
/*    q_queue.sort();      
      show_q();
      q_queue.push_back(1);
      show_q();
      q_queue = {};      
      q_queue.push_back(3);
      q_queue = q_queue.delete;      
      q_queue.push_back(9);
      show_q();
  */    
   end

   function void show_q();
      for (int iii=0; iii<q_queue.size(); iii++) begin
	 $write("q_queue[%0d]=%0d, ",iii, q_queue[iii]);
      end // for (int iii=0; iii<q_queue.size(); iii++)
      $display(" (my_int=%0d)",my_int);      
   endfunction
endmodule // my_queue

