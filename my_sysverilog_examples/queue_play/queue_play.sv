module queue_play;


   integer my_queue[$]={1,4,6,5};
   

   initial begin  : lets_play_w_queue
      
      $display($time," %m: STARTING OUR QUEUE PLAY SIM");   

      #4;      
//      show_queue;           
      #4;
      my_queue[$] = {0,1,2,3};      
//      show_queue;      

      
   end
   
/*
   function void show_queue;
      for (int iii=0; iii<my_queue.size(); iii++) begin
	 $display($time," %m: my_queue[%0d]=%0d",iii,my_queue[iii]);	 
      end
   endfunction //
*/

endmodule // queue_play

//note. Cadence IUS8.2 does not currently support:
//    = { }; 
// to clear a queue. It seems to not support this to set a queue either
// my_queue.delete( ); 
// should be used to clear it
