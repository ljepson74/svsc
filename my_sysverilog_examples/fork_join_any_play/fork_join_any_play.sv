

module fork_join_any_play;

   integer variable;

   //needed to put some time in here to get the fork join processes to be interspersed.
   integer top 	=500;
   
   integer waiter1, waiter2;
      
   initial begin
      fork


	 begin : PROC2
	    for (int i=0; i<top; i++) begin
	       waiter2 	= ($urandom%top);
	       $display(" %m:            goodbye in PROC2 i=%0d",i);
	       #waiter2;
	       end
	 end // block: PROC2

	 begin : PROC1
	    for (int i=0; i<top; i++) begin
	       waiter1 			= ($urandom%top);	       
	       repeat (10000) variable 	= $urandom;
	       $display(" %m: hello in PROC1 i=%0d    variable=%0d",i,variable);
	       #waiter1;
	    end
	 end // block: PROC1

      join_any

      $display(" WE LEFT THE JOIN_ANY");

      $finish;

   end


endmodule // fork_join_any_play
