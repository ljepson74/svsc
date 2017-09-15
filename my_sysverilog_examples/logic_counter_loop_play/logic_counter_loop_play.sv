
module logic_counter_loop_play;

   localparam SIZE  =1<<8;


   initial begin
      $display(" STARTED ");
      run_our_loop;
   end


   task run_our_loop;
      logic [7:0] variable;      

      for (variable=0; variable<SIZE; variable=variable+1) begin

	 $display(" %m:  variable = dec:%0d  = hex:%0x",variable, variable);	 
	 
      end // for (variable 					  =0; variable<SIZE; variable=variable+1)
      
	
   endtask
   

endmodule // logic_counter_loop_play

   
