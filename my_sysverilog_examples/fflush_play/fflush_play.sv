module fflush_play;

   integer handle;
   integer randynum;

   initial begin
      //open a file
      //write to it
      handle 	   = $fopen("gingerbread.txt", "w");
      
      
      repeat (5) begin
	 randynum  =$urandom;
	 $display("we give %0d",randynum);	 
	 $fdisplay(handle,"we give %0d", randynum);
      end

      //A
      //try to flush it/ clear it.. doesn't work.  hmpth
      //$fflush(handle);      

      //B
      //so let`s close and reopen to clear it.   
      $fclose(handle);   
      handle 	   = $fopen("gingerbread.txt", "w");      
      $fclose(handle);

      //now look at the file, it will be empty
   end
endmodule

