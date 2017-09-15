module urandom_play;


   initial begin

      repeat(10) begin
	 $display("$random gets = %0d",$random%3);
      end

      separator();      
      
      repeat(10) begin
	 $display("$urandom gets = %0d",$urandom%3);
      end

      separator();      
      
      repeat(10) begin
	 //$display("{$random} gets = %0d",{$random%3});  //what do the { and } do?
	 $display("{$random} gets = %0d",{$random}%3);
      end  
      
   end
   

   //check the LRM(?) statement that urandom is thread stable and random is not.


   function void separator();
      $display("((((((((((((((((((((((((((((((((((((((((((((((");      
   endfunction
   
   
endmodule // urandom_play
