module randomizing_subsection_of_reg_array_play;

   my_class my_obj;


   initial begin
      my_obj  = new();

      $display("%m: Looking into why in another testbench, the dist I use for a subfield of a reg doesn't seem to be having the correct effect.");
      $display("%m: It seems like, there, that if there is any value in the dist, then the odds are 50/50.");
      $display("%m:   i.e.  :=1, :=1000  will give 50/50 results, but   :=0, :=1000  will give the expected  0/100 results ");


      repeat (10) begin
	 assert(my_obj.randomize());
	 my_obj.show;
      end
   end

endmodule // randomizing_subsection_of_reg_array_play
