program test(my_if this_if);
   initial begin
      class_stimulus class_stimulus_u  = new(this_if.tb);
      fork
	 class_stimulus_u.run_t();
      join_none
      #122;
      $finish;   
   end
endprogram // test
