program test(memory tbf0);
   initial begin
      class_stimulus class_stimulus_u  = new(tbf0.tb);
      fork
	 class_stimulus_u.run_t();
      join_none
      #122;
      $finish;   
   end

/*   initial begin
      tbf0.addr 		    <= 8'h55;
      #10;
   end */
endprogram // test
