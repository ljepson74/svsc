program test(my_if this_if);
   initial begin
      class_stimulus class_stimulus_u  = new(.aaa(4), .bbb(3)); //this_if);
      class_stimulus class_stimulus_u2 = new(.aaa(7), .bbb(9)); //this_if);

      class_stimulus_u.run_t(this_if);
      #100;      
      class_stimulus_u2.run_t(this_if);

      #122;
      $finish;   
   end
endprogram 
