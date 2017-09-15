module dice_game;

class a_die;
   rand int value;

   constraint six_sides { value>=1 && value<=6; }

   function void pre_randomize();      
      $write(" die ready to be rolled ....");
   endfunction   
   
   function void post_randomize();      
      $display(" die roll is now = %0d", value);
   endfunction   
endclass

   
   initial begin
      a_die my_die;
      my_die  = new();

      repeat (4) begin
	 my_die.randomize();	 
      end
      
   end 

   
endmodule // dice_game
