module dice_game;

class dice;
   rand int value, value2;

   constraint six_sides { value>=1  && value<=6; 
                          value2>=1 && value2<=6; 
   }

   constraint seven_eleven { ((value+value2)==7) || ((value+value2)==11); }
   
   function void pre_randomize();      
      $write(" dice ready to be rolled ....");
   endfunction   
   
   function void post_randomize();      
      $display(" dice roll is now = %0d %0d", value, value2);
   endfunction   
endclass

   
   initial begin
      dice my_dice;
      my_dice  = new();

      my_dice.constraint_mode(0);      
      my_dice.six_sides.constraint_mode(1);      
      repeat (5) begin
	 assert (my_dice.randomize() with  { ((value+value2)==2) || ((value+value2)==12); }) else 
	   $fatal(" ERROR: Mister SVS, randomization failed, miserably.");	 
         $display("     ..going to reroll the second die.");
         void'(my_dice.randomize(value2));      	 
	 $display("     ..going to reroll the first die with inline constraint of >=5.");
         void'(my_dice.randomize(value) with {value>=5;});
         $display("\n");       
      end      
   end 

   
endmodule // dice_game
