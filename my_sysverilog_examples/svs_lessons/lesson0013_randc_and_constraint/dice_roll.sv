module dice_game;

class dice;
   randc int value;     //random-cyclic variable (cycles thru all values before repeating)
   //rand int value;        //random variable

   constraint six_sides { value>=1  && value<=6; } 
   constraint odd { (value%2)==1; }
   function void post_randomize();
      $display(" dice roll is now = %0d", value);
   endfunction   
endclass

   
   initial begin
      dice my_dice;
      my_dice  = new();

      //my_dice.constraint_mode(0);      

      repeat (10) begin
	 assert (my_dice.randomize()) else  $fatal(" ERROR: Mister SVS, randomization failed, miserably.");	 
      end      
   end    

endmodule // dice_game
