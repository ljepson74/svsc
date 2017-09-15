module dice_game;

class dice;
   randc int value;

   constraint six_sides { value>=1  && value<=6; } 
   constraint odds      { (value%2)==1; } 
      
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
/*

1. explain:  single die.  roll it
2. explain rand v. randc   c for cyclic
3. change to randc
4. show that we cycle thru
5. add another constraint of only odds

 */ 
  