module dice_game;

class dice;
   rand int value, value2;

   constraint six_sides { value>=1 && value<=6
				 && value2>=1 && value2<=6; }

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

      my_dice.six_sides.constraint_mode(0);      
      repeat (6) begin
//	 assert (my_dice.randomize()) else
//	   $display(" Mister SVS, randomization failed, miserably.");
	 if (my_dice.randomize()) 
	   ;
	 else
	   $display(" ERROR: Mister SVS, randomization failed, miserably.");
      end
   end
endmodule // dice_game
//Goals
// Working with multiple constraints on a random variable in a class
// using return value of randomize ..conflicting constraints
// constraint_mode() - turning constraints on and off

//add value2
//die -> dice, fix displays
//RUN  - result: bad second roll
//edit original constraint
//RUN - result: good roll
//add second constraint for 7s,11s. 
//           POINT: use ==, not =  EXPRESSIONS, not ASSIGNMENT.
//RUN - maybe get 11, maybe need to increase repeat
//make conflicting constraints
//RUN - see error.
//utilize return val of randomize to print smthg better
//turn off one constraint. RUN. turn off all constraints and turn one back on. RUN
//show and tell
