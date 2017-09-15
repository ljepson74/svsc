module dice_game;

class dice;
   rand int value;        //random variable
   int stats[1:6] = {0,0,0,0,0,0};

//   constraint six_sides { value>=1  && value<=6;    }
//   constraint fixed_odds{ value dist {6,5,4,3,2,1}; }
//   constraint fixed_odds{ value dist {6:/5,5,4,3,2,1}; }
/*   constraint fixed_odds{ value dist {
				      6:/5,  // 1/(5+1+1+1+1+1)
				      5:/1,  // 1/(5+1+1+1+1+1)
				      4:/1,  // 1/(5+1+1+1+1+1)
				      3:/1,  // 1/(5+1+1+1+1+1)
				      2:/1,  // 1/(5+1+1+1+1+1)
				      1:/1   // 1/(5+1+1+1+1+1)
				      }; }
*/
/*   constraint fixed_odds{ value dist {
				      6:=5,  // 1/(5+1+1+1+1+1)
				      5:=1,  // 1/(5+1+1+1+1+1)
				      4:=1,  // 1/(5+1+1+1+1+1)
				      3:=1,  // 1/(5+1+1+1+1+1)
				      2:=1,  // 1/(5+1+1+1+1+1)
				      1:=1   // 1/(5+1+1+1+1+1)
				      }; }
*/ 
//   constraint fixed_odds{ value dist {[6:4]:/1, 3:/1, 2:/1, 1:/1}; }// BAD RANGE [low:high]. error
//   constraint fixed_odds{ value dist {[4:6]:/1, 3:/1, 2:/1, 1:/1}; }  
   constraint fixed_odds{ value dist {[4:6]:=1, 3:/1, 2:/1, 1:/1}; }  
   
   function void post_randomize();
      $display(" dice roll is now = %0d", value);
      stats[value]  = stats[value]+1;
   endfunction

   function void show_stats();
      foreach (stats[iii]) begin
	 $display("%3d : %3d of %3d : %2.2f%",
		  iii, stats[iii], stats.sum(), (real'(stats[iii])/real'(stats.sum()))*100);
      end
   endfunction

endclass


   initial begin
      dice my_dice;
      my_dice  = new();

      repeat (100) begin
	 assert (my_dice.randomize()) else  begin 
	    $display(" ERROR: Mister SVS, randomization failed, miserably.");	 
	    $fatal(1);	    
	 end
      end

      my_dice.show_stats();
   end

   
endmodule // dice_game




//got rid of fatal warning
//

//1)
/*
Hello, welcome to the SystemVerilogShow.  Today we are going to look at distributions.  Distributions can be used in constaint blocks to control the distribution of results.
 The distribution set, specified with dist is ...

 */
 // distributions (dist) can be used in constraints for specifying sets of weighted values
// "distribution set" - comma separated list of values (or expressions or ranges)

//2)
// dist is a constraint.   swap the following
//   constraint six_sides { value>=1  && value<=6;    }
//   constraint fixed_odds{ value dist {6,5,4,3,2,1}; }
// offscreen, add func to show spread.
// by default, each has a weight of 1
// run

//3) weights
//  :=  versuse  :/
//   ADD A DIST (the swap we did showed this) w/ default weight of 1
// run and prove

//   USE WEIGHTS - nb: weights, not percentages
// show := versus :/


