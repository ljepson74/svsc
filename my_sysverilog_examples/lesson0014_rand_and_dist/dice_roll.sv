module dice_game;

// distributions (dist) can be used in constraints for specifying sets of weighted values
//    which control the distribution of results
// distribution set - comma separated list of values (or expressions or ranges)
   
class dice;
   rand int value;        //random variable  
   int stats[1:6]  = {0,0,0,0,0,0};
   
//   constraint six_sides { value>=1  && value<=6; }
     constraint fixed_odds{ value dist {6,5,4,3,2,1}; }
/*     constraint fixed_odds{ value dist {
				      6:/50,  //50/(50+1+1+1+1+1)
				      5:/1,   // 1/(50+1+1+1+1+1)
				      4:/1,   // 1/(50+1+1+1+1+1)
				      3:/1,   // 1/(50+1+1+1+1+1)
				      2:/1,   // 1/(50+1+1+1+1+1)
				      1:/1    // 1/(50+1+1+1+1+1)
				      }; }
      constraint fixed_odds{ value dist {
				      6:=50,  //50/(50+1+1+1+1+1)
				      5:=1,   // 1/(50+1+1+1+1+1)
				      4:=1,   // 1/(50+1+1+1+1+1)
				      3:=1,   // 1/(50+1+1+1+1+1)
				      2:=1,   // 1/(50+1+1+1+1+1)
				      1:=1    // 1/(50+1+1+1+1+1)
				      }; }
*/ 

//   constraint fixed_odds{ value dist {[4:6]:/1, 3:/1, 2:/1, 1:/1}; }  
//   constraint fixed_odds{ value dist {[4:6]:=1, 3:/1, 2:/1, 1:/1}; }  
//   constraint fixed_odds{ value dist {[6:4]:=1, 3:/1, 2:/1, 1:/1}; }// BAD RANGE [low:high]. error

  
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
