odule dice_game;
   
class dice;
   rand int value;        //random variable  
   int stats[1:6]  = {0,0,0,0,0,0};
   
   
   constraint fixed_odds;  //implicit external constraint 
   constraint even;        //explicit external constraint

   function void post_randomize();
      $display(" dice roll is now = %0d", value);      
      stats[value]  = stats[value]+1;
   endfunction

   extern virtual function void show_stats();
endclass


   
   constraint dice::fixed_odds{ value dist {6,5,4,3,2,1}; }
   constraint dice::even{ (value%2)==0; }
   
   function void dice::show_stats();
      foreach (stats[iii]) begin
	 $display("%3d : %3d of %3d : %2.2f%",
		  iii, stats[iii], stats.sum(), (real'(stats[iii])/real'(stats.sum()))*100);
      end
   endfunction

   
   
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
/*
#15  
1) purpose: learn about "extern" to move method and constraint bodies out of classes, to make code cleaner
2) coming off of page 144/5 and 444 of 2009 spec
3) base code 
4) large class with many lines devoted to methods and constraints. tough to skim  
5) move method (task/function) out of class declaration
 extern qualifier means body/implementation/declaration is outside the class
 outside, use "class-name":: to tie it back in.

 6) move constraint out as implicit constraint
 7) run
 8) remove body. run and show warning.  then re-add body
 
 9) add a second constraint make even
 10)move constraint out as explicit constraint
 11) run //FAILS b/c not supported by 12.1 IUS
 12) implicit VS. explict.  
       explicit MUST have declaration.  
       implicit can skip declaration (making empty constraint), warning must be issued
 
i) make prototype
ii) move func out and tie it back in with "class-name"::
 NOTE: declartion much match prototype exactly, except for 'tie-in' (class resolution) w/ class
 note about qualifiers:   extern protected virtual function asdfasdf
  (qualifiers not needed:  local/protected/virtual in this case

implicit  //w/o extern, do not need declaration
explicit  //w/ extern, must have declaration.  Not yet supported by my simulator
 //
 

 
 #17
 purpose: continuing look at "extern" methods
 Coming off of page 145
 Note about return type and class resolution operator. use in example
  
 
 
  444
  637
      
 */