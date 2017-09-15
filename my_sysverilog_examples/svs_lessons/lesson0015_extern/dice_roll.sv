// "extern"  see IEEE-1800-2009-SystemVerilog-std.pdf  pgs 144-5,444
//  moving methods/constraints out of classes

module dice_game;
   
class dice;
   rand int value;       
   int stats[1:6]  = {0,0,0,0,0,0};
      

   constraint fixed_odds;  //implicit external constraint
   extern constraint even; //explicit external constraint
   
   extern function void post_randomize();
   extern function void show_stats();

endclass


   constraint dice::even { (value%2)==0; }   
   //constraint dice::fixed_odds{ value dist {6,5,4,3,2,1}; }

   function void dice::post_randomize();
      $display(" dice roll is now = %0d", value);      
      stats[value]  = stats[value]+1;
   endfunction
   
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
