module dice_game;
   
class a_die;
   rand int value;   

   constraint six_sides { value>=1 && value<=6; }

   function void pre_randomize();
      $display("  start.");      
   endfunction
   function void post_randomize();
      $display("%m  done.");
      $display("%m die roll = %0d",value);
   endfunction

endclass



   initial begin
      a_die my_die;      
      int junk;
      
      my_die  = new();

      repeat(4) begin
	 my_die.randomize();
	 $display(" die roll = %0d",my_die.value);      
      end

   end // initial begin   

endmodule // dice_game


//1.
// make module, class inside
// create instance, randomize
// add constraint
// loop.  add post_randomize
// loop.  add pre_randomize


// randomize()
// illegal constraint
// use return of randomize to discover failure

// use post_randomize
