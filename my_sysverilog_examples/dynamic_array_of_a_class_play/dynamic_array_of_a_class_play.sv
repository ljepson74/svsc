//This code does nothing in particular, but is an attempt to access/use a dynamic array of class objects.

module dynamic_array_of_a_class_play;

   class_sample class_sample_dyn_array[];
   
   initial begin
      $display($time," %m: STARTING NOW");      

      repeat (3) begin
	 separator("  looping ... ");
	 
	 //make a new one, copying rest of array in.
	 class_sample_dyn_array     = new[(class_sample_dyn_array.size()+1)](class_sample_dyn_array);
	 $display(" Added an object.  Size is %0d", class_sample_dyn_array.size() );	 
	 class_sample_dyn_array[(class_sample_dyn_array.size()-1)]  = new();  //must construct it.	 
         
	 //populate it.
	 class_sample_dyn_array[(class_sample_dyn_array.size()-1)].set_integer($random);  //b/c count from 0 on
	 
	   show_them_all();	   
      end
      

      separator("  FINALE FINALE ");      
      class_sample_dyn_array[1].some_integer  = 777;   //ok.  we can access a specific element like this.

      $display("");      
      show_them_all();     
   end


   function void show_them_all();
      foreach (class_sample_dyn_array[thatone]) begin 
	 $write(" %m:  object:%0d: ",thatone);	    
	 class_sample_dyn_array[thatone].show_all(); 
      end      
   endfunction
   
   function void separator(input string a_string);
      $display("");
      $write($time," %m:***************************checkpoint******  %s", a_string);
   endfunction

   
endmodule // dynamic_array_of_a_class_play

