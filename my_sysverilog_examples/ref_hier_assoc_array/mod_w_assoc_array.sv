


module mod_w_assoc_array;


   string aa_string [bit [3:0]];
   int 	  aa_int    [bit [3:0]];

   int    icansee_int 	  = 5;
   string icansee_string  = "VISIBLE";


   initial
     begin
	aa_string[1] 	  = "string stored at 1";	
	aa_string[3] 	  = "string stored at 3";	
	aa_int[1] 	  = 11;	
	aa_int[3] 	  = 33;	
     end
   
endmodule // mod_w_assoc_array
