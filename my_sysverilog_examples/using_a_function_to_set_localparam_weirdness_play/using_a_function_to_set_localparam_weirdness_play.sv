module using_a_function_to_set_localparam_weirdness_play;
   parameter SMTHG 	     = 16;
   

   localparam my_localparam  =clogb2(SMTHG);
   
`include "extra.h"

   initial begin
      $display(" STARTING ");
      #4;
      $display(" STARTED my_localparam=%0d ",my_localparam);
   end
   
endmodule // using_a_function_to_set_localparam_weirdness_play
