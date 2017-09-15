module dpi_play;

   import "DPI-C" function int factorial(input int my_input);   
   import "DPI-C" tell_story = function void tell_the_story();
           
      initial
	begin
	   $display($time," %m: here we are.");
	   factorial(7);
	   tell_the_story();	   
	end
   
endmodule // dpi_play
