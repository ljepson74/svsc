//1) shortint, int, longint.   default.  settings(2-state). rollover.  -numbers
//1) take screenshot of output
//2) make each on unsigned
//2) check results
//3) talk thru the results


module tb;
   integer             my_integer;   
   
   shortint unsigned   my_shortint;
   int      unsigned   my_int;
   longint  unsigned   my_longint;
   //integer my_integer;

   initial begin
      my_integer = -1; my_shortint  = -1;  my_int = -1;  my_longint = -1;
      #1;
      my_integer =  0; my_shortint  =  0;  my_int =  0;  my_longint =  0;
      #1;
      my_integer =  1; my_shortint  =  1;  my_int =  1;  my_longint =  1;
      #1;
      my_integer =  2; my_shortint  =  2;  my_int =  2;  my_longint =  2;
      #1;
      my_integer = (2**16)-1; my_shortint  = (2**16)-1;  my_int =  (2**16)-1;  my_longint =  (2**16)-1;
      #1;      
      my_integer = (2**16)+1; my_shortint  = (2**16)+1;  my_int =  (2**16)+1;  my_longint =  (2**16)+1;
      #1;
   end

   initial begin
      $monitor("%0d:\t>my_shortint=(hex:%16x)(%10d) / my_int=(hex:%16x)(%10d) / my_longint=(hex:%16x)(%10d) ",my_integer, my_shortint,my_shortint,my_int,my_int,my_longint,my_longint);      
   end

endmodule

