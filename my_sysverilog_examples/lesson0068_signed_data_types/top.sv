module top;

   integer          my_integer;
   integer unsigned my_uinteger;
   //bit [31:0]  my_unsigned;

   initial begin
      $monitor($time,"**Show values: my_integer=(bin)%32b=(dec)%0d   my_uinteger=(bin)%32b=(dec)%0d",my_integer,my_integer,my_uinteger,my_uinteger);
      #5;
      my_integer =0;
      my_uinteger=my_integer;
      #5;
      my_integer ={32{1'b1}};
      my_uinteger=my_integer;
      #5;
      my_integer ={1'b0,{31{1'b1}}};
      my_uinteger=my_integer;
      #5;
      my_integer =-5;
      my_uinteger=my_integer;
      #5;
   end

endmodule
