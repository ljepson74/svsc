//2 - WORKING
`define numberargs 2
`define part1(arg_type,arg_name)  arg_type arg_name;
`define part2(arg_name,arg_value) arg_name = arg_value;  $display("%0s=%0d",`"arg_name`",arg_value);
`define part3(arg_type, arg_name,arg_value) arg_type arg_name; initial begin arg_name = arg_value;  $display("%0s=%0d",`"arg_name`",arg_value); end

`define wholey(arg_number) 


module macro_play;

   //int my_int1;
   //int my_int2;
   `part1(int, my_int1)
   `part1(int, my_int2)

   `part3(int, my_int4, 444)

   initial begin
//     my_int1 = 11;
//     my_int2 = 22;
//     $display("my_int1=%0d",my_int1);
//     $display("my_int2=%0d",my_int2);
      `part2(my_int1, 111)
      `part2(my_int2, 222)

      `wholey(numberargs)

   end
endmodule // macro_play
