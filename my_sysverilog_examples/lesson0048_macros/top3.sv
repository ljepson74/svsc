`define macro_make_macro1 \
$display "SV is great"; \
`define child_macro $display("C is not bad");
  


  
  module macro_play;
   int my_int1;
   
   initial begin
           my_int1 = 11;
           $display("my_int1=%0d",my_int1);
   end
endmodule // macro_play
