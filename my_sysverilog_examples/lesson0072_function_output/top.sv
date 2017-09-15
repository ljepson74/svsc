module top;
   int result;

   function outputter(output int number);
      number=3;
   endfunction


   initial begin
      outputter(.number(result));
      $display("result is ....... %0d",result);
   end

endmodule
