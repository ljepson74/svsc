typedef bit [3:0] fourbit_t;

module top;

   logic [3:0] fourlogic;
   bit   [3:0] fourbit;
   byte        a_byte;
   
   function void showme();
      $display("fourlogic=%4b  fourbit=%4b  a_byte=%8b",fourlogic,fourbit,a_byte);
   endfunction

   initial begin
      fourlogic = 4'b1x0z;
      fourbit   = 4'b1111;  //no warning of x/z assignment to 2-state variable

      fourbit   = bit'(fourlogic);
      
      fourbit   = fourbit_t'(fourlogic);

      fourbit   = fourbit_t'(int'((fourlogic)));
   end

endmodule