//module class;  //ERROR
//module top;
module CLASS;

//class class;  //ERROR
class keyword_class;
   //bit class;   //ERROR      
//   bit CLASS; //okay

   bit fred; //case-insensitive
   bit FRED; //case-insensitive, both are allowed
endclass

   initial begin
      $display("**************START***************");
      $display("************** END ***************");
   end

endmodule
