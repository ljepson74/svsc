class aaa;
   //protected function new();
   function new(input int anum="555");
      $display("STAN IS IN THE HOUSE ");
   endfunction // new 
endclass // aaa

class bbb extends aaa;
   function new();
      $display("LUSHAN BROUGHT THE PIZZA PIE");
   endfunction // new 
endclass


module top;

   aaa a1;
   bbb b1;

   initial begin
      b1=new();
      $display("**********");
      //a1=new("CARLO");
   end
   
endmodule // top
