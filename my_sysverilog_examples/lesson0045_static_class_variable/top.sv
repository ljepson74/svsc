module top();

class a_class;

   int number1;
   static int numberN;
   
   function new();
      $display("We won't 'make this' in this example.  ERROR");
      $finish;  //ERROR
   endfunction

   static function string sayhi();   // w/ return value
      return("hola, privet, salut");
   endfunction

   static function void saybye();    // w/o return value
      $display("adios, pahka, adieu");
   endfunction
   
endclass


   initial begin
      $display("\nWe start this. ******************\n\n");
      
      a_class::numberN=5;  //static class variables are like any static variable, created at compile time.
      $display("   NumberN=%0d.", a_class::numberN);
      $display("   function-return=%0s", a_class::sayhi());

      a_class::saybye();
      $display("\n\nWe end this. ******************\n");
   end

endmodule