class my_class;

   rand int var1;
   rand int var2;
   
   constraint c_1 { var1>0; }
endclass

class higher;  //a class can have another class inside of it.

   class lower;
   endclass
endclass


//////////////////////////////////////
module top;
   my_class my_class;

initial begin
   my_class=new();

   my_class.var1=1;

   as_myassert : assert(my_class.randomize(var2));
   $display("ALL DONE");
end   
endmodule // top


/*   as_myassert : assert(my_class.randomize(var2)) begin
      $display("PASS: var2=%0d",my_class.var2);
   end else begin
      $display("FAIL: b_number=%0d",my_class.var2);
   end
*/