module my_top();   //attemp to show package, import, include

   import my_package1::*, my_package2::*;

   int valueA;

   function void tellmex();
      $display("\n\n ***************** hello ***************\n\n");
   endfunction

   initial begin
      tellme();
//      my_package1::tellme();
 //     my_package2::tellme();
   end
endmodule : my_top
