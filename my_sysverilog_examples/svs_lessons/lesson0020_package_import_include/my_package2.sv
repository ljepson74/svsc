package my_package2;

   int valueA;

   function void tellme();  //this should not be seen by my_top
      $display("\n\n ******* hola *******\n\n");
   endfunction

endpackage : my_package2
