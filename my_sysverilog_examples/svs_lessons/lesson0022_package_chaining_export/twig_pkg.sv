package twig_pkg;
   import leaf_pkg::leaf_hi;
   //export leaf_pkg::*;
   
   function void twig_hi();
      $display("%m: I am twig");
      leaf_hi();
   endfunction

endpackage : twig_pkg