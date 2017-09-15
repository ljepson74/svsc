package branch_pkg;
   import twig_pkg::*;
  // export *::*;
      
   function void branch_hi();
      $display("%m: I am branch");
      twig_hi();
      //leaf_hi();
   endfunction

endpackage : branch_pkg