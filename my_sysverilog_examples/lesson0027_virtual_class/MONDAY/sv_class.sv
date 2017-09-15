class sv_class extends kl_class;
   function void whoami(input string name="kai");
      $display("my name is %0s",name);
   endfunction : whoami
/*   function void whereami();
      $display("SUNNYVALE");
   endfunction
*/
 endclass // kl_class
