virtual class aclass;

   virtual function void whoami(input string name="noone");
      $display(" I am %s",name);
   endfunction : whoami

   function void sayhello();
      $display(" hola");
   endfunction : sayhello

endclass : aclass
