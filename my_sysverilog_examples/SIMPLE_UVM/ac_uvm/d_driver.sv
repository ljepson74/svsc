class d_driver;

   virtual d_if d_if_ghost;
      
   function new();      
      $display(" %m:  Great. Instantiated this driver.");
   endfunction

  task run();
     $display(" %m: we are really running now");
     #14;
     d_if_ghost.interface_bus  = 4'bZXZX;
     #14;
     d_if_ghost.interface_bus  = 4'b1010;
     #14;
   endtask

endclass : d_driver
