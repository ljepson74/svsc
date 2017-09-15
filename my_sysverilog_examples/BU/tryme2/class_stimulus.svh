class class_stimulus;

   virtual memory.tb port_vif;

   function new(virtual memory.tb ports);
      this.port_vif  = ports;      
   endfunction // new
   
   task run_t();
      repeat (3) $display(" hiccup in my pollen ");      
   endtask

endclass //
