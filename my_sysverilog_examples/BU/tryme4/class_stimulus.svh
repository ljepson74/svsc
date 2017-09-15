class class_stimulus;

   virtual memory.tb port_vif;

   function new(virtual memory.tb ports);
      this.port_vif  = ports;      
   endfunction // new
   
   task run_t();
      repeat (3) begin
	 $display(" hiccup in my pollen ");  
	 port_vif.some_data  = $urandom;
	 #2;	 
      end
   endtask
endclass //
