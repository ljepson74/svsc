class class_stimulus;

//   virtual my_if.tb port_vif;
   virtual my_if port_vif;

//   function new(virtual my_if.tb ports);
   function new(virtual my_if ports);
      this.port_vif  = ports;
   endfunction

   task run_t();
      repeat (3) begin
	 port_vif.some_data  = $urandom;
	 #2;	 
      end
   endtask
endclass 
