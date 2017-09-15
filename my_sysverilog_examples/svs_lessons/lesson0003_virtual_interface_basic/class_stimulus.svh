class class_stimulus;

   virtual my_if port_vif;
   int 	   my_aaa, my_bbb;
   
   function new(input int aaa,bbb);
      my_aaa 	     = aaa;
      my_bbb 	     = bbb;      
   endfunction

   task run_t(virtual my_if ports);
      this.port_vif  = ports;
      repeat (1) begin
	 port_vif.some_data  = my_aaa;
	 #2;	 
	 port_vif.some_data  = my_bbb;
	 #2;	 
      end
      this.port_vif  = null;
   endtask
endclass 
