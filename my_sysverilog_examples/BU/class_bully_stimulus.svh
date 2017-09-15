class class_bully_stimulus;
   
   integer out_age;   
   integer out_iq;   
   integer out_shoesize;   
   
   function new ();
   endfunction

   task go();      
      repeat (3) begin
	 #40;
	 out_age      = $urandom;
	 out_iq       = $urandom;
	 out_shoesize = $urandom;
      end
   endtask // go
     
endclass
