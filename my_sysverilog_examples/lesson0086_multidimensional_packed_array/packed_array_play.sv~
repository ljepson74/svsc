module packed_array_play;

   
   bit [3:0] [7:0] packed_a;
   bit [7:0] 	     unpacked_a [3:0];
   

   initial begin
      set_packed_a(8'h41);
      read_packed_a();

      $display($time,"\n\n packed_a[0]=%0x",packed_a[0]);
      

   end // initial begin


   function void set_packed_a;
      input logic [7:0] junk;

      for (int i=0; i<=3; i++) begin
	 packed_a[i]  = junk;
	 junk 	      = junk+ 1 ;  //$urandom;	 
      end      
   endfunction


   function void read_packed_a;
      for (int j=0; j<=3; j++) begin
	 $display("packed_a[%0d]=0x:%0x = bin:%0b",j, packed_a[j], packed_a[j]);
      end
   endfunction
   function void read_unpacked_a;
      for (int jj=0; jj<=3; jj++) begin
	 $display("unpacked_a[%0d]=0x:%0x = bin:%0b",jj, unpacked_a[jj], unpacked_a[jj]);
      end
   endfunction

   
endmodule // packed_array_play
