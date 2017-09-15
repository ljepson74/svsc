module test;

   bit [7:0] unpacked_a [3:0];
   bit [3:0] [7:0] packed_a;

   initial begin
      set_packed_a;
      set_unpacked_a;


      $display("WE HAVE:  %8b",packed_a[2]);  
      $display("WE HAVE:  %2b",packed_a[2][2:1]);     
      
      $display("WE HAVE:  %8b",unpacked_a[2]);  
      $display("WE HAVE:  %2b",unpacked_a[2][2:1]);   
   end


   function void set_packed_a();
	 packed_a[0]  = 8'b1111_1111;	 
	 packed_a[1]  = 8'b0000_0000;	 
	 packed_a[2]  = 8'b1111_0011;	 
	 packed_a[3]  = 8'b1100_1111;	 
   endfunction
   
   function void set_unpacked_a();
	 unpacked_a[0]  = 8'b0000_0000;	 
	 unpacked_a[1]  = 8'b1111_1111;	 
	 unpacked_a[2]  = 8'b1111_0011;	 
	 unpacked_a[3]  = 8'b1100_1111;	 
   endfunction
endmodule // test
