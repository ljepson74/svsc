module dut(my_if mif);
   initial begin
      $monitor($time," mif.some_data=%2x", 
	       mif.some_data);      
   end  
endmodule
