module mem_tb();

   my_if my_connection();

   dut my_dut(.mif(my_connection));

   test my_test(.this_if(my_connection));   
   
endmodule // mem_tb
