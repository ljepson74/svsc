module mem_tb();

   logic clk  =0;
   always #1 clk=!clk;

   memory mem_if0(clk);

   ram ram_top(.mif(mem_if0));

   test test_u(.tbf0(mem_if0));
   
   
endmodule // mem_tb
