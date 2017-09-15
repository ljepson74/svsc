module svs_top ();
   import uvm_pkg::*;

   logic clk, resetn;
   logic [31:0] outbus;

   svs_if svs_if_u[3:0](.clk(clk), .resetn(resetn));
   
   svs_test svs_test_u = new();
   //svs_test_u = new;

   initial begin
      clk    <= 1'b0;
      resetn <= 1'b1;
      #40;
//      $finish;
   end
   always begin
      #5;
      clk <= ~clk;
   end
   svs_dut svs_dut(
		   .clk(clk),
		   .resetn(resetn),
		   .inbus3(svs_if_u[3].bus32),
		   .inbus2(svs_if_u[2].bus32),
		   .inbus1(svs_if_u[1].bus32),
		   .inbus0(svs_if_u[0].bus32),
		   .outbus(outbus)
		   );

   initial begin
      run_test("");//svs_test");      
   end
endmodule // svs_top
