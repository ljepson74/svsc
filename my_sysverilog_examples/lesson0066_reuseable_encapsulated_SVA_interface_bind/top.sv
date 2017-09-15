//irun -sv top.sv


//1. Example of encapsulated checks.  SVA,protocol,functionalcoverage
module my_sva(input logic [3:0] bus);
   as_silly_check : assert property (@(bus) bus!=4'h5) begin
      $display("%m, pass. bus=%0h",bus);
   end else begin
      $display("%m, fail. bus=%0h",bus);
   end
endmodule

//2. DUT. Could be VHDL
module my_dut(
   input logic [3:0] a_bus);
endmodule

//3. Simple interface
interface my_if();
   logic [3:0] 	     bus;
endinterface

//Scenario 1. We bind checks to a module.  We already do this.
// Useful for interface checking in top-level sim.
module my_binding();
   bind my_dut my_sva name_of_bind1(.bus(a_bus));  //bound SVA to the DUT
endmodule

//Scenario 2. We 
module tb_top;
   logic [3:0] drv_bus;

   my_if  my_if();
   my_dut my_dut(my_if.bus);

   //Ugliness, since we can't bind module to interface or instantiate in interface, afaik
   my_sva my_sva(.bus(my_if.bus)); //use (.*) connection somehow;

   assign my_if.bus = drv_bus;

   initial begin
      #4;
      repeat (10) begin
	 drv_bus=$urandom;
	 $display($time,": drv_bus=%0h",drv_bus);
	 #4;
      end
      $finish;
   end
endmodule : tb_top
