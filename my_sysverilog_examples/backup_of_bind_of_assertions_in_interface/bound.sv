module bound_baby(internal_if.smp_mp i);
endmodule : bound_baby

module bound (
	      clk,
	      data_bus,
	      bus_data
	      );

   input        clk;
   input [31:0] data_bus;
   input [31:0] bus_data;


   internal_if waste(.clk(clk));
   assign waste.data_bus = data_bus;
   assign waste.bus_data = bus_data;
      
   bound_baby bound_baby_u(.i(waste));


endmodule : bound

module bound_holder();
//   internal_if an_if();
//   bound bound_u(.clk);
endmodule


