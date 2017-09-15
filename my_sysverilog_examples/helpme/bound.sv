//module charlie(interface.smp_mp i);
/*module charlie(internal_if.smp_mp i);
endmodule*/

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


/* doesn't work
   internal_if.smp_mp cleaner(.clk(clk),
			      .data_bus(data_bus),
			      .bus_data(bus_data)
			      );
*/
endmodule : bound


module bound2 (internal_if.smp_mp my_if);


endmodule : bound2

