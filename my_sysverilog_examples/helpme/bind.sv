bind dut bound bound_u(.clk(clk), .data_bus(data_bus), .bus_data(bus_data));

/* doesn't work
bind dut bound2 bound2_u(.my_if.clk(clk),
			 .my_if.data_bus(data_bus),
			 .my_if.bus_data(bus_data)
			 );
*/