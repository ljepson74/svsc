bind dut bound bound_u(.clk(clk), .data_bus(data_bus), .bus_data(bus_data));

/* doesn't work
bind dut bound2 bound2_u(.my_if.clk(clk),
			 .my_if.data_bus(data_bus),
			 .my_if.bus_data(bus_data)
			 );
*/

/*
IDEAL GOAL.  #3.  do not use bound or bound2.  just connect/bind internal_if.smp 
 to the dut.  The goal is to use the assertions in the interface on internal signals.
 At the submodule testbench level
  
bind dut internal_if.smp_mp somename(.clk(clk), .data_bus(data_bus), .bus_data(bus_data));
 */
