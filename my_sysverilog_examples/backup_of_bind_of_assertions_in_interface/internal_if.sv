interface internal_if(input clk);

   logic [31:0] data_bus;
   logic [31:0] bus_data;
 
   modport smp_mp (input clk, data_bus, bus_data);

   //add assertions here
   bind_x_check: assert property(@(negedge clk) !(data_bus[6:5]===2'b11)) else begin
      $display("UNK-CHK"," ERROR: unexpected value found");
      $finish;
   end

				 
/*   assert (bus_data[4]===1'b0) else begin
      $display(" ERROR.  bus_data[4]=%1b (not case-equal to 1'b0)",bus_data[4]);
   end
 */  
endinterface : internal_if
