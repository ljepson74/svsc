interface in_if (input clk);
   logic [31:0] data_bus;

   //clocking blocks
   clocking drv_cb @(posedge clk);
      output data_bus;      
   endclocking

   clocking smp_cb @(posedge clk);
      input data_bus;      
   endclocking

   //modports
   modport drv_mp (clocking drv_cb);
   modport smp_mp (clocking smp_cb);
endinterface : in_if

