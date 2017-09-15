interface memory(input bit clk);

   logic  [7:0] some_data;

   modport dut (input some_data);

   modport tb (output some_data);

endinterface // memory


     