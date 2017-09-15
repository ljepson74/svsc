interface memory(input bit clk);

   logic  [7:0] addr;
   logic  [7:0] data_i;
   logic  [7:0] data_o;
   logic        rw;
   logic        ce;

   modport dut (input addr, data_i, rw, ce, clk, output data_o);   
   
   modport tb (output addr, data_i, rw, ce,   input data_o, clk);
endinterface // memory


     