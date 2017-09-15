interface a_if(input logic clk);

   logic a_signal;

   clocking master_cb@(posedge clk);
      output a_signal;
   endclocking : master_cb
   
   //   modport master_mp(input clk, output a_signal);   
   modport master_mp(clocking master_cb);   
      
endinterface // a_if

