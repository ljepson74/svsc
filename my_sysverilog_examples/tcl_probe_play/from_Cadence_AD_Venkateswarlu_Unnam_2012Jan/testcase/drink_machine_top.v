module drink_machine_top(
      clk, reset, sd1_rd_en_io,nickel_out);

input   clk,  reset;
output  [3:0] nickel_out;
        
inout [3:0]sd1_rd_en_io ; 

assign sd1_rd_en_io = nickel_out ;

endmodule

