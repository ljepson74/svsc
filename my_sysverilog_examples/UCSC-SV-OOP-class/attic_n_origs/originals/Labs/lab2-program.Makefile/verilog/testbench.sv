module testbench();

parameter SIZE = 4;

wire              clk;
wire              reset;
wire              enable;
wire              preload;
wire  [SIZE-1:0]  preload_data;
wire              mode;
wire             detect;
wire [SIZE-1:0]  result;

testcase t1( 
            .clk            (clk),
            .reset          (reset),
            .enable         (enable),
            .preload        (preload),
            .preload_data   (preload_data),
            .mode           (mode),
            .detect         (detect),
            .result         (result)
          );

counter c1( 
            .clk            (clk),
            .reset          (reset),
            .enable         (enable),
            .preload        (preload),
            .preload_data   (preload_data),
            .mode           (mode),
            .detect         (detect),
            .result         (result)
          );

endmodule
