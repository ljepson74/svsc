`timescale 1ns/1ns

module testbench();

   bit          clk;
   wire   [7:0] din;
   logic  [7:0] dout;
   wire   [7:0] addr;
   wire         ce;
   wire         we;

   // Free running clock
   always #5 clk = !clk;

   // Instantiate design under test
   ram iram(.clk   	(clk),
            .din   	(din),
            .dout  	(dout),
            .addr  	(addr),
            .ce    	(ce),
            .we    	(we)
           );

   // Connect the testcase
   testcase itestcase(.clk	(clk),
                      .din   	(din),
                      .dout  	(dout),
                      .addr  	(addr),
                      .ce    	(ce),
                      .we    	(we)
                     );

endmodule
