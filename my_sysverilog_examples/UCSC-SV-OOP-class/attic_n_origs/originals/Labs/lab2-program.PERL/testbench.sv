module testbench();
  parameter SIZE = 4;

  logic            clk = 0;
  logic            reset;
  logic            enable;
  logic            preload;
  logic [SIZE-1:0] preload_data;
  logic            mode;
  logic            detect;
  logic [SIZE-1:0] result;

  always #5 clk = ~clk;

  counter counter_u(clk,reset,enable,preload,preload_data,mode,detect,result);
  testcase testcase_u(clk,reset,enable,preload,preload_data,mode,detect,result);

endmodule
