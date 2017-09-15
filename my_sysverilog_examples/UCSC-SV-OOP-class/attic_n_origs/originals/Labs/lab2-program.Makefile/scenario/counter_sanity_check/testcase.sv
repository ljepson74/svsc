program testcase(clk,reset,enable,preload,preload_data,mode,detect,result);

parameter SIZE = 4;

output              clk;
output              reset;
output              enable;
output              preload;
output  [SIZE-1:0]  preload_data;
output              mode;
input               detect;
input   [SIZE-1:0]  result;

logic              clk;
logic              reset;
logic              enable;
logic              preload;
logic  [SIZE-1:0]  preload_data;
logic              mode;
logic              detect;
logic  [SIZE-1:0]  result;

initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

initial begin
  $monitor("t=%3t: result = %2d, detect = %b", $time, result, detect);

  reset   = 1;
  enable  = 0;
  preload = 0;
  mode    = 0;

  @(posedge clk) reset = 0;
  
  @(posedge clk);
  enable = 1;

  repeat(10) @(posedge clk);
  enable = 0;

  repeat(10) @(posedge clk);
  $finish;
end

endprogram
