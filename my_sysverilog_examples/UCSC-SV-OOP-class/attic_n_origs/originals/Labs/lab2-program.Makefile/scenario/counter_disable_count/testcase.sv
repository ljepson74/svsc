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

logic              detect_asserted;
logic  [SIZE-1:0]  disable_value;

initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

initial begin
  $monitor("t=%3t: result = %2d, detect = %b, enable = %b", $time, result, detect, enable);

  reset           = 1;
  enable          = 0;
  preload         = 0;
  mode            = 0;
  detect_asserted = 0;
  disable_value   = $urandom_range(0,{SIZE{1'b1}});

  @(posedge clk) reset = 0;
  
  fork
    increment_count;
  join_none

  wait (disable_value == result); 
  @(posedge clk) enable = 0;
  disable fork;

  
  $finish;
end

final begin
  if(disable_value == result) 
    $display("t=%3t: PASS - test disabled correctly -> disable_value = %2d, result = %2d", $time, disable_value, result);
  else
    $display("t=%3t: FAIL - test NOT disabled correctly -> disable_value = %2d, result = %2d", $time, disable_value, result);
end

task automatic increment_count;
    @(posedge clk);

    enable = 1;
    repeat({SIZE{1'b1}}) @(posedge clk);

    enable = 0;
    repeat({SIZE{1'b1}}) @(posedge clk);
endtask

endprogram
