
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
logic  [SIZE-1:0]  preload_value;
logic              reset_asserted;
logic              preload_asserted;

`include "scenario/counter_preload/tasks.sv"


initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

initial begin
  $monitor("t=%3t: result = %2d, detect = %b, enable = %b, reset = %b, preload = %b", $time, result, detect, enable, reset, preload);

  init;

  @(posedge clk) reset = 0;
  
  fork
    increment_count;
    preload_count(preload_value, preload_data);
  join

  
  $finish;
end

final begin
  if(preload_asserted) 
    $display("t=%3t: PASS - preload asserted correctly -> preload_data = %2d", $time, preload_data);
  else
    $display("t=%3t: FAIL - preload NOT asserted ", $time);
end

task automatic preload_count(logic [SIZE-1:0] preload_value, preload_data);
  wait (preload_value == result); 
  @(posedge clk) preload  = 1;
  @(posedge clk) preload  = 0;
  if(result == preload_data)
    preload_asserted = 1;
  else
    preload_asserted = 0;
endtask


task automatic increment_count;
    @(posedge clk);

    enable = 1;
    repeat({SIZE{1'b1}}) @(posedge clk);

    enable = 0;
    repeat({SIZE{1'b1}}) @(posedge clk);
endtask

endprogram
