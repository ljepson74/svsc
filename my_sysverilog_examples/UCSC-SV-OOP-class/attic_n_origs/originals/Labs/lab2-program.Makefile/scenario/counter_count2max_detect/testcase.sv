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

initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

initial begin
  $monitor("t=%3t: result = %2d, detect = %b", $time, result, detect);

  reset           = 1;
  enable          = 0;
  preload         = 0;
  mode            = 0;
  detect_asserted = 0;

  @(posedge clk) reset = 0;
  
  fork
    increment_count;
    check_detect;
  join

  disable fork;
  
  $finish;
end

final begin
  if(detect_asserted) 
    $display("t=%3t: PASS - detect asserted during simulation", $time);
  else
    $display("t=%3t: FAIL - detect NOT asserted during simulation", $time);
end

task automatic check_detect;
  @(detect) begin
    if(result == {SIZE{1'b1}}) begin
      detect_asserted = 1'b1;
      $display("t=%3t: Assert detect_asserted...", $time);
    end
  end
endtask

task automatic increment_count;
    @(posedge clk);

    enable = 1;
    repeat({SIZE{1'b1}}) @(posedge clk);

    enable = 0;
    repeat({SIZE{1'b1}}) @(posedge clk);
endtask

endprogram
