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
logic              reset_asserted;

initial begin
  clk = 1'b0;
  forever #5 clk = ~clk;
end

initial begin
  $monitor("t=%3t: result = %2d, detect = %b, enable = %b, reset = %b", $time, result, detect, enable, reset);

  reset           = 1;
  enable          = 0;
  preload         = 0;
  mode            = 0;
  detect_asserted = 0;
  disable_value   = $urandom_range(0,{SIZE{1'b1}});

  @(posedge clk) reset = 0;
  
  fork
    increment_count;
    disable_count(disable_value);
  join

  
  $finish;
end

final begin
  if(reset_asserted) 
    $display("t=%3t: PASS - reset asserted correctly", $time);
  else
    $display("t=%3t: FAIL - reset NOT asserted", $time);
end


task automatic disable_count(logic [SIZE-1:0] disable_value);
  wait (disable_value == result); 
  @(posedge clk) reset = 1;
  @(posedge clk) begin
    if(result == {SIZE{1'b0}})
      reset_asserted = 1'b1;
    else
      reset_asserted = 1'b0;
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
