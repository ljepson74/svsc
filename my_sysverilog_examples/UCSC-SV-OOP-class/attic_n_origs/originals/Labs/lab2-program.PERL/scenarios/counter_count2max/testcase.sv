program testcase(clk,reset,enable,preload,preload_data,mode,detect,result);
  parameter SIZE=4;

  input  logic            clk;
  output logic            reset;
  output logic            enable;
  output logic            preload;
  output logic [SIZE-1:0] preload_data;
  output logic            mode;
  input  logic            detect;
  input  logic [SIZE-1:0] result;

  initial begin
    $monitor("t=%3t: result = %02d, detect = %b", $time, result, detect);

    reset  = 1;
    enable = 0;
    preload = 0;
    mode = 0;
    @(posedge clk) reset = 0;
    @(posedge clk);
    enable = 1;
    repeat (16) @(posedge clk);
    enable = 0;
    repeat (10) @(posedge clk) $finish;
  end
endprogram
