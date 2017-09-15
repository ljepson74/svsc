
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

  parameter MAX_VAL = (1 << SIZE) - 1;

  logic [SIZE-1:0] random_max, preload_point, preload_data;
  logic error = 0;

  `include "../../tasks.sv"

  initial begin
    preload_point = $urandom_range(1,MAX_VAL);
    preload_data = $urandom_range(1,MAX_VAL);
    $display("preload point = %02d MAX_VAL = %02d preload_data=%02d", preload_point, MAX_VAL, preload_data);
    forever begin
      @(posedge clk)
        if ( preload ) begin
          preload = 0;
          if ( enable && (result != preload_data) ) begin
            $display("ERROR result=%02d != to preload=%02d", result, preload_data);
            error++;
          end
        end
      @(posedge clk)
        if ( result == preload_point )
          preload = 1;
    end
  end

  initial begin 
    $monitor("t=%3t: result=%02d, detect=%b reset=%b enable=%b preload=%b",
       $time, result, detect, reset, enable, preload);
    init();
    @(posedge clk) reset = 0;
    @(posedge clk);
    enable = 1;
    repeat (16) @(posedge clk);
    enable = 0;
    repeat (10) @(posedge clk) $finish;
  end

  final begin
    if ( error )
     $display("FAIL");
    else
     $display("PASS");
  end
  

endprogram
