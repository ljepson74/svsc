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

  logic error = 0;

  initial begin
    forever begin
      @(posedge clk) 
      if ( reset == 0 ) begin
        if ( result == MAX_VAL && detect != 1 ) begin
          $display("ERROR detect wrong result=%0d detect=%0b", result, detect);
          error++;
        end
        if ( result != MAX_VAL && detect == 1 ) begin
          $display("ERROR detect wrong result=%0d detect=%0b", result, detect);
          error++;
        end
      end
    end
  end

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

  final begin
    if ( error )
     $display("FAIL");
    else
     $display("PASS");
  end

endprogram
