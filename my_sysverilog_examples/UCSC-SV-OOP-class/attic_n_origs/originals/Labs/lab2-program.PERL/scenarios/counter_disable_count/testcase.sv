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

  logic [SIZE-1:0] random_max, prev_result;
  logic enable1;
  logic enable2 = 1;
  logic error = 0;

  assign enable = (enable1 && enable2);

  initial begin
    random_max = $urandom_range(1,MAX_VAL);
    $display("random_max = %02d MAX_VAL = %02d", random_max, MAX_VAL);
    forever begin
      @(posedge clk) begin
        if ( !reset && !enable2 && prev_result != result ) begin
          $display("ERROR count still changing while disabled");
          error = 1;
        end
        prev_result = result;
        if ( result == random_max )
          enable2 = 0;
      end
    end
  end

  initial begin 
    $monitor("t=%3t: result = %02d, detect = %b  enable=%b en1=%b en2=%b", $time, result, detect, enable, enable1, enable2);
    reset  = 1;
    enable1 = 0;
    preload = 0;
    mode = 0;
    @(posedge clk) reset = 0;
    @(posedge clk);
    enable1 = 1;
    repeat (16) @(posedge clk);
    enable1 = 0;
    repeat (10) @(posedge clk) $finish;
  end

  final begin
    if ( error )
     $display("FAIL");
    else
     $display("PASS");
  end
  

endprogram
