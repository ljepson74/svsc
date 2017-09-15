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

  logic [SIZE-1:0] random_max, random_reset, prev_result;
  logic enable1, reset1;
  logic enable2 = 1;
  logic reset2 = 1;
  logic error = 0;

  assign enable = (enable1 && enable2);
  assign reset = (reset1 || reset2);

//initial begin
//  random_max = $urandom_range(1,MAX_VAL);
//  $display("random_max = %02d MAX_VAL = %02d", random_max, MAX_VAL);
//  forever begin
//    @(posedge clk) begin
//      if ( !reset && !enable2 && prev_result != result ) begin
//        $display("ERROR count still changing while disabled");
//        error = 1;
//      end
//      prev_result = result;
//      if ( result == random_max )
//        enable2 = 0;
//    end
//  end
//end

  initial begin
    random_reset = $urandom_range(1,MAX_VAL);
    $display("random_reset = %02d MAX_VAL = %02d", random_reset, MAX_VAL);
    forever begin
      @(posedge clk) begin
        if ( reset2 ) begin
          if ( result != 0 ) begin
            $display("ERROR count did not reset=%b reset1=%b reset2=%b", reset,reset1,reset2);
            error = 1;
          end
          reset2 = 0;
        end
        if ( result == random_reset )
          reset2 = 1;
      end
    end
  end

  initial begin 
    $monitor("t=%3t: result = %02d, detect = %b reset=%b re1=%b re2=%b", $time, result, detect, reset, reset1, reset2);
    reset1  = 1;
    enable1 = 0;
    preload = 0;
    mode = 0;
    @(posedge clk) reset1 = 0;
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
