`timescale 1ns/1ns

program testcase(input  wire        clk,
                 output logic [7:0] din,
                 input  wire  [7:0] dout,
                 output logic [7:0] addr,
                 output logic       ce,
                 output logic       we
                );
 
  // Clocking block 

  initial begin

    // Initialize program block outputs
    addr = 0;
    din  = 0;
    ce   = 0;
    we   = 0;

    // ========== Write Operation to Ram ==========
    $display("========== WRITE OPERATION TO RAM ====================");

    for (int i = 0; i < 4; i++) begin

      repeat (2) @(posedge clk); 

      addr = i;
      din  = $urandom_range(0, 255);
      ce   = 1; //ce=1 --> Chip Enable
      we   = 1; //we=1 --> WRITE Enable

      repeat (2) @(posedge clk); 
      ce = 0;

      $display("t=%5t: WRITE: addr=%2h, din=%2h, dout=%2h, we=%2h, ce=%2h", $time, addr, din,dout,we,ce);
    end


    // ========== Read Operation from Ram ==========
    $display("\n");
    $display("========== READ OPERATION FROM RAM ====================");

    for (int i = 0; i < 4; i++) begin
      
      repeat (1) @(posedge clk); 
      addr = i;
      ce   = 1;
      we   = 0; //we=0 --> READ Enable

      repeat (3) @(posedge clk); 
      ce = 0;
 
      $display("t=%5t: READ : addr=%2h, din=%2h, dout=%2h, we=%2h, ce=%2h", $time, addr, din,dout,we,ce);
    end

    repeat(10) @(clk) $finish;
  end

endprogram

