//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Testcase to bring up the testbench

import tasks::*;
program testcase(interface  p_tx_if, interface  p_rx_if);
   string where      = "testcase";
   int    num_packet;
   env    myenv;

   initial begin
      $vcdpluson();
      //$vcdplusdeltacycleon();

      myenv = new(.handle_tx_if(p_tx_if), .handle_rx_if(p_rx_if));

      num_packet = $urandom_range(300,800);
      myenv.run(.cnt(num_packet));
   end // initial begin

endprogram : testcase
