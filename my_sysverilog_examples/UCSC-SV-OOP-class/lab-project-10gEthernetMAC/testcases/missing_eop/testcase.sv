//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Testcase to check missing eop behavior of DUT

import tasks::*;
program testcase(interface  p_tx_if, interface  p_rx_if);

class packet_missing_eop extends packet;
   constraint c_legal_eop { eop==1'b0;}
endclass : packet_missing_eop


   string where      = "testcase";
   int    num_packet;
   env    myenv;
   packet_missing_eop pkt_special;

   initial begin
      $vcdpluson();
      //$vcdplusdeltacycleon();

      myenv = new(.handle_tx_if(p_tx_if), .handle_rx_if(p_rx_if));

      //connect packet handle from generator.sv to this testcase packet
      pkt_special           = new();
      myenv.mygenerator.pkt = pkt_special;

      num_packet = $urandom_range(1,1);
      myenv.run(.cnt(num_packet));
   end // initial begin

endprogram : testcase
