//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Testcase to check undersized packet behavior of DUT

import tasks::*;
program testcase(interface  p_tx_if, interface  p_rx_if);

class packet_undersized extends packet;
   constraint c_tx_data_size {
      tx_data.size() dist {[5:7]  :/ 45,
                           [8:59] :/ 45};
   }
endclass : packet_undersized


   string where      = "testcase";
   int    num_packet;
   env    myenv;
   packet_undersized pkt_special;

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
