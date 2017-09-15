//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Testcase to check Zero-Interpacket-Gap behavior of DUT

import tasks::*;
program testcase(interface  p_tx_if, interface  p_rx_if);

class packet_0ipg extends packet;
   constraint c_ipg { ipg dist {0      :/ 70,
                                [1:30] :/ 0};
   }
endclass : packet_0ipg

   string      where      = "testcase";
   int         num_packet;
   env         myenv;
   packet_0ipg pkt_special;

   initial begin
      $vcdpluson();
      //$vcdplusdeltacycleon();

      myenv = new(.handle_tx_if(p_tx_if), .handle_rx_if(p_rx_if));

      //connect packet handle from generator.sv to this testcase packet
      pkt_special           = new();
      myenv.mygenerator.pkt = pkt_special;

      num_packet = $urandom_range(203,203);
      myenv.run(.cnt(num_packet));
   end // initial begin

endprogram : testcase
