//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

import tasks::*;
class generator;
   string where="gen";

   mailbox gen2drv;
   packet  pkt;

   extern function new(input mailbox gen_2_drv_mb);
   extern task run(input int cnt=1);
endclass : generator

///
///
///

function generator::new(input mailbox gen_2_drv_mb);
   this.gen2drv = gen_2_drv_mb;
   pkt          = new(.name("genpkt"));
endfunction : new

task generator::run(input int cnt=1);
   packet pkt2snd;

   for (int nn=0; nn<cnt; nn++) begin
      pkt2snd = new pkt; //shallow copy
      pkt2snd.randomize();
      //pkt.show("Packet to Send<<<<<<<");
      gen2drv.put(pkt2snd);
   end
   printme(where,"All packets sent, gen2drv.");
endtask : run
