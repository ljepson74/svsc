//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

class env;
   string where="env";

   //env components
   generator   mygenerator;
   driver      mydriver;
   monitor     mymonitor_out;
   scoreboard  myscoreboard;
   //monitor_in  mymonitor_in;  lkj todo, instead of driver2scoreboard, send from input monitor

   //env channels for comm between components
   mailbox gen_2_drv_mb;
   mailbox out_mon_mb;
   mailbox in_mon_mb;

   extern function new(virtual pkt_tx_if handle_tx_if,
                       virtual pkt_rx_if handle_rx_if);
   extern task reset();
   extern task run(input int cnt=1);
   extern function end_of_sim();
endclass : env

///
///
///

function env::new(virtual pkt_tx_if handle_tx_if,
                  virtual pkt_rx_if handle_rx_if);

   gen_2_drv_mb = new();
   out_mon_mb   = new();
   in_mon_mb    = new();

   mygenerator   = new(.gen_2_drv_mb(gen_2_drv_mb));
   mydriver      = new(.handle_tx_if(handle_tx_if), .send2sb(in_mon_mb), .gen_2_drv_mb(gen_2_drv_mb));
   mymonitor_out = new(.handle_rx_if(handle_rx_if), .send2sb(out_mon_mb));
   myscoreboard  = new(.in_mon2sb(in_mon_mb), .out_mon2sb(out_mon_mb)   );
// mymonitor_in  = new(.handle_rx_if(handle_tx_if), .send2sb(in_mon_mb)); //lkjtodo
endfunction : new

task env::reset();
   set_err_cnt(.value(0));
endtask : reset

task env::run(input int cnt=1);
   fork
      mygenerator.run(.cnt(cnt));      
      mydriver.run();
   join_none

   fork
      mymonitor_out.run();
      //mymonitor_in.run();
      myscoreboard.run();
      begin : timeout
         WaitNS(9876543);
         repeat(1) printme(where,"Test timed out as end mechanism.");
      end // block: timeout
   join_any

   end_of_sim();
   repeat(1) printme(where," *************** Test Over.***************");
endtask : run


function env::end_of_sim();
   myscoreboard.end_of_sim();
endfunction : end_of_sim
