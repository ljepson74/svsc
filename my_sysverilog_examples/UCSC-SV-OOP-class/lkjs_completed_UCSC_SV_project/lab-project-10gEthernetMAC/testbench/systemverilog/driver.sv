//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//driver is a container class that holds a packet.
//driver currently generates stimulus as well as transmits it.  driver
//should be split into a generator and a driver, as a future improvement.

import tasks::*;
class driver;
   string  where="drv";
   virtual pkt_tx_if tx_vif;
   mailbox send2sb;
   mailbox gen2drv;
   packet  pkt;

   extern function new(virtual pkt_tx_if handle_tx_if, input mailbox send2sb, input mailbox gen_2_drv_mb);

   extern task reset();
   extern task run();

   extern task send_pkts();
   extern task send_packet(input packet pkt);
endclass : driver

///
///
///

function driver::new(virtual pkt_tx_if handle_tx_if, input mailbox send2sb, input mailbox gen_2_drv_mb);
   tx_vif       = handle_tx_if;
   this.send2sb = send2sb;
   this.gen2drv = gen_2_drv_mb;
   pkt          = new(.name("drvpkt")); //lkj needed?
endfunction : new

task driver::reset();
   tx_vif.cb_tx.pkt_tx_data <= 64'b0;
   tx_vif.cb_tx.pkt_tx_val  <= 1'b0;
   tx_vif.cb_tx.pkt_tx_sop  <= 1'b0;
   tx_vif.cb_tx.pkt_tx_eop  <= 1'b0;
   tx_vif.cb_tx.pkt_tx_mod  <= 3'b0;
   repeat ($urandom_range(20,80)) begin @tx_vif.cb_tx; end  //offset stimulus
endtask : reset

task driver::run();
   reset();
   send_pkts();
endtask : run


task driver::send_pkts();   
   packet in_pkt;

   forever begin
      gen2drv.get(in_pkt);
      send_packet(in_pkt);
   end
endtask : send_pkts


//Each invocation & completion of this task sends a single packet to the dut.
task driver::send_packet(input packet pkt);
   int pktsize;

   pktsize = pkt.tx_data.size();

   while(tx_vif.cb_tx.pkt_tx_full==1'b1) begin //Do not start new packet until !full
      @tx_vif.cb_tx;
   end

   printme(where,$psprintf(" Start new packet w/ ipg=%0d",pkt.ipg)); //maybe ipg should include full cycles
   repeat(pkt.ipg) begin @tx_vif.cb_tx; end

   tx_vif.cb_tx.pkt_tx_val <= 1'b1;

   for (int i=0; i<pktsize; i=i+8) begin
      tx_vif.cb_tx.pkt_tx_sop <= 1'b0;
      tx_vif.cb_tx.pkt_tx_eop <= 1'b0;
      tx_vif.cb_tx.pkt_tx_mod <= 2'b0;

      if (i == 0) tx_vif.cb_tx.pkt_tx_sop <= pkt.sop;

      if (i + 8 >= pktsize) begin
	 tx_vif.cb_tx.pkt_tx_eop <= pkt.eop;
	 tx_vif.cb_tx.pkt_tx_mod <= pkt.tx_mod;
      end

      tx_vif.cb_tx.pkt_tx_data[`LANE7] <= pkt.tx_data[i+0];
      tx_vif.cb_tx.pkt_tx_data[`LANE6] <= pkt.tx_data[i+1];
      tx_vif.cb_tx.pkt_tx_data[`LANE5] <= pkt.tx_data[i+2];
      tx_vif.cb_tx.pkt_tx_data[`LANE4] <= pkt.tx_data[i+3];
      tx_vif.cb_tx.pkt_tx_data[`LANE3] <= pkt.tx_data[i+4];
      tx_vif.cb_tx.pkt_tx_data[`LANE2] <= pkt.tx_data[i+5];
      tx_vif.cb_tx.pkt_tx_data[`LANE1] <= pkt.tx_data[i+6];
      tx_vif.cb_tx.pkt_tx_data[`LANE0] <= pkt.tx_data[i+7];

      @tx_vif.cb_tx;
   end // for (int i=0; i<=(pktsize); i=i+8)

   tx_vif.cb_tx.pkt_tx_val <= 1'b0;
   tx_vif.cb_tx.pkt_tx_eop <= 1'b0;
   tx_vif.cb_tx.pkt_tx_mod <= 3'b0;


   packet::inc_total_driven();  //increment # of pkts sent
   send2sb.put(pkt);            //pass pkt to scoreboard
endtask : send_packet
