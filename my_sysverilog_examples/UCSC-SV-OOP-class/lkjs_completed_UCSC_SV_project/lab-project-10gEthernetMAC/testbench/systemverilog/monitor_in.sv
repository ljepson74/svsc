//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//This is an in-progress file.  In the future the testbench should have two monitors, to
//monitor the input to the DUT and the output from the DUT.

class monitor_in;
   string  where="mon_in";
   virtual pkt_tx_if tx_vif;
   mailbox send2sb;

   extern function new(virtual pkt_tx_if handle_tx_if, input mailbox send2sb);
   extern task          reset();
   extern task          collect_packet();
   extern task          run();
endclass : monitor_in

///
///
///

function monitor_in::new(input string name="",
                      virtual pkt_tx_if handle_tx_if, input mailbox send2sb);
   where        = name;
   this.tx_vif  = handle_tx_if;
   this.send2sb = send2sb;
endfunction : new


task monitor_in::reset();
   tx_vif.cb_rt.pkt_tx_ren <= 1'b0;
endtask : reset

task monitor_in::run();
   printme(where,$psprintf("run: pre-reset"));
   reset();
   printme(where,$psprintf("run: post-reset"));
//   fork
      collect_packet();
//   join
   printme(where,$psprintf("run: the-end"));
endtask : run


// Task to read a single packet from receive interface and display
task monitor_in::collect_packet();
   packet pkt;
   logic done;

   printme(where,$psprintf("* * **Waiting for packets** * *"));
   forever begin
      if (rt_vif.pkt_tx_valid) begin
         pkt = new();
         done = 0;

         while (!done) begin
            if (tx_vif.pkt_tx_valid) begin

               if (tx_vif.pkt_tx_sop) begin
                  printme(where,$psprintf("     ** got SOP."));
                  //lkj, put assert in here to make sure sop starts when tx_val starts
               end
               printme(where,$psprintf("     ** got data=%16x.",tx_vif.pkt_tx_data));

               pkt.add8B(tx_vif.pkt_tx_data);
               //pkt.show("debug as mon reconstructs packet");

               if (tx_vif.pkt_tx_eop) begin
                  done = 1;
                  printme(where,$psprintf("     ** got EOP."));
               end
            end // if (tx_vif.pkt_tx_val)
            @tx_vif.cb_tx;
         end // while (!done)
         pkt.show("++Rcvd packet");
//       send2sb.put(pkt);  //pass pkt to scoreboard
         tx_count = tx_count + 1;
      end
      @tx_vif.cb_tx;
   end // forever begin
endtask : collect_packet




