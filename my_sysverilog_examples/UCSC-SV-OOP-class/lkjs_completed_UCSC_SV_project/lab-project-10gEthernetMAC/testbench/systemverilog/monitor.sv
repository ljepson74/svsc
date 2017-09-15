//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

class monitor;
   string  where="mon";
   virtual pkt_rx_if rx_vif;
   mailbox send2sb;

   extern function new(virtual pkt_rx_if handle_rx_if, input mailbox send2sb);
   extern task          reset();
   extern task          collect_packet();
   extern task          run();
   extern function void monitor_err();  //lkj rm me
endclass : monitor

///
///
///

function monitor::new(virtual pkt_rx_if handle_rx_if, input mailbox send2sb);
   this.rx_vif  = handle_rx_if;
   this.send2sb = send2sb;
endfunction : new


task monitor::reset();
   rx_vif.cb_rx.pkt_rx_ren <= 1'b0;
endtask : reset

task monitor::run();
   //printme(where,$psprintf("run: pre-reset"));
   reset();
   //printme(where,$psprintf("run: post-reset"));
//   fork
      collect_packet();
     // monitor_err();
//   join
   //printme(where,$psprintf("run: the-end"));
endtask : run


// Task to read a single packet from receive interface and display
task monitor::collect_packet();
   packet pkt;
   logic done;

   printme(where,$psprintf("* * **Waiting for packets** * *"));
   forever begin
      if (rx_vif.cb_rx.pkt_rx_avail) begin  //lkjhelp
         pkt = new(.name("rcvpkt"));
         done = 0;
         rx_vif.cb_rx.pkt_rx_ren <= 1'b1;
         @rx_vif.cb_rx;

         while (!done) begin
            if (rx_vif.cb_rx.pkt_rx_val) begin //lkjhelp
               //printme(where,$psprintf("receiving a packet got rx_val. #1"));
               if (rx_vif.cb_rx.pkt_rx_sop) begin //**1  //lkjhelp
                  //printme(where,$psprintf("     ** got SOP."));
               end
               //printme(where,$psprintf("     ** got data=%16x.",rx_vif.pkt_rx_data));

               pkt.add8B(rx_vif.cb_rx.pkt_rx_data); //lkjhelp
               //pkt.show("debug as mon reconstructs packet");

               if (rx_vif.cb_rx.pkt_rx_eop) begin  //lkjhelp
                  done = 1;
                  pkt.tx_mod = rx_vif.cb_rx.pkt_rx_mod;  //lkjhelp
                  pkt.adjust_for_mod();
                  rx_vif.cb_rx.pkt_rx_ren <= 1'b0;
                  //printme(where,$psprintf("     ** got EOP."));
               end
            end // if (rx_vif.pkt_rx_val)
            @rx_vif.cb_rx;
         end // while (!done)
         packet::inc_total_collected();
         //pkt.show("++Rcvd packet");
         send2sb.put(pkt);  //pass pkt to scoreboard
      end // if (rx_vif.pkt_rx_avail)
      @rx_vif.cb_rx;
   end // forever begin
endtask : collect_packet

function void monitor::monitor_err();
//   forever begin
//   end
endfunction : monitor_err



//**1
//Does SOP need to be high on 1st clk cycle of val?
//can we drop val during transmission of packet? lkj
//Put assert in here to make sure sop starts when rx_val starts


