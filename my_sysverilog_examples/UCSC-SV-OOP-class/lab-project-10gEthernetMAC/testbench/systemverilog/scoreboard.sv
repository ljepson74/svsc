//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

class scoreboard;
   string where="sb";

   mailbox rcv_from_in_mon;
   mailbox rcv_from_out_mon;

   coverage cov;// = new();

   int good_pkt_stats[int];

   extern function new(input mailbox in_mon2sb, input mailbox out_mon2sb);
   //add a reset here and to all components to clear stuff out, lkj

   extern function void reset();
   extern task run();
   extern function void end_of_sim();
   extern task compare(); //lkj make func
   extern function void update_good_pkt_stats(input int new_good_size);
   extern function void show_good_pkt_stats();
endclass : scoreboard

///
///
///

function scoreboard::new(input mailbox in_mon2sb, input mailbox out_mon2sb);
   rcv_from_in_mon  = in_mon2sb;  //note: pkt really comes from driver, for now
   rcv_from_out_mon = out_mon2sb;
   cov              = new();
endfunction : new


function void scoreboard::reset();
endfunction : reset


task scoreboard::run();
   forever begin
      compare();
   end
endtask : run

task scoreboard::compare();
   packet in_pkt;
   packet out_pkt;

   //printme(where,"Await in and out pkts to compare.");

   rcv_from_in_mon.get(in_pkt);
   //printme(where," Got in pkt.");
   in_pkt.show($psprintf(where,":INPUT-PKT:"));
   cov.collect_coverage(in_pkt); //gather coverage

   rcv_from_out_mon.get(out_pkt);
   //printme(where," Got out pkt.");
   out_pkt.show($psprintf(where,":OUTPUT-PKT:"));

   //printme(where,"Compare in and out pkts - start");
   out_pkt.compare(in_pkt);
   //printme(where,"Compare in and out pkts - end");

   update_good_pkt_stats(in_pkt.tx_data.size());
endtask : compare


function void scoreboard::update_good_pkt_stats(input int new_good_size);
   //if a packet of that size already was received, update its cnt
   //if not, add it, with a cnt of 1

   if (good_pkt_stats.exists(new_good_size)) begin
      good_pkt_stats[new_good_size]++;
   end else begin
      good_pkt_stats[new_good_size]=1;
   end
endfunction : update_good_pkt_stats

function void scoreboard::show_good_pkt_stats();
   string stats = "";
   string sub   = "";
   int cnt      = 0;

   foreach (good_pkt_stats[rur]) begin
      sub = $psprintf("[%0d]:%0d",rur,good_pkt_stats[rur]);
      //normalize size
      while (sub.len()<11) begin
         sub={sub," "};
      end

      stats = {stats,sub};
      cnt++;
      if (cnt%10==0) begin
         stats = {stats,"\n"};
      end
   end
   printme(where,"-----------Packet-size-stats--[Size]:#packets---");
   printme(where,$psprintf("\n%0s",stats));
   printme(where,"------------------------------------------------");
endfunction : show_good_pkt_stats



function void scoreboard::end_of_sim();
   int err_cnt;

   printme(where,"...............................");
   printme(where,"...............................");

   if (good_pkt_stats.size()>0) begin
   end else begin
      printme(where,$psprintf("ERROR: stats thinks 0 packets were collected."));
      inc_err_cnt();
   end


   if (packet::get_total_driven()==packet::get_total_collected()) begin
      printme(where,
              $psprintf("All packets received:%0d. Sim done!!! ****",
                        packet::get_total_collected()));
   end else begin
      printme(where,
              $psprintf("ERROR Not all packets received. sent:%0d. received:%0d Sim done!!! ****",
                              packet::get_total_driven(), packet::get_total_collected()));
   end   //lkj, why count w/ both of these pairs?

   err_cnt=get_err_cnt();
   if (err_cnt) begin
      printme(where,$psprintf("TestResult  ERRORS: err_cnt=%0d",err_cnt));
      printme(where,$psprintf("TestResult:FAIL"));
      printme(where,$psprintf("TestResult    Errors are missing packets or packets with mismatch data (relative to input) "));
   end else begin // if (err_cnt)
      printme(where,$psprintf("TestResult  No Errors: err_cnt=%0d",err_cnt));
      printme(where,$psprintf("TestResult:PASS"));
   end

   printme(where,"...............................");
   printme(where,"...............................");
   show_good_pkt_stats();

endfunction : end_of_sim