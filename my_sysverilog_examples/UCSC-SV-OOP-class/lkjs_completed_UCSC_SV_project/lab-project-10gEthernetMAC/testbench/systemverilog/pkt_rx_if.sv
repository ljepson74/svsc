//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

interface pkt_rx_if(input clk, input reset_n);
   string where="rx_if";

   //A->B
   logic        pkt_rx_avail;
   logic        pkt_rx_val;
   logic        pkt_rx_sop;
   logic [2:0]  pkt_rx_mod;
   logic [63:0] pkt_rx_data;
   logic        pkt_rx_eop;
   logic        pkt_rx_err;

   //A<-B
   logic   pkt_rx_ren;

   clocking cb_rx @(posedge clk);
//      default output #1ns;   //for easier waveform debug
      input reset_n;
      input pkt_rx_avail,
            pkt_rx_val,
            pkt_rx_sop,
            pkt_rx_mod,
            pkt_rx_data,
            pkt_rx_eop,
            pkt_rx_err;

      output pkt_rx_ren;
   endclocking : cb_rx

   as_check_err : assert property( @(posedge clk) disable iff (!reset_n)
                                   (pkt_rx_err==1'b0)
                                   ) else begin
      printme(where,$psprintf("TestResult  FATAL ERROR: pkt_rx_err=%1b",pkt_rx_err));
      printme(where,$psprintf("TestResult:FAIL"));
      $finish;
   end

   as_check_for_ctrl_x : assert property ( @(posedge clk) disable iff (!reset_n)
                                           !($isunknown({pkt_rx_avail,pkt_rx_val,pkt_rx_err,pkt_rx_ren})) ) else begin
      printme(where,$psprintf("TestResult  FATAL ERROR: X on control input to DUT"));
      printme(where,$psprintf("TestResult:FAIL"));
      $finish;
   end

   as_check_for_data_x : assert property ( @(posedge clk) disable iff (!reset_n)
                                           !(pkt_rx_val && $isunknown({pkt_rx_sop,pkt_rx_mod,pkt_rx_eop})) ) else begin
      printme(where,$psprintf("TestResult  FATAL ERROR: X on control input to DUT"));
      printme(where,$psprintf("TestResult:FAIL"));
      $finish;
   end
endinterface : pkt_rx_if
