//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

interface pkt_tx_if( input clk, input reset_n);
   string where="tx_if";

   //A->B
   logic        pkt_tx_val; //pkt_tx_valid;
   logic        pkt_tx_sop;
   logic [2:0]  pkt_tx_mod;
   logic [63:0] pkt_tx_data;
   logic        pkt_tx_eop;

   //A<-B
   logic        pkt_tx_full;


   clocking cb_tx @(posedge clk);
      default output #1000ps;   //for easier waveform debug

      input  reset_n;
      input  pkt_tx_full;

      output pkt_tx_val,
             pkt_tx_sop,
             pkt_tx_mod,
             pkt_tx_data,
             pkt_tx_eop;
   endclocking : cb_tx
   //will not use. modport mp_tx (clocking cb_tx);

   as_check_for_ctrl_x : assert property ( @(posedge clk) disable iff (!reset_n)
                                           !($isunknown({pkt_tx_val,pkt_tx_full})) ) else begin
      printme(where,$psprintf("TestResult  FATAL ERROR: X on control input to DUT"));
      printme(where,$psprintf("TestResult:FAIL"));
      $finish;
   end

   as_check_for_data_x : assert property ( @(posedge clk) disable iff (!reset_n)
                                           !(pkt_tx_val && $isunknown({pkt_tx_sop,pkt_tx_mod,pkt_tx_eop})) ) else begin
      printme(where,$psprintf("TestResult  FATAL ERROR: X on data input to DUT"));
      printme(where,$psprintf("TestResult:FAIL"));
      $finish;
   end

endinterface : pkt_tx_if
