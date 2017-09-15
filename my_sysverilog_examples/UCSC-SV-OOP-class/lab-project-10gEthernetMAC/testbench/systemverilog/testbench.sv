//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

//Based upon code from opencores.org by A. Tanguay

`include "timescale.v"
`include "defines.v"

//`define GXB
//`define XIL

module tb;
   logic      clk_156m25;
   logic      clk_312m50;
   logic      clk_xgmii_rx;
   logic      clk_xgmii_tx;

   logic      reset_156m25_n;
   logic      reset_xgmii_rx_n;
   logic      reset_xgmii_tx_n;

   logic      xaui_tx_l0_n;
   logic      xaui_tx_l0_p;
   logic      xaui_tx_l1_n;
   logic      xaui_tx_l1_p;
   logic      xaui_tx_l2_n;
   logic      xaui_tx_l2_p;
   logic      xaui_tx_l3_n;
   logic      xaui_tx_l3_p;

   logic [3:0]    tx_dataout;


   pkt_tx_if tx_if(.clk(clk_156m25), .reset_n(reset_156m25_n));
   pkt_rx_if rx_if(.clk(clk_156m25), .reset_n(reset_156m25_n));

   xgmii_tx_if mii_tx_if();
   xgmii_rx_if mii_rx_if();
   wb_if       wb_if();


   // Clock generation
   initial begin
      clk_156m25 = 1'b0;
      clk_xgmii_rx = 1'b0;
      clk_xgmii_tx = 1'b0;
      forever begin
         WaitPS(3200);
         clk_156m25 = ~clk_156m25;
         clk_xgmii_rx = ~clk_xgmii_rx;
         clk_xgmii_tx = ~clk_xgmii_tx;
      end
   end

   initial begin
      clk_312m50 = 1'b0;
      forever begin
         WaitPS(1600);
         clk_312m50 = ~clk_312m50;
      end
   end


   initial begin
      // Unused for this testbench
      wb_if.wb_adr_i = 8'b0;
      wb_if.wb_clk_i = 1'b0;
      wb_if.wb_cyc_i = 1'b0;
      wb_if.wb_dat_i = 32'b0;
      wb_if.wb_rst_i = 1'b1;
      wb_if.wb_stb_i = 1'b0;
      wb_if.wb_we_i  = 1'b0;
      reset_156m25_n   = 1'b0;
      reset_xgmii_rx_n = 1'b0;
      reset_xgmii_tx_n = 1'b0;
      wb_if.wb_rst_i   = 1'b0;   //lkj
      WaitNS(20);
      reset_156m25_n   = 1'b1;
      reset_xgmii_rx_n = 1'b1;
      reset_xgmii_tx_n = 1'b1;
      wb_if.wb_rst_i   = 1'b1;   //lkj
      WaitNS(100);
`ifdef XIL
      WaitNS(200000);
`endif
   end


   testcase testcase1(.p_tx_if(tx_if), .p_rx_if(rx_if));


   xge_mac dut(
               //Resets and Clocks
               .reset_156m25_n     (reset_156m25_n),       //input
               .reset_xgmii_rx_n   (reset_xgmii_rx_n),     //input
               .reset_xgmii_tx_n   (reset_xgmii_tx_n),     //input
               .clk_156m25         (clk_156m25),           //input
               .clk_xgmii_rx       (clk_xgmii_rx),         //input
               .clk_xgmii_tx       (clk_xgmii_tx),         //input

               //Transmit
               .pkt_tx_val         (tx_if.pkt_tx_val),        //input
               .pkt_tx_sop         (tx_if.pkt_tx_sop),        //input
               .pkt_tx_mod         (tx_if.pkt_tx_mod[2:0]),   //input
               .pkt_tx_data        (tx_if.pkt_tx_data[63:0]), //input
               .pkt_tx_eop         (tx_if.pkt_tx_eop),        //input
               .pkt_tx_full        (tx_if.pkt_tx_full),       //output

               //Receive
               .pkt_rx_avail       (rx_if.pkt_rx_avail),      //output
               .pkt_rx_val         (rx_if.pkt_rx_val),        //output
               .pkt_rx_sop         (rx_if.pkt_rx_sop),        //output
               .pkt_rx_mod         (rx_if.pkt_rx_mod[2:0]),   //output
               .pkt_rx_data        (rx_if.pkt_rx_data[63:0]), //output
               .pkt_rx_eop         (rx_if.pkt_rx_eop),        //output
               .pkt_rx_err         (rx_if.pkt_rx_err),        //output
               .pkt_rx_ren         (rx_if.pkt_rx_ren),        //input

               //XAUI Interface (?)
               .xgmii_txc          (mii_tx_if.xgmii_txc),       //output
               .xgmii_txd          (mii_tx_if.xgmii_txd[63:0]), //output
               .xgmii_rxc          (mii_rx_if.xgmii_rxc),       //input
               .xgmii_rxd          (mii_rx_if.xgmii_rxd[63:0]), //input

               //Wishbone Interface
               .wb_clk_i           (clk_156m25),              //input
               //lkj .wb_clk_i      (wb_if.wb_clk_i),         //input
               .wb_rst_i           (reset_156m25_n),          //input
               //lkj .wb_rst_i           (wb_if.wb_rst_i),    //input
               .wb_adr_i           (wb_if.wb_adr_i[7:0]),     //input
               .wb_cyc_i           (wb_if.wb_cyc_i),          //input
               .wb_dat_i           (wb_if.wb_dat_i[31:0]),    //input
               .wb_stb_i           (wb_if.wb_stb_i),          //input
               .wb_we_i            (wb_if.wb_we_i),           //input
               .wb_ack_o           (wb_if.wb_ack_o),          //output
               .wb_dat_o           (wb_if.wb_dat_o[31:0]),    //output
               .wb_int_o           (wb_if.wb_int_o)           //output
               );

`ifdef GXB
   // Example of transceiver instance
   gxb gxb(// Outputs
           .rx_ctrldetect                  (mii_rx_if.xgmii_rxc_75316420),
           .rx_dataout                     (mii_rx_if.xgmii_rxd_75316420),
           .tx_dataout                     (tx_dataout[3:0]),
           // Inputs
           .pll_inclk                      (clk_156m25),
           .rx_analogreset                 (~reset_156m25_n),
           .rx_cruclk                      ({clk_156m25, clk_156m25, clk_156m25, clk_156m25}),
           .rx_datain                      (tx_dataout[3:0]),
           .rx_digitalreset                (~reset_156m25_n),
           .tx_ctrlenable                  (mii_tx_if.xgmii_txc_75316420),
           .tx_datain                      (xgmii_txd_75316420),
           .tx_digitalreset                (~reset_156m25_n));
`endif

`ifdef XIL
   // Example of transceiver instance
   xaui_block xaui(// Outputs
                   .txoutclk               (),
                   .xgmii_rxd              (mii_rx_if.xgmii_rxd[63:0]),
                   .xgmii_rxc              (mii_rx_if.xgmii_rxc),
                   .xaui_tx_l0_p           (xaui_tx_l0_p),
                   .xaui_tx_l0_n           (xaui_tx_l0_n),
                   .xaui_tx_l1_p           (xaui_tx_l1_p),
                   .xaui_tx_l1_n           (xaui_tx_l1_n),
                   .xaui_tx_l2_p           (xaui_tx_l2_p),
                   .xaui_tx_l2_n           (xaui_tx_l2_n),
                   .xaui_tx_l3_p           (xaui_tx_l3_p),
                   .xaui_tx_l3_n           (xaui_tx_l3_n),
                   .txlock                 (),
                   .align_status           (),
                   .sync_status            (),
                   .mgt_tx_ready           (),
                   .drp_o                  (),
                   .drp_rdy                (),
                   .status_vector          (),
                   // Inputs
                   .dclk                   (clk_156m25),
                   .clk156                 (clk_156m25),
                   .clk312                 (clk_312m50),
                   .refclk                 (clk_156m25),
                   .reset                  (~reset_156m25_n),
                   .reset156               (~reset_156m25_n),
                   .xgmii_txd              (mii_tx_if.xgmii_txd[63:0]),
                   .xgmii_txc              (mii_tx_if.xgmii_txc),
                   .xaui_rx_l0_p           (xaui_tx_l0_p),
                   .xaui_rx_l0_n           (xaui_tx_l0_n),
                   .xaui_rx_l1_p           (xaui_tx_l1_p),
                   .xaui_rx_l1_n           (xaui_tx_l1_n),
                   .xaui_rx_l2_p           (xaui_tx_l2_p),
                   .xaui_rx_l2_n           (xaui_tx_l2_n),
                   .xaui_rx_l3_p           (xaui_tx_l3_p),
                   .xaui_rx_l3_n           (xaui_tx_l3_n),
                   .signal_detect          (4'b1111),
                   .drp_addr               (7'b0),
                   .drp_en                 (2'b0),
                   .drp_i                  (16'b0),
                   .drp_we                 (2'b0),
                   .configuration_vector   (7'b0));

   glbl glbl();
`endif



   // XGMII Loopback
   // This test is done with loopback on XGMII or using one of the tranceiver examples
`ifndef GXB
 `ifndef XIL
   assign mii_rx_if.xgmii_rxc = mii_tx_if.xgmii_txc;
   assign mii_rx_if.xgmii_rxd = mii_tx_if.xgmii_txd;
 `endif
`endif

endmodule : tb

//
//
// ERRATA:
//    pkt_tx_val is new name of pkt_tx_valid (spec is out-of-date)
//
