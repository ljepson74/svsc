//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

interface xgmii_rx_if;
   //A->B
   logic [7:0]  xgmii_rxc;
   logic [63:0] xgmii_rxd;

   //A<-B

   //helper signals
   logic [7:0] xgmii_rxc_75316420;
   logic [7:0] xgmii_rxd_75316420;


   assign xgmii_rxc_75316420 = {xgmii_rxc[7],
                                xgmii_rxc[5],
                                xgmii_rxc[3],
                                xgmii_rxc[1],
                                xgmii_rxc[6],
                                xgmii_rxc[4],
                                xgmii_rxc[2],
                                xgmii_rxc[0]};

   assign xgmii_rxd_75316420 = {xgmii_rxd[63:56],
                                xgmii_rxd[47:40],
                                xgmii_rxd[31:24],
                                xgmii_rxd[15:8],
                                xgmii_rxd[55:48],
                                xgmii_rxd[39:32],
                                xgmii_rxd[23:16],
                                xgmii_rxd[7:0]};

endinterface : xgmii_rx_if

