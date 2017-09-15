//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

interface xgmii_tx_if;
   //A->B
   logic [7:0]  xgmii_txc;
   logic [63:0] xgmii_txd;

   //A<-B


   //helper signals
   logic [7:0]  xgmii_txc_75316420;
   logic [63:0] xgmii_txd_75316420;

   assign xgmii_txc_75316420 = {xgmii_txc[7],
                                xgmii_txc[5],
                                xgmii_txc[3],
                                xgmii_txc[1],
                                xgmii_txc[6],
                                xgmii_txc[4],
                                xgmii_txc[2],
                                xgmii_txc[0]};

   assign xgmii_txd_75316420 = {xgmii_txd[63:56],
                                xgmii_txd[47:40],
                                xgmii_txd[31:24],
                                xgmii_txd[15:8],
                                xgmii_txd[55:48],
                                xgmii_txd[39:32],
                                xgmii_txd[23:16],
                                xgmii_txd[7:0]};
endinterface : xgmii_tx_if

