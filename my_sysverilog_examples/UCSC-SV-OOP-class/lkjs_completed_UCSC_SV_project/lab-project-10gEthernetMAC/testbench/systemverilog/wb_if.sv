//UCSC Extension:Advanced Verification with SystemVerilog OOP Testbench Course Project.
//Linc Jepson,2014.  Instructor B. Ting.

interface wb_if;
   //A->B
   logic [7:0]  wb_adr_i;
   logic        wb_clk_i;
   logic        wb_cyc_i;
   logic [31:0] wb_dat_i;
   logic        wb_rst_i;
   logic        wb_stb_i;
   logic        wb_we_i ;

   //A<-B
   logic        wb_ack_o;
   logic [31:0] wb_dat_o;
   logic        wb_int_o;
endinterface : wb_if
