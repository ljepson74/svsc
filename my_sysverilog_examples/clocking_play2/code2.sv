`timescale 1ns/1ps

module my_dut(input clk, en,
	      input [3:0] data,	      
	      output reg [3:0] data_out   
	      );
   reg 	[3:0]	     data_d;

   always@(posedge clk)
     if (en) begin
	data_d   <= data;
	data_out <= data_d;
     end
endmodule : my_module

interface dut_if(input bit clk, rst_n);
   logic en;
   logic [3:0] data, data_out;

   default clocking cb @(posedge clk);
      default input #1step output #3;      
      input    data_out;
      output   en, data;
   endclocking // cb

   modport dut_port(clocking cb,input rst_n);
endinterface : dut_if

module smthg(dut_if an_if);
   initial
     begin
	$monitor("lkj: got data:%h",
		 an_if.data);
	an_if.en    =0;
	an_if.data  =4'hF;
	repeat (44) @an_if.cb;
	an_if.en    <= 1;
	an_if.data  <= 4'hA;
	#10;
	an_if.en    <= 0;
	#10;
	an_if.en    <= 1;
	an_if.data  <= 4'hB;
	#10;
	@(posedge an_if.clk) an_if.data  <= 4'hC;
	#10;
	an_if.en    <= 1;
	an_if.data  <= 4'hD;
	#40;
	$finish;
     end // initial begin


   always@(an_if.data_out) begin
      $display(" data_out=%0h",data_out);
   end

endmodule : smthg

module my_top;
   reg        clk, en;
   reg  [3:0] data;
   wire [3:0] data_out;

   initial begin
      $recordfile("my.trn");
      $recordvars("depth=0", my_top);
      clk=0;
      $display("tb: we look for B now * * * * * * * ");
      wait(myif.cb.data==4'hB);
      $display("tb: we drive B now * * * * * * * ");
   end

   always begin
      #5 clk = ~clk;
   end

   dut_if myif(.clk(clk));

   my_dut my_dut(.clk         (myif.clk),
		 .en          (myif.cb.en),
		 .data        (myif.cb.data),
		 .data_out    (myif.data_out));

   smthg smthg(.an_if(myif));

/*
   always@(myif.cb.data[1]) begin
      $display("tb: saw clk");
//    wait(myif.cb.data[1]);
//    $display("tb: saw data[1] set. data=%h",myif.cb.data);
      wait(myif.cb.data_out[1]);
      $display("tb: saw data_out[1] set. data_out=%h",myif.cb.data_out);
   end
*/
 endmodule : my_top




