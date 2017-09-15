`timescale 1ns/1ps
//Sri's synthesizable rtl
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
endmodule // my_module

`ifdef OLDSCHOOL
//program my_top;
module my_top;
   reg clk, en;
   reg [3:0] data;   
   wire [3:0] data_out;   

   initial begin
	$recordfile("my.trn");
	$recordvars("depth=0", my_top);
   end
   
   always begin
      #5 clk = 0;
      #5 clk = 1;	
   end

   my_dut my_dut
     (.clk(clk), 
      .en(en),
      .data(data),
      .data_out(data_out)
      );

   initial
     begin
	$monitor("lkj: %h",data_out);
	en    =0;
	data  =4'hF;
	#20;
	en  = 1;
	#10;
	data  = 4'hA;
	#10;
	data  = 4'hB;
	#10;
	data  = 4'hC;
	#10;
	data  = 4'hD;
	#40;
	$finish;       
     end
endmodule
//endprogram // my_program
`endif


`ifdef NEWSCHOOL

//define interfaces outside of modules and program blocks
interface dut_if(input bit clk, rst_n);
   logic en;
   logic [3:0] data, data_out;
   
   default clocking cb @(posedge clk);
      default input #1step output #3;      
      input    data_out;
      output   en, data;      
   endclocking // cb   

   modport dut_port(
		    clocking cb,
		    input rst_n
		    );   
   endinterface // dut_if

//holds the code that 'does' the test
module my_top;
   reg clk, en;
   reg [3:0] data;   
   wire [3:0] data_out;   

   initial begin
	$recordfile("my.trn");
	$recordvars("depth=0", my_top);
   end
  
   always begin
      #5 clk = 0;
      #5 clk = 1;	
   end

   dut_if myif(clk);
  
   
   my_dut my_dut
     (.clk         (myif.clk), 
      .en          (myif.en),
      .data        (myif.data),
      .data_out    (myif.data_out)
      );


program testtest;   
   default clocking cb @(posedge clk);
      default input #1step output #3;      
      input    data_out;
      output   en, data;      
   endclocking // cb   
   
   initial
     begin
	$monitor("lkj: %h",myif.data_out);
	en    =0;
	data  =4'hF;
	repeat (44) @myif.cb;
	myif.en  <= 1;
	myif.data  <= 4'hA;
	#10;
	myif.data  <= 4'hB;
	#10;
	@(posedge myif.clk) myif.data  <= 4'hC;
	#10;
	myif.data  <= 4'hD;
	#40;
	$finish;
     end // initial begin
endprogram // testtest
   
endmodule // my_top


`endif //  `ifdef NEWSCHOOL
   




