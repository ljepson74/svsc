//from www.asic-world/systemverilog/clocking1.html

`timescale 1ns/1ns

//prog dec w/ ports
program clocking_skew_prg
  (
   input  wire  clk,
   output logic [7:0] din,
   input  wire  [7:0] dout,
   output logic [7:0] addr,
   output logic ce,
   output logic we
   );


//clocking block
   clocking ram @(posedge clk);
      input 	#1 dout;
      output 	#1 din,addr,ce,we;
      endclocking
   
   initial begin
      //init the outputs
      ram.addr <= 0;
      ram.din  <= 0;
      ram.ce   <= 0;
      ram.we   <= 0;
      //write ops to ram
      for (int i = 0; i<2; i++) begin
	 @ (posedge clk);
	 ram.addr <= i;
	 ram.din  <= $random;
	 ram.ce   <= 1;
	 ram.we   <= 1;
	 @ (posedge clk);
	 ram.ce <= 0;
      end // for (int i = 0; i<2; i++)
      //read ops to ram
      for (int i = 0; i<2; i++) begin
	 @ (posedge clk);
	 ram.addr <= i;
	 ram.ce   <= 1;
	 ram.we   <= 0;
	 //below this line is same as @ (posedge clk);
	 @ (ram);
	 ram.ce <= 0;	 
      end // for (int i = 0; i<2; i++)
      #40 $finish;      
   end
endprogram // clocking_skew_prg
      

//simple top level file
module clocking_skew();

   logic clk  =0;
   wire [7:0] din;
   logic [7:0] dout;
   wire [7:0]  addr;
   wire        ce;
   wire        we;
   reg [7:0]   memory [0:255];

   //clock generator
   always #10 clk++;
   
   //simple ram model
   always @ (posedge clk)
     if (ce)
       if (we)
	 memory[addr] <= din;
       else
	 dout 	      <= memory[addr];

   
   initial begin
	$recordfile("my.trn");
	$recordvars("depth=0", clocking_skew);
   end // initial begin
   
   //monitor all the signals
   initial begin
      $monitor("@%0dns addr:%0x din %0x dout %0x we %0x ce %0x",
	       $time, addr, din, dout, we, ce);
   end


   //connect the program
   clocking_skew_prg U_program
     (
      .clk   (clk),
      .din   (din),
      .dout  (dout),
      .addr  (addr),
      .ce    (ce),
      .we    (we)
      );
   
   
endmodule // clocking_skew

