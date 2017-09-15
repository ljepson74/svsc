module top;
   logic        clk;
   logic        valid;
   logic        enable;
   logic [3:0]  abus;

   initial begin
      clk=0;      
      #5;
      forever begin
	 #5 clk=!clk;
      end
   end // initial begin

   initial begin
      $monitor("%t valid=%1b enable=%1b abus=%1h",$time, valid, enable, abus);
   end // initial begin
   
   initial begin
      #5;
      valid =1'b1;
      enable=1'b0;
      repeat (55) begin
	 @(posedge clk);
	 valid =$urandom();
	 enable=$urandom();
	 abus  =$urandom(); 
	 nandkumar : assert (abus==4'hX);
	 //if (abus[3:0] == 4'h6) $display("%t assertion active",$time);
      end // repeat (55)
      $finish;
   end

   property pos;
     // @(posedge clk) abus[3:0]==4'h6;
    @( abus) abus[3:0]!=4'h6;
   endproperty
   assert property (pos);

   property neg;
     // @(posedge clk) abus[3:0]==4'h6;
    @( abus) abus[3:0]==4'hX;
   endproperty
   assert property (neg);

   property fail;
     // @(posedge clk) abus[3:0]==4'h6;
    @( abus) (abus[3:0]!=4'h6) |=> (abus[3:0]!=4'h6);
   endproperty
   assert property (fail);   
endmodule : top

//raw assert versus assert in a property
//raw assert will show each time it fails?       //immediate assertion
//property assert will show each time pass->fail //conconcurrent assertion