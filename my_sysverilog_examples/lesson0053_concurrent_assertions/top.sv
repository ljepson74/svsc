module top;
   logic        clk;
   logic        valid;
   logic [2:0]  abus;

   initial begin
      clk=0;      
      #5;
      forever begin
	 #5 clk=!clk;
      end
   end // initial begin

   initial begin
      $monitor("%t valid=%1b  abus=%1h",$time, valid, abus);
   end // initial begin
   
   initial begin
      #5;
      valid =1'b1;
      repeat (20) begin
	 @(posedge clk);
	 valid =$urandom();
	 abus  =$urandom_range(0,7); 
	 CAMERONCAMERON : assert (abus!==3'h7);
	 //if (abus[3:0] == 3'h6) $display("%t assertion active",$time);
      end // repeat (55)
    
      $finish;
   end

   property JEPSONJEPSON;
      // @(posedge clk) abus[2:0]==3'h6;
      @( abus) abus[2:0]!==3'h7;
   endproperty
   assert property (JEPSONJEPSON);
   
   /*   property neg;
    // @(posedge clk) abus[2:0]==3'h6;
    @( abus) abus[2:0]==3'hX;
   endproperty
    assert property (neg);

    property fail;
    // @(posedge clk) abus[2:0]==3'h6;
    @( abus) (abus[2:0]!=3'h6) |=> (abus[2:0]!=3'h6);
   endproperty
    assert property (fail);   
    */
endmodule : top

//raw assert versus assert in a property
//raw assert will show each time it fails?       //immediate assertion
//property assert will show each time pass->fail //conconcurrent assertion