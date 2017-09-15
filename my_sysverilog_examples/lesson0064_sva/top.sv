module top;
   int  nagesh;
   int  mod3,mod5; 
   initial begin 
      $monitor("nagesh=%0d mod3/5=%0d/%0d",nagesh,mod3,mod5);
      repeat(10) begin
	 #1 nagesh=$urandom_range(4,100);
      end
      $finish;
   end
   assign mod3=(nagesh%3);
   assign mod5=(nagesh%5);
      
   property div3;
      @(nagesh) (mod3==0);
   endproperty
   property div5;
      @(nagesh) (mod5==0);
   endproperty

   sequence d53;
      @(mod5)
	1;
   endsequence
 
   assert property (div5) begin
      $display("buzz");
   end
   assert property (div3) begin
      $display("fizz");
   end
   assert property (d53) begin
      $display("BF");
   end
  
endmodule