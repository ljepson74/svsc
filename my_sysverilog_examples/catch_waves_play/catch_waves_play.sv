module catch_waves_play;

   logic clk;
   logic [10:0] counter;


   initial begin
      #73;      
      $recordfile("my_waves.trn");
      $recordvars("depth=0", catch_waves_play);
      #100;
      $recordoff;
   end
   
   initial begin
      $display(" %m: STARTING NOW");      
      clk      = 0;
      counter  = 11'd0;      
      #500;
      $display(" %m: ENDING NOW");      
      $finish;      
   end

   always begin
      #3;
      clk      = ~clk;
      counter  = counter + 1'b1 ;            
      $display(" %m:  counter = %0d  clk=%0b",counter,clk);            
   end // forever begin
   

endmodule
