`timescale 1ns/100ps

module catch_waves_trn_vcd_play;

   logic rst_;
   logic clk;

   logic junk;
   
   
   initial begin
      $display($time," %m:  .vcd vs. .trn question that arose......(see code comments)");      
      clk   = 1;
//      #5ns;      
      junk  = 0;      
      forever begin    //10. I understand that this will hang-up the sim and it won't advance past this.
	 #5ns clk = ~clk; 
	 $display($time," %m: toggle the clock.");	 
      end
      #50ns rst_ = 1;
      #5ns  rst_ = 0;
      #5ns  rst_ = 1; 
      $finish;
      
   end


   //lkj doesn't like putting this here. where is better
   initial begin
      //simvision
      $recordfile("verilog.trn");  //20. so no time elapses and this has no data in it
      $recordvars("depth=0",catch_waves_trn_vcd_play);

      //vcd for gtkwave
      $dumpfile("verilog.vcd");  //30. but why then does this grow
      $dumpvars(0,catch_waves_trn_vcd_play);
   end


   //40.  ok.  maybe the trn file does not need to grow in size and has some equation to indicate that that a 1b signal is toggling w/ 5ns period.  But, I can't open the .trn with simvision and see the toggling clk, but in the .vcd (text inspection) I see the clk toggling

endmodule
