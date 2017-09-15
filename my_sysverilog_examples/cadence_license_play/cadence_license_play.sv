
module cadence_license_play;

   reg [7:0] magic_bus;
   reg 	     clk;
   string    my_message;   
   reg 	     high_one;
   
   
/*
covergroups are used for functional coverage.

no covergroups 
covergroups in an ifdef
covergroups no in an ifdef
 
irun cadence_license_play.sv
I use the following licenses.

 
  Users of Incisive_Enterprise_Simulator:  (Total of 3 licenses issued;  Total of 3 licenses in use) /
   Incisive_Enterprise_Simulator v10.2, vendor: cdslmd /
    linc.jepson octocore.internal.caustic.com octocore.internal.caustic.com:74 (v8.100) (tatou/5280 197), start Mon 1/31 15:50 /
  Users of VERILOG-XL:  (Total of 3 licenses issued;  Total of 3 licenses in use) /
   VERILOG-XL  v10.2, vendor: cdslmd /
    linc.jepson octocore.internal.caustic.com octocore.internal.caustic.com:74 (v8.100) (tatou/5280 772), start Mon 1/31 15:50 /

    Incisive_HDL_Simulator    (Cheaper
     Incisive_Enterprise_Simulator (Pricier
  */
   
       
   initial begin
      $monitor($time, " %m: magic_bus=%2h",magic_bus);
      clk 	    = 0;      
      high_one 	    = 1'b1;
      
      
      repeat (900000) begin
	 magic_bus  = $urandom;
	 #400;	 
	 end
      $display(" **** WE ARE ALL DONE **** ");      
      $finish;      
   end   

   always begin
      clk  = #15 ~clk;      
   end

`ifdef NOPE   
   covergroup my_cg @(posedge clk);
      smthg_registered : coverpoint (magic_bus);      
   endgroup   
`endif
   assert property ( @(posedge clk) ( (high_one != 1'b0) ) );   

   
endmodule


