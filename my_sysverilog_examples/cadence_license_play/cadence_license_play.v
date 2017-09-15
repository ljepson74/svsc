module cadence_license_play;

   reg [7:0] magic_bus;
   
   initial begin
      $monitor($time, " %m: magic_bus=%2h",magic_bus);

      repeat (4) begin
	 magic_bus  = $urandom;
	 #400;	 
      end   
   end   

endmodule
