//imitates punit_sim_top

module op_top;

   logic reset;   
   logic bus8_a;
   logic bus8_b;
   logic bus9;   
      
   dut dut(
	   .rst    (reset),
	   .in_a   (bus8_a), 
	   .in_b   (bus8_b), 
	   .out_ab (bus9)
	   );
   
   stim_gen stim_gen(
		     .reset  (reset),
		     .drive1 (bus8_a),
		     .drive2 (bus8_b),
		     .result (bus9)
		     );

endmodule
