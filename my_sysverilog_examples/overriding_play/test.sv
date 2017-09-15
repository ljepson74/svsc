program test;
   initial
     begin
	#30;
	$display($time,"  ***************************");
	op_top.stim_gen.reset_it();
	$display($time,"  ***************************");
	op_top.stim_gen.setup_it();
	$display($time,"  ***************************");

	$display($time, " now what?");
	$display($time,"  * * * reset=%0b, in1=%0b in2=%0b,  answer=%0b",op_top.reset,op_top.bus8_a,op_top.bus8_b,op_top.bus9);
	repeat (3) begin op_top.stim_gen.rand_it(); #5; end
	#10;
     end // initial begin

endprogram // test
