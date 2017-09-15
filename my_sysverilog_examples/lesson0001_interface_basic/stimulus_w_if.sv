module stimulus_w_if( score_items_if s_if );   
   
   initial begin
      repeat (3) begin
	 #40;
	 s_if.if_age      = $urandom;
	 s_if.if_iq       = $urandom;
	 s_if.if_shoesize = $urandom;
      end
   end
   
endmodule
