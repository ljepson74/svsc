module stimulus(score_if the_if);
   initial begin
      repeat (3) begin	 
	 the_if.if_age      = $urandom;
	 the_if.if_iq       = $urandom;
	 the_if.if_shoesize = $urandom;
	 #10;	 
      end
   end
endmodule


