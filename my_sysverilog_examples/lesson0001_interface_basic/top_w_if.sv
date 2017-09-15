module top_w_if;

   integer dut_score;

   score_items_if my_if();


   stimulus stimulus( .out_age(     my_if.if_age),
		      .out_iq(      my_if.if_iq),
		      .out_shoesize(my_if.if_shoesize)
		     );

   dut dut( .in_age(     my_if.if_age),
	    .in_iq(      my_if.if_iq ),
	    .in_shoesize(my_if.if_shoesize),
	    .out_score(dut_score)
	    );

   initial begin
      $monitor($time, " new score is: %0d", dut_score);
   end

endmodule // top_w_if
