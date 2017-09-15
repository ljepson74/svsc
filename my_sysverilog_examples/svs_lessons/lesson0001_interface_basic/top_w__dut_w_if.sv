module top_w__dut_w_if;

   integer dut_score;

   score_items_if that_if();   


   stimulus stimulus(
		     .out_age(     that_if.if_age),
		     .out_iq(      that_if.if_iq),
		     .out_shoesize(that_if.if_shoesize)
		     );

   dut_w_if dut(.this_if(that_if), .out_score(dut_score));

   
    initial begin
        $monitor($time, " new score is: %0d", dut_score);
    end    


endmodule // top_w__dut_w_if
