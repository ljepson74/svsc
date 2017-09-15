module dut(score_if this_if,
	   output integer out_score
	   );
    always@(*) begin
        out_score= (this_if.if_age * 
		    this_if.if_iq  * 
		    this_if.if_shoesize)
	  %101;  
    end
endmodule
