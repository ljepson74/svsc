module dut(
    input integer in_age,
    input integer in_iq,
    input integer in_shoesize,
    output integer out_score
	);


    always@(*) begin
        out_score = (in_age * in_iq * in_shoesize)%101;  
    end


endmodule
