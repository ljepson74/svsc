module top_final;

   integer dut_score;

   score_items_if that_if();   

//   stimulus_w_if stimulus(.s_if(that_if));

   dut_w_if      dut(.this_if(that_if), .out_score(dut_score));

   
    initial begin
        $monitor($time, " new score is: %0d", dut_score);
    end    


endmodule // top_w__dut_w_if
