module top;
    integer stimulus_age;
    integer stimulus_iq;
    integer stimulus_shoesize;
    integer dut_score;


    stimulus stimulus(
        .out_age(stimulus_age),
        .out_iq(stimulus_iq),
        .out_shoesize(stimulus_shoesize)
    );

    dut dut(
        .in_age(stimulus_age),
        .in_iq(stimulus_iq),
        .in_shoesize(stimulus_shoesize),
        .out_score(dut_score)
      );
    
    initial begin
        $monitor($time, " new score is: %0d", dut_score);
    end 
    
   
endmodule

//q a file doesnt save (still has asterix) if it does not compile/pass-parse?
//q how can i start a new text file (verilog file for example, w/o having to use the mouse and go to the pull-down menus?)
//q: if I make a dut and then want to instantiate it, is there an easy way to just have it appear in code along with explicit port list, with empty connections for me to connect
//q: how can i turn on/off line-wrap, so code does/n't go off right of page?