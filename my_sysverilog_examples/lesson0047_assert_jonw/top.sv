module assert_box();

   
  bit clk;
  bit a;
  bit [3:0] b, c;
//    bit [3:0] exp_val;


  // Design, &c.

  initial begin
    // $vcdpluson();
     //$shm_open("waves.shm");
     //$shm_probe("A");

     @(posedge clk);
     a <= 1'b1;
     @(posedge clk);
     a <= 1'b0;
     @(posedge clk);
     a <= 1'b1;
     @(posedge clk);
     a <= 1'b0;
    $finish;
  end

  always
    clk = #5 ~clk;

  // Assertion
/*
  assert property (@(posedge clk)
		   (a, exp_val = get_val(b)) |=> c === exp_val);
*/
  always_ff @(posedge clk) begin
    if (a)  c <= ~b+1;
    b <= b + 1;
  end

//property my_prop(local output bit [3:0] exp_val);
  property my_prop;
    bit [3:0] exp_val;
     (a, exp_val = get_val(b), $display("%0t:eval-pre a=%0d exp_val=%0d",$time,a,exp_val) ) |=> 
//	      jonw("jon2a",0) && jonw("jon2b",1) |->
	      (c===exp_val) & jonw("jon2",0) |->
	      jonw("jon3",0);
  endproperty

  vladimir : assert property (@(posedge clk) my_prop) begin
         $display("JONPROP-PASS");
  end else begin
    $display("JONPROP-FAIL");
  end

   function bit jonw(input string note="junk",
		     input int value=0);
      $display("%0t:%0s",$time,note);
      return(value);
   endfunction
   
  function bit [3:0] get_val(bit [3:0] x);
    return ~x;
  endfunction
endmodule // assert_box

