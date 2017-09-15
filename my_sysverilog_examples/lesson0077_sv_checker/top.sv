module top;
checker my_checker;
  as_fail : assert property(1==0) else begin
     $display("You're a failure. * * * ***");
  end   
endchecker

  //my_checker my_check;

   initial begin
      #55;
      $finish;
   end

endmodule // top
