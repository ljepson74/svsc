package leaf_pkg;

   function void leaf_hi();
      $display("%m: I am leaf");
   endfunction
/*
   checker my_check(logic a_signal);
   lkj9876543210: assert property (!$isunknown(a_signal));
   endchecker
   */
endpackage : leaf_pkg

/*module mod(input logic a_signal, clk);
   lkj9876543210: assert property 
   (@(posedge clk) !$isunknown(a_signal));
endmodule // mod
*/
checker mod(input logic a_signal, clk);
   lkj9876543210: assert property 
   (@(posedge clk) !$isunknown(a_signal));
endchecker // mod
