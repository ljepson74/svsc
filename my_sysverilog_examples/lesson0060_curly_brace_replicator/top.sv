module top;

   logic [31:0] smthg;

   initial begin
      smthg = {1{$random}};
      $display("***** smthg=%0b",smthg);
      $finish;
   end

endmodule // top
