module top;

   //bit arraytosum[3:0];
   int arraytosum[3:0];

   initial begin
      //arraytosum={1'b0,1'b1,1'b1,1'b1};
      arraytosum={1,1,1,0};
      $display("sum is %0d",arraytosum.sum);
   end

endmodule : top
