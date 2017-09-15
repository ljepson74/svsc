module top;

   //return from a function

   bit [31:0] baseFs = 32'hFFFFFFFF;
   bit [31:0] base   = 32'h76543210;

   bit [15:0]  a_original;
   bit [0:+16] b_colon_1st;   //confusing. 17b. Saying range is from 0 thru positive 16.
   //bit [0+:16] c_colon_2nd; //illegal cannot use part select for declaration
   bit [16:+0] d_size_1st;    //confusing. 17b. Saying range is from 16 thru positive 0.

   initial begin
      //$monitor($time,"[3:0]=%2h, [0:+3]=%2h, [0+:3]=%2h", a_original, b_colon_1st, c_colon_2nd);
      $monitor($time,": [15:0]=%8h, [0:+15]=%8h, [16:+0]=%8h", a_original, b_colon_1st, d_size_1st);
      #1;

      //assign w/ expected overflow
      a_original   = baseFs;
      b_colon_1st  = baseFs;
      d_size_1st   = baseFs;
      //c_colon_2nd =8'hFF;  // b/c illegal declaration

      $display($time," %% partselect=%2h and it is:%0d",a_original[7+:8], $size(a_original));
      //$display($time," partselect=%2h",a_original[7:+8]);  //illegal
      #1;
      a_original  = base;
      b_colon_1st = base;
      #1;


      $display($time," clog2(5)=%0d  clog2(2)=%0d  clog2(1)=%0d  clog2(0)=%0d",$clog2(5),$clog2(2),$clog2(1), $clog2(0));
      $display($time," bits(5)=%0d  bits(2)=%0d  bits(1)=%0d  bits(0)=%0d",$bits(5),$bits(2),$bits(1), $bits(0));
      $finish;
   end

endmodule
