module logger;

   bit [3:0] bit4;
   
   initial begin
      bit4=4'b0001;
      $display("bit4=%4b   clog2=%0d log10=%0d", bit4, $clog2(bit4), $log10(bit4));
      bit4=4'b0010;
      $display("bit4=%4b   clog2=%0d log10=%0d", bit4, $clog2(bit4), $log10(bit4));
      bit4=4'b0100;
      $display("bit4=%4b   clog2=%0d log10=%0d", bit4, $clog2(bit4), $log10(bit4));
      bit4=4'b1000;
      $display("bit4=%4b   clog2=%0d log10=%0d", bit4, $clog2(bit4), $log10(bit4));
   end

   
endmodule