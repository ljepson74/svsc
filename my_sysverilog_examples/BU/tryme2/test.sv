program test(memory tbf0);
   initial begin
      tbf0.addr  <= 8'h55;
      #10;
      tbf0.addr  <= 8'h95;
      #10;
   end

endprogram // test
