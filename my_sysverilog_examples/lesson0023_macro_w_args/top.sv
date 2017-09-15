module top;

   logic man_clock;

`define append(f) f``_clock

`define msg(x) `" > x < `"
`define atif(name) `"function void frog_check_``name();   endfunction`"
`define atif2(name) function void frog_check_``name(input string mess);   $display("were %0s",mess); endfunction

   `atif2(vlad)

   initial begin
      $monitor("?_clock = %0x",`append(man));
      bar();
      `append(man) = 1'b1;
      $display("macro is: %0s",`atif(fita));
      $display("we have: %0s:", `msg(atif));
      frog_check_vlad("home, really");
      #1
      bar();
   end

   function void bar();
      $display(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
   endfunction
endmodule
