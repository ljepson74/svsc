module tb;

  import "DPI-C" context function int gate(input int a, b);
  logic a;

  initial
    begin
       a = gate(1,2);
       $display("hello %x", a);
       $finish();
    end

endmodule
