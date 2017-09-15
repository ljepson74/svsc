interface i2;
   wire a,b,c,d;
   modport master (input a, b, output c, d);
   modport slave  (input c, d, output a, b);
endinterface // i2

module m (i2.master i);
endmodule // m

module s (i2.slave i);
endmodule // s

module top;
   i2 i();

   m u1(.i(i));
   s u2(.i(i));
endmodule // top
