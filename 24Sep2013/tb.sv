module a(input [3:0] d,  output m);
   assign m = &d;
endmodule


module yyy(input a,output [3:0] d);
   assign d = {~a, 3'd0};
endmodule


module tb();
   wire a;
   assign a = 0;

//   wire [3:0] d;
//   wire d;

   yyy yyy0(.a(a), .d(d));
   a a0(.d(d), .m(m));

   initial
     $monitor("hello and hola and nihao %x", m);

endmodule
