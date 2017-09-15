module top;

class C;
   int c1 = 1;
   int c2 = 1;
   int c3 = 1;

   function new(int a);
      c2 = 2;
      c3 = a;
   endfunction

   function void show();
      $display("c1=%0d  c2=%0d  c3=%0d", c1,c2,c3);
   endfunction
endclass

class D extends C;
   int d1 = 4;
   int d2 = c2;
   int d3 = 6;

   function new;
      super.new(d3);
   endfunction   
endclass

initial begin
   C c_m;
   D d_m;
   c_m = new(13);
   c_m.show;

   d_m = new(333);
   d_m.show;
end
   
endmodule // top
