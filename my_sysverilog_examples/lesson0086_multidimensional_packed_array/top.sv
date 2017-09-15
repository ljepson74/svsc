module top;

   bit [2:0] [7:0] mdpa1;  //multidimensional packed array #1
   bit [7:0] [2:0] mdpa2;  //multidimensional packed array #2

   initial begin

      mdpa1 = {8'hFF, 8'hFF, 8'd0};
      mdpa2 = {8'hFF, 8'hFF, 8'd0};

      for (int j=0; j<=2; j++) begin
         $display("mdpa1[%0d]=0x:%0x = bin:%0b",j, mdpa1[j], mdpa1[j]);
      end
      for (int j=0; j<=2; j++) begin
         $display("mdpa2[%0d]=0x:%0x = bin:%0b",j, mdpa2[j], mdpa2[j]);
      end

      $display($time,"\n\n mdpa1=%0x",mdpa1);
      $display($time,"\n\n mdpa2=%0x",mdpa2);
   end // initial begin


//   function void read_packed;
//      for (int j=0; j<=2; j++) begin
//         $display("mdpa1[%0d]=0x:%0x = bin:%0b",j, mdpa1[j], mdpa1[j]);
//      end
//   endfunction
//
//
//
//   function void set_packed_a;
//      input logic [7:0] junk;
//
//      for (int i=0; i<=2; i++) begin
//         mdpa1[i]  = junk;
//         junk         = junk+ 1 ;  //$urandom;
//      end
//   endfunction
//
endmodule : top
