// Goal: can write a string like "AF41" and convert it to integer, w/o using an intermediate string variable?
//  i.e.       "AF41".atohex() .... or smthg like that.

module top;
   string a_string;


   initial begin
      a_string="F";
      $display(">>>>>>>>>>>>  a_string=%0d", a_string.atohex();

      $finish();
   end

endmodule
