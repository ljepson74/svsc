//This package represents an auto-generated package, so I want to use these values in the enum
package allpkg;
   parameter [3:0] ASDF_RED   = 4'b1111;  //?? I want to use these
   parameter [3:0] ASDF_WHITE = 4'b0000;
   parameter [3:0] ASDF_BLUE  = 4'b0110;
   parameter [3:0] ASDF_GREEN = 4'b1001;

   typedef enum bit [3:0] {RED=ASDF_RED, WHITE=ASDF_WHITE, BLUE=ASDF_BLUE, GREEN=ASDF_GREEN} colors_e;
   typedef enum {BO,REX,DOTTIE,SAL,DI}  names_e;
endpackage


module top;
   import allpkg::*;

   colors_e  aa[names_e];  //associate array


   initial begin
      aa[names_e.BO]=RED;
      aa[DI]=GREEN;

      foreach(aa[xyz]) begin
	 $display("aa[%0s]=%0s",xyz.name(),aa[xyz].name());
      end

      $finish;
   end
endmodule : top
