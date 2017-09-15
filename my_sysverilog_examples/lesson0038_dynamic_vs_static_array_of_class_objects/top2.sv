/*
Do fixed size arrays not support .size()?
If so, is this b/c 
 a) the expectation is that someone uses a paramater/constant to specify the size and that they can just use it again
 b) fixed sizes arrays were part of pre-SystemVerilog Verilog, and as such missed this convenient feature.
 
Or, am I doing smthg wrong below?

Running irun 13.1, I am told that it (size()) "is not a valid built in method name for this object".

  */

module top;

class tiny;
   int age;
endclass : tiny
   
   int farray[10];  //fixed array
   //tiny farray[9:0];  //fixed array

   initial begin

      for (int jjj=0; jjj<10; jjj++) begin
//	 farray[jjj] = new();
      end

//    for (int jjj=0; jjj<10; jjj++) begin
      for (int jjj=0; jjj<farray.size(); jjj++) begin  //size() not allowed ?
//	 farray[jjj].age = $urandom_range(121,0);
	 farray[jjj] = $urandom_range(121,0);
      end

      $display("******************************");
      for (int jjj=0; jjj<10; jjj++) begin
//	 $display("%0d: %0d",jjj,farray[jjj].age);
	 $display("%0d: %0d",jjj,farray[jjj]);
      end

   end

endmodule : top
