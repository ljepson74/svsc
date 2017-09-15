/*
Do fixed size arrays not support .size()?
If so, is this b/c 
 a) the expectation is that someone uses a paramater/constant to specify the size and that they can just use it again
 b) fixed sizes arrays were part of pre-SystemVerilog Verilog, and as such missed this convenient feature.
 
Or, am I doing smthg wrong below?

Running irun 13.1, I am told that it (size()) "is not a valid built in method name for this object".

  */

module top;
   
   int farray[10];  //fixed array

   initial begin

//1    for (int jjj=0; jjj<10; jjj++) begin             //works
/*2*/  for (int jjj=0; jjj<farray.size(); jjj++) begin  //doesn't work
//3    for (int jjj=0; jjj<$size(farray); jjj++) begin  //works
	 farray[jjj] = $urandom_range(121,0);
      end

      $display("******************************");
      for (int jjj=0; jjj<10; jjj++) begin
	 $display("%0d: %0d",jjj,farray[jjj]);
      end

   end

endmodule : top
