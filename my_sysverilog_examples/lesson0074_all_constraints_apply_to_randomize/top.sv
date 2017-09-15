/*
 Yesterday I learned that when randomize is called, all active constraints must be met ... even if you are passing a specific member as an argument to the randomize call.

 i.e. If you try to randomize a specific class member by passing it to the randomize call, like this randomize(var2), all constraints in the scope of the randomize must still be met, even if they have nothing to do with the member being randomized.

 ***Someone please jump in if I phrased that poorly.

 In the below example there are two variables and a constraint on one.
 Uncommenting the line that causes a constraint on var1 to be violated will cause the later call to randomize to fail, even though it is passed an argument (var2) that has nothing to do with var1.
 
 I now understand randomize a bit better.

 (new development.  someone showed me soft constraints)
     */
class showit;
   rand int var1;
   rand int var2;
   
   constraint c_1 { soft var1<100; }
   //constraint c_2 { var1<100; }
endclass

//////////////////////////////////////
module top;
   showit showit;

   initial begin
      showit=new();

      showit.var1=101;   //UNCOMMENT ME, PLEASE.

      as_myassert : assert(showit.randomize(var2)) begin
	 $display("\n********** Victory : var2=%0d var1=%0d \n",showit.var2, showit.var1);
      end else begin
	 $display("\n********** Defeat  : var2=%0d var1=%0d \n",showit.var2, showit.var1);
      end

   end   
endmodule : top
