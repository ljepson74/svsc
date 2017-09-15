//I needed to step thru an enum in a testbench today.  As it took me a while to figure out how to do it, I post a small example.
//I want to do it without making any assumptions of the values of the enums (values are the default type of int, in this case).
//Reference: SystemVerilog doc "1800-2012.pdf" Section 6.19 Enumerations

module top;
   //typedef enum {alpha=0, beta=1, gamma=2, delta=3, epsilon=4} greek;  //to show default assignments
   typedef enum {alpha, beta, gamma, delta, epsilon} greek;
   greek letters2;

   initial begin
      $display("****** Walk thru an enumeration example. ***********");

/*      for (greek letters=letters.first(), int walk=0;
	   walk < letters.num();
	   letters=letters.next(), walk++) begin */
	 for (greek letters=letters.first(); letters!=(letters.num()-1); letters=letters.next()) begin //neverending loop
	 $display(" %0d *** %0s", letters, letters.name);
      end

   end
endmodule : top

/*  Output:
****** Walk thru an enumeration example. ***********
 0 *** alpha
 1 *** beta
 2 *** gamma
 3 *** delta
 4 *** epsilon
*/
/*
I'm also posting here, because I find it easier to remember how I did smthg if post it online, than if I have to search thru all my old code.
I thought I did this nicely with a foreach loop, but cannot find it, so may be imagining it.

   Note: I was not keen on having to make the variable walk.
*/

//Noted failures:
      //for (greek letters=letters.first(); letters!=letters.last();    letters=letters.next()) begin //shows only 0-3
      //for (greek letters=letters.first(); letters<=(letters.num()-1); letters=letters.next()) begin //neverending loop

