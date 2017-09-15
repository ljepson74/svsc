class my_class;

   rand int   aside_check;

   rand logic [31:0] register_a;
   rand logic [31:0] register_b;

   constraint onlyone {

      //NOTE THAT THIS DISTIBUTION SEEMS TO WORK
      register_a[31:0] dist {
			     32'hFFFF_0000 := 900,
			     32'hDDDD_0000 := 1,
			     32'h9999_0000 := 0,
			     32'h9999_0000 := 0
			     };

      //NOTE THAT THIS DISTRIBUTION SEEMS TO WORK
      register_b[31:16] dist {
			      16'h3333 := 100,
			      16'h4444 := 100,
			      16'h2222 := 100,
			      16'h1111 := 100
			      };

      //NOTE THAT THIS DISRIBUTION DOES **NOT** SEEM TO WORK.  
      // The 'spread' of values is almost even, when it should be greatly skewed per the prob settings. 
      // HOWEVER, If I remove the 0 probability from one of the options, things are as expected.
      // This is true using Cadence IUS8.1s019.  When run with IUS92, the problem (unexpected behavior)
      //  is not present.
      register_b[15:00] dist {
			      16'h1111 := 0,        // SEE DIFFERENCE WHEN THIS "0" IS REPLACED W/ A "1"
			      16'h2222 := 9000,
			      16'h3333 := 1,
			      16'h9999 := 1
			      };
   }


   function new();
      register_a  = '0;
      register_b  = '0;
   endfunction

   function void show();
      $display("%m: register_a=%8x   -   register_b=%8x       aside_check=%0d",register_a,register_b,  aside_check);

//      $display("%m: register_a=%8x",register_a);
 //     $display("%m:                              register_b=%8x",register_b);
      //$display("%m: \n");
   endfunction

endclass


