//array locator methods (working with queues)
module my_array2;
   parameter SIZE = 5;

   class_y genesis;
   class_y my_array[SIZE];
   integer results[$];
   
   initial begin
      genesis=new();

      for (int i=0; i<SIZE; i++) begin
	 void'(genesis.randomize());
	 genesis.show();
	 my_array[i]=genesis;
      end

      results = my_array.find_index with (item.int1<0);
      show_q2();
      
/*    my_array  = {-2,1,4,0,-8};
      show_q();
      $display("--------------");

      results  = my_array.min(x) with (x<-1);
      show_q2();
      results  = my_array.max(x) with (x<7);
      show_q2();
      results = my_array.unique(x)  with (x>-1);
      show_q2();
      results = my_array.find_index with (item>0);
      show_q2();
*/
    end


   function void show_q();
      $write("my_array=");
      for (int iii=0; iii<SIZE; iii++)
        $write("[%2d]",iii);
      $display("");  $write("          ");
      for (int iii=0; iii<SIZE; iii++)
        $write("%2d  ",       my_array[iii]);
      $display("");
   endfunction

   function void show_q2();
      $display("results.size()=%0d",results.size());
      $write("res=");
      for (int iii=0; iii<results.size(); iii++)
       $write("[%2d]",iii);
      $display("");  $write("     ");
      for (int iii=0; iii<results.size(); iii++)
        $write("%2d  ",       results[iii]);
      $display("");
   endfunction

endmodule
