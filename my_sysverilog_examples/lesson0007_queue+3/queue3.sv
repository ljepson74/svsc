//array locator methods (working with queues)
module queue3;
   integer qqq[$], results[$];

   initial begin
      qqq  = {-2,1,4,0,4,-8,9};
      show_q();
      results  = qqq.min(x) with (x<-1);      
      show_q2();
      results  = qqq.max(x) with (x<7);      
      show_q2();
      results = qqq.unique(x)  with (x>-1);      
      show_q2();
   end

   function void show_q();
      $write("qqq=");
      for (int iii=0; iii<qqq.size(); iii++)
	$write("[%2d]",iii);
      $display("");  $write("     ");
      for (int iii=0; iii<qqq.size(); iii++)
	 $write("%2d  ",       qqq[iii]);
      $display("");      
   endfunction
   function void show_q2();
      $write("res=");
      for (int iii=0; iii<results.size(); iii++)
	$write("[%2d]",iii);
      $display("");  $write("     ");
      for (int iii=0; iii<results.size(); iii++)
	 $write("%2d  ",       results[iii]);
      $display("");
   endfunction

endmodule 
