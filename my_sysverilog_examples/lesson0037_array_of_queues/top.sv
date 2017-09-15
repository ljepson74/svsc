module top;

   int sole_q[$];
   int a_qs[3][$];  //array of queues

   function void ss(input string note="empty"); //show sizes
      $display("sizes: sole=, a_[0],[1],[2]=  %0d, %0d,%0d,%0d   //%0s",
	       sole_q.size(), a_qs[0].size(), a_qs[1].size(), a_qs[2].size(),note);
   endfunction

   
   initial begin

      ss("START");
      sole_q={1,2,3}; a_qs[0]={1};a_qs[1]={1,2};a_qs[2]={1,2,3};
      ss("A");
      sole_q.delete();
      ss("DEL SOLE");
      a_qs[1].delete();
      ss("DEL A_ [1]");
//illegal      a_qs.delete();
//illegal      a_qs[2:0].delete();
//illegalorimpossible      ss("DEL A_ [all]");
      sole_q={1,2,3,4};
      ss("REFILL SOLE");
      
   end
endmodule
