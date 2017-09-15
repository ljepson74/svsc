module real_play;   

   real      dumbo;
   //not supported by IUS8.2    shortreal gumbo;
   
   
   initial begin
      dumbo  = 4.54321e0;
      //gumbo  = 4.54321e0;
      show_em(" dumbo is real.   gumbo is shortreal");      

      dumbo  = -dumbo;      
      //gumbo  = -gumbo;
      show_em(" negated both");      
   end


   function void show_em;
      input string msg;
      $display(" %0s ",msg);

      //      $display(" dumbo>>(e)%0e (f)%0f<<   gumbo>>(e)%0e (f)%0f<<",dumbo, dumbo,  gumbo, gumbo);
      $display(" dumbo>>(e)%0e (f)%0f<<",dumbo, dumbo);

   endfunction
   
endmodule //
