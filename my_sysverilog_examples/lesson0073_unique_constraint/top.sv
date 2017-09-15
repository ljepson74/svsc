module top;

class uniqueone;
   rand bit [3:0] arrayme[16];

   constraint c_yes { unique {arrayme}; }


   function void post_randomize();
      foreach (arrayme[ioo]) begin
         $display("arrayme[%0d]=%4b",ioo,arrayme[ioo]);
      end
   endfunction
endclass

   uniqueone uniqueone_i;

   initial begin
      uniqueone_i=new();
      uniqueone_i.randomize();
   end

endmodule
