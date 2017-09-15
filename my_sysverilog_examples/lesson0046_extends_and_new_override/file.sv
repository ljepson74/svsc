//virtual class gramps;
class gramps;
   function new(input string caller="grampa");
      $display("******Gramps*****, by %0s",caller);
   endfunction
   virtual function shout();
      $display("******I AM GRAMPS*****");
   endfunction
endclass

class pops extends gramps;
   function new();
     //super.new(.caller("poppa"));
//    super.new();
      $display("******Pops*****");
//      super.new(.caller("poppa"));
   endfunction
   virtual function shout();
      super.shout();
      $display("******I AM POPS*****");
   endfunction
endclass // pops


module top;
   gramps gramps1;
   pops   pops1;

   initial begin
      $display("------------1------");
      gramps1 = new();
      $display("------------2------");
      pops1   = new();
      $display("------------3------");
//      gramps1.shout();
      $display("------------4------");
//      pops1.shout();
      $display("------------5------");
      $display("------------6------");
   end
   
endmodule

