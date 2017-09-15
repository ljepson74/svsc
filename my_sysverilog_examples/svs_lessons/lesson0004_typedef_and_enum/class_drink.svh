typedef int unsigned drink_cost;   //2-state.  never negative

module tb;

   drink_cost some_cost;

   initial begin
      some_cost  = -1;
      #1;      
      some_cost  = {100{1'b1}};
      #1;      
      some_cost  = 12;
      #1;      
      some_cost  = -4;
   end

   initial begin
      $monitor("******************>>> some_cost = dec:%10d  \t\t hex:%16x", some_cost, some_cost);
   end

endmodule


/*
class class_drink();

   drink_cost cost;

   function void new();
      cost  = 1;
   endfunction

endclass
*/