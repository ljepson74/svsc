module top;

class aclass;
   int index;

   function void get_latency;
      //assert (randomize(index) with {index inside {[1:5]}}) else begin  //WHAT IS THE PROPER SYNTAX?
      //assert (randomize(index) inside {[1:5]}) else begin               //WHAT IS THE PROPER SYNTAX?
      assert (randomize(index) with {index<=5;  index>=1;}) else begin    //WORKS
         $display("ERROR:  We failed!");
         $finish;
      end

      $display("RESULT: index=%0d",index);
   endfunction
endclass

   initial begin
      aclass a_class=new();
      a_class.get_latency();
      $finish;
   end
endmodule
