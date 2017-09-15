module top;
  
class object;
   rand bit coin;
   int percent_heads = 10;
      
   function new();
      //assert(randomize(coin) with {coin==1; coin==0;})      else begin endit("#1"); end
	
      //assert(std::randomize(coin) with {coin==1; coin==0;}) else begin endit("#2"); end
      
      //if(! (randomize(coin) with {coin==1; coin==0;}) )          begin endit("#3"); end

      //if(! (std::randomize(coin) with {coin==1; coin==0;}) )     begin endit("#4"); end
      

      if(! (randomize(coin) with {coin dist{1:=(percent_heads),0:=(100-percent_heads)} ;}) )     begin endit("#4"); end
   endfunction

   function void endit(input string note);
      $display("**********Failed %0s",note); $finish;
   endfunction
endclass

   object obj;
      
   initial begin
      $display("******* Going to play with coin");
      repeat (7) begin
	 obj=new();
	 $display("******* flip.... coin=%0b",obj.coin);
      end
   end

endmodule