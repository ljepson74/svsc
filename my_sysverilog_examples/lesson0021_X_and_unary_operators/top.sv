module top;

   //check for unknown on bus when valid=1
   
   initial begin
      test(1, 8'h80);
      test(1, 8'b1010101X);
   end
  

   function test(input logic valid, input  logic [7:0] bus, input string note="-");
      $display("\n\n             ****%0s****",note);
      $display("valid=%1b  bus=%2h   ",valid,bus);
      $display("|%2h=%1b   ",bus,(|bus)); 
      $display("&%2h=%1b   ",bus,(&bus)); 
      $display("^%2h=%1b   ",bus,(^bus)); 
      $display(" 1&(^bus)=%1b  ",(1&(^bus))); 
      $display(" 1|(^bus)=%1b  ",(1|(^bus))); 


      $display("\n");
   endfunction

endmodule : top
