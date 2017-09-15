module top;

   bit   clk;
   logic write_valid;
   logic write_data;

   always clk = #5 !clk;

   initial begin
      clk=0;
      write_valid=0;
      #7;
      write_valid=1;
      
      #100;
      $finish;
   end

   as_showme : assert property (@(posedge clk) disable iff (!write_valid) (!$isunknown(write_data)) ) else begin
      $display("*** ERROR. write_data was unknown. ***");
   end

endmodule