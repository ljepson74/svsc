module counter(clk,reset,enable,preload,preload_data,mode,detect,result);

parameter SIZE = 4;

input              clk;
input              reset;
input              enable;
input              preload;
input  [SIZE-1:0]  preload_data;
input              mode;
output             detect;
output [SIZE-1:0]  result;

wire               clk;
wire               reset;
wire               enable;
wire               preload;
wire   [SIZE-1:0]  preload_data;
wire               mode;
reg                detect;
reg    [SIZE-1:0]  result;

reg    [SIZE-1:0]  result_next = 0;
reg                detect_next = 0;

always @ (posedge clk or posedge reset)
   if (reset) begin
      result <= {SIZE{1'b0}};
      detect <= 0;
   end
   else begin
      result <= result_next;
      detect <= detect_next;
   end

always @ (enable or preload or mode or result) begin
 if (enable)
   if (preload)
     result_next = preload_data;
   else
     if (!mode)
       if (result == {SIZE{1'b1}})
         result_next = {SIZE{1'b0}};
       else
         result_next = result + 1;
     else
       if (result == {SIZE{1'b0}})
         result_next = {SIZE{1'b1}};
       else
         result_next = result - 1;

      if (enable && !preload && (result_next == {SIZE{1'b1}}))
         detect_next = 1'b1;
      else
         detect_next = 1'b0;
end

endmodule
