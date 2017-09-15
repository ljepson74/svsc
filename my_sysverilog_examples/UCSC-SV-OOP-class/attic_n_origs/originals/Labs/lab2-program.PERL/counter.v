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

always @ (posedge clk or posedge reset)
begin
   if (reset)
      result <= {SIZE{1'b0}};
   else
      if (enable)
         if (preload)
            result <= preload_data;
         else
            if (!mode)
               if (result == {SIZE{1'b1}})
                  result <= {SIZE{1'b0}};
               else
                  result <= result + 1;
            else
               if (result == {SIZE{1'b0}})
                  result <= {SIZE{1'b1}};
               else
                  result <= result - 1;

      if (enable && !preload && (result == {SIZE{1'b1}}))
         detect <= 1'b1;
      else
         detect <= 1'b0;
end

endmodule
