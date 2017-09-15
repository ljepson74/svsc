module top;

   logic [39:0] smthg = 666;
   
   
   initial begin
      #1 smthg = 'x;
      #1 smthg = '1;
      #1 smthg = 'z;
      #1 smthg = '0;
      #1 smthg = 'b?;
      
	      
   end

   always@(smthg) begin
      $display(" we have newline\nthere",smthg);
      $display(" we have formfeed\fthere",smthg);
      $display(" we have tab\tthere",smthg);
      $display(" we have vtab\vthere",smthg);
      $display(" smthg = %40b",smthg);
   end


endmodule : top
