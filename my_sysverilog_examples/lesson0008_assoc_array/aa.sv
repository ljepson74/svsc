module aa;

   integer aa [bit [15:0]];

   initial begin
      aa  = '{2:5, 6:55, 7:3, 16'hFFFE:-6};
      show();
      aa.delete(6);      
      show();
      aa[8]  =33;      
      show();
   end

   
   function void show();
      foreach (aa[i]) begin
	 $write("aa[%4h]=%0d, ",i,aa[i]);	 
      end
      $display("");   
      $display(" aa size =%0d",aa.size());      
   endfunction   
endmodule // aa
