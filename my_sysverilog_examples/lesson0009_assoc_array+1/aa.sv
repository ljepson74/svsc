module aa;

   integer aa [bit [15:0]];
   bit [15:0] ii,iii;   
   
   initial begin
      aa  = '{2:5, 6:55, 7:3, 16'hFFFE:-6, default:0};
      show();
      $display(" >>%0d",aa[88]);
      show();
      if (aa.exists(6)) begin
	 aa[6] 	= 6;
	 show();
      end // if (aa.exists(6))
      // first, last, next, prev
      if (aa.first(ii)) begin
	 void'(aa.first(iii));
	 void'(aa.next(iii));
	 $display(" aa[%0d]=%0d, aa[%0d]=%0d", ii, aa[ii], iii, aa[iii]);
	 aa[ii]  = aa[iii];	 
	 show();	 
      end
   end

   
   function void show();
      foreach (aa[i]) begin
	 $write("aa[%4h]=%0d, ",i,aa[i]);	 
      end
      $display("");   
      $display(" aa size =%0d",aa.size());      
   endfunction   
endmodule // aa
