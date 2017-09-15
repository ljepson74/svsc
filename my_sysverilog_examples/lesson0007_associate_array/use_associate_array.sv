module use_assiciate_array;

   string aa_assocarray[integer];

   initial begin
      aa_assocarray  = '{0:"zero",1:"one",2:"two",3:"three",4:"four"};
      aa_show;
      aa_assocarray.shuffle();
      aa_show;      
   end


   function void aa_show;
      foreach (aa_assocarray[iii]) begin 
	 $display(" iii=%0d  aa_assocarray[iii]=%0s", iii, aa_assocarray[iii]);	 
      end
      $display("");
   endfunction
   

endmodule