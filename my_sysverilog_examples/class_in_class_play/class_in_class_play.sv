module class_in_class_play;

   c1 my_c1;

   initial begin
      my_c1  = new();

      $display("----going to try to do something now------");      
      my_c1.my_c2.do_smthg;     
      $display("----just tried to do something      ------");      
   end

endmodule // class_in_class_play



