module extern_play;


   initial begin
      class_mine class_mine_inst;  
      class_mine_inst  = new();     
      class_mine_inst.display_me;
   end

endmodule // extern_play
