module pass_object_handle_thru_queue_play;

   high_class high_class_guy;
   int i;
   integer many;
   
   high_class class_q [$];
   
   
   initial begin
      i 	     =1;
      many 	     =5;
      
      
      repeat (many) begin
	 high_class_guy 			     = new(.whoami("Jessie"), .whoami_number("12"));	 

	 case (i)
	   1: begin high_class_guy.identifier	     ="Adam";   high_class_guy.number=i;  end
	   2: begin high_class_guy.identifier	     ="Bill";   high_class_guy.number=i;  end
	   3: begin high_class_guy.identifier	     ="Chas";   high_class_guy.number=i;  end
	   4: begin high_class_guy.identifier	     ="Dave";   high_class_guy.number=i;  end
	   5: begin high_class_guy.identifier	     ="Elon";   high_class_guy.number=i;  end
	   default: begin high_class_guy.identifier  ="Mr.X";   high_class_guy.number=-1;  end
	 endcase

	 i++;	   

	 class_q.push_back(high_class_guy);	 
	 end

      i 		 =0;      
      repeat (many) begin
	 high_class_guy  = class_q.pop_back();

	 $display(" %m: high_class_guy.identifier=%0s",high_class_guy.identifier);
	 
	 i++;	
      end

   end

endmodule
