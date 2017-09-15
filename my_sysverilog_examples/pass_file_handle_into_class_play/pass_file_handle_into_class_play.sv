//2011jan.  I am having trouble passing a file handle into a class instances


class my_class;
   integer my_handle;

   function new();
      input integer handle;
      this.my_handle  = handle;      
   endfunction

   function void print;
      $display(" %m: me me me  inside0");
      $fdisplay(my_handle," %m: me me me  inside1");
      $fdisplay(this.my_handle," %m: me me me .  inside2");
   endfunction
   
endclass // my_class


module pass_file_handle_into_class_play;

   integer handle_print_file;

   my_class obj_1;
   my_class obj_2;
   
   initial begin
      handle_print_file  = $fopen("pass_file_handle_into_class_play","a+");
      
      obj_1 = new(.handle(handle_print_file));
      obj_2 = new(.handle(handle_print_file));

      $fdisplay(handle_print_file," %m: HERE WE ARE");

      repeat (4) begin
	 obj_1.print();
	 obj_2.print();	 
      end
		
   end


endmodule // pass_file_handle_into_class_play


