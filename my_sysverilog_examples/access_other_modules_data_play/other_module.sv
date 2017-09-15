module other_module;

   logic [31:0] can_you_access_this;
   class_one class_one_a;

   initial begin
      class_one_a 	   =new();
      can_you_access_this  = 32'hFACC_AACE;
   end


   function logic [15:0] module_gimme_data_function;
      module_gimme_data_function  = class_one_a.my_data;
   endfunction //

   task module_gimme_data_task;
      output logic [15:0] result;
      result  = class_one_a.my_data;
   endtask
   
endmodule // other_module
