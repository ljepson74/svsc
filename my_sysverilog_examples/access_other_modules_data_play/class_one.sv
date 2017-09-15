class class_one;

   logic [15:0] my_data;

   function new();
      my_data  =16'hEE77;      
   endfunction

   function logic [15:0] gimme_data_function;
      gimme_data_function  = my_data;      
   endfunction //

   task gimme_data_task;
      output logic [15:0] result;
      result  = my_data;     
   endtask
   
endclass
