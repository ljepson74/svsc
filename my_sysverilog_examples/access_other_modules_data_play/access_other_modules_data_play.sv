module access_other_modules_data_play;
   logic [15:0] task_result;

   initial begin
      #500;
      //OKAY. WORKS AS EXPECTED
      $display($time," %m: DIRECT ACCESS INTO MODULE: %0h",other_module.can_you_access_this);

      //DOES NOT WORK. DOES CADENCE PLAN TO SUPPORT THIS?
//1      $display($time," %m: DIRECT ACCESS INTO MODULES OBJECT:  %0h",other_module.class_one_a.my_data);  //

      //DOES NOT WORK. WHEN WILL IT?  ncelab: *E,CUDACO   Unsupported hierarchical reference to dynamic object
//2      $display($time," %m: ACCESS MODULES OBJECT WITH FUNCTION: %0h",other_module.class_one_a.gimme_data_function());      

      //DOES NOT WORK. WHEN WILL IT?  ncelab: *E,CUDACO   Unsupported hierarchical reference to dynamic object
//3      other_module.class_one_a.gimme_data_task(.result(task_result));      
//3      $display($time," %m: ACCESS MODULES OBJECT WITH TASK: %0h",task_result);      
      

      //////////////////////////////////////////////////////////////////////////////
      //    LET'S JUST TRY TO ACCESS A FUNCTION/TASK IN ANOTHER MODULE, WHICH WILL ACCESS THE DATA
      //WORKS
      $display($time," %m: ACCESS MODULES OBJECT WITH PARENT MODULES FUNCTION: %0h",other_module.module_gimme_data_function());      

      //WORKS
      other_module.module_gimme_data_task(.result(task_result));      
      $display($time," %m: ACCESS MODULES OBJECT WITH PARENT MODULES TASK: %0h",task_result);      
      
      
      
   end // initial begin

endmodule // access_other_modules_data_play

