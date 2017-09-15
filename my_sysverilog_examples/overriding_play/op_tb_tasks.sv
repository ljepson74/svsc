//imitates punit_tb_tasks.sv
class op_smthg;
   rand logic [7:0] some_bus;
   rand logic [7:0] other_bus;

   constraint for_some{
      some_bus  inside  {[32:255]};
      other_bus inside  {[3:7]};
   }
   constraint for_other{
      some_bus  inside  {[3:7]};
      other_bus inside  {[32:255]};
   }


//   task send_smthg;
//   endtask // send_smthg

endclass // op_smthg
