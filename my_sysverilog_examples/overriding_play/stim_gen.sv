//imitates scene_gen.sv
program stim_gen
  (
   output logic reset,
   output logic [7:0] drive1,
   output logic [7:0] drive2,
   input  logic [8:0] result
   );

   `include "op_tb_tasks.sv"
   op_smthg myop;
   
   
   initial
     begin
	$monitor($time,"  * * * reset=%1b, in1=%8b in2=%8b,  answer=%9b",reset,drive1,drive2,result);	 
	reset  = 0;	
	myop   = new();		       
	assign drive1 	= myop.some_bus;
	assign drive2 	= myop.other_bus;   
	myop.constraint_mode(0);   
	myop.for_other.constraint_mode(1);	
	assert (myop.randomize());

	#5;
	
     end


   task setup_it();
      $display($time,"  %m start");
      #5;
      //      myop.for_other.constraint_mode(1);
      assert (myop.randomize());
      // myop.randomize();  WHY DOES THIS LINE NOT WORK, BUT WITH AN ASSERT AROUND IT, IT WORKS?
	myop.for_other.constraint_mode(1);	
	assert (myop.randomize());
	#5;
      $display($time,"  %m end");
   endtask // setup_it


   task reset_it();
      begin
	 $display($time,"  %m start");
	 #100;
      	 reset  = 0;
	 #5;
	 reset  = 1;
	 #100;
	 $display($time,"  %m end");
	end
   endtask // reset_it

   function void rand_it;	
      myop.for_other.constraint_mode(1);	
      assert (myop.randomize());
   endfunction
   
endprogram // stim_gen


   
