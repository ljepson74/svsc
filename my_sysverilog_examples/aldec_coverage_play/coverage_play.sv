//
//  CASE 1.  Class.  Module w/ Covergroup in it.
//
class my_bus;  //parameterize my width, pls

   logic [31:0] bus;
 
   function new();
      $display("Making a new my_bus.");
      bus  = '0;
    endfunction

   function void change();
//      bus  = bus + 2'b11;               why doesnt cov seem to change when I use this instead of $random?
      bus  = $random();
      $display("bus=%32b",bus);
   endfunction

endclass // my_bus


module case1;

   my_bus bus1;
   real cov_results  = 1.666;

   covergroup my_bus_toggles;  //function sample(int argg);
      coverpoint bus1.bus;
      //coverpoint argg;
   endgroup // my_bus_toggles

   my_bus_toggles cg1;


   initial begin
      bus1     = new();   //make the bus;
      cg1      = new();
      cg1.start();

      repeat (11) begin
	 bus1.change;
	 cg1.sample();
	 #20;
      end // repeat (6)
      cg1.stop();

//      $display("* ** *** CASE1 COVERAGE=%e",cg1.get_inst_coverage());
      $display("* ** *** **** ***** ****** CASE1 COVERAGE=%e ****** ***** **** *** ** *",cg1.get_coverage());

      
      $finish;      
   end
endmodule // coverage_play



//
// CASE 2.  Below is sample taken from asic-world.com
//
module case2();

   logic [2:0] addr;
   wire [2:0]  addr2;

   assign addr2  = addr+1;

   covergroup address_cov;
      ADDRESS : coverpoint addr {
	 option.auto_bin_max=10;
      }
      ADDRESS2 : coverpoint addr2 {
	 option.auto_bin_max=10;
      }
   endgroup // address_cov

   address_cov my_cov 		       =new;

   initial begin
      my_cov.ADDRESS.option.at_least   =1;
      my_cov.ADDRESS2.option.at_least  =2;
      //start the coverage collection
      my_cov.start();
      //set the coverage group name
      my_cov.set_inst_name("FROM ASIC-WORLD");
      $monitor("addr8'h%x addr28'h%x",addr,addr2);
      repeat(11) begin
	 addr  =$urandom_range(0,7);
	 //sample the covergroup
	 my_cov.sample();
	 #10;
      end // repeat (10)
      //stop the coverage collection
      my_cov.stop();
      //display the coverage
      $display("* ** *** **** ***** ****** CASE2 COVERAGE=%e ****** ***** **** *** ** *",my_cov.get_coverage());
   end

endmodule // test


//
// CASE 3.  Below is another lkj attempt to use a covergroup in a class (which as I understand from a few sources, such as Chris Spear's verification book, putting covergroups in classes is suggested).
//
class class_w_covergroup;
   
   logic [31:0] bus;

   covergroup covergroup_in_class;
      coverpoint bus;      
   endgroup // covergroup_in_class
   
   function new();
      covergroup_in_class  = new();
      $display("Making a new my_bus.");
      bus  = '0;
   endfunction
   
   function void change();
      bus  = $random();
      $display("bus=%32b",bus);
      covergroup_in_class.sample();      
   endfunction


   function void wrap_it_up();
      covergroup_in_class.get_inst_coverage();
      $display(" - - - - - - -  my_class_w_covergroup's coverage is=%e",	       
	       covergroup_in_class.get_inst_coverage());
   endfunction // get_inst_coverage
   
   
endclass //


module case3();

   class_w_covergroup my_class_w_covergroup;
      
   initial begin
   
      my_class_w_covergroup  = new();
//      my_class_w_covergroup.start();  //Error: VCP2948
      #20;

      repeat (4) begin
	 my_class_w_covergroup.change;    //.change(); 
//	 my_class_w_covergroup.sample(); //Error: VCP2948
	 #20;	 
      end // repeat (n)      
//      my_class_w_covergroup.stop();

//      $display(" - - - - - - -  my_class_w_covergroup's coverage is=%e",	       
//	       my_class_w_covergroup.wrap_it_up);
      my_class_w_covergroup.wrap_it_up;      
      $finish;      
   end // initial begin   
   
endmodule

