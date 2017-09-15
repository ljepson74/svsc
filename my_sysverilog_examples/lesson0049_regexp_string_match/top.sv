module top;

import uvm_pkg::*;
`include "uvm_macros.svh"
class aclass;
   uvm_cmdline_processor ulp=new();
endclass

   string resultsq[$];
   aclass aclass1;

   function void show_matches(input string note="junk");
      $display("\n\n*******************************");
      foreach(resultsq[pop]) begin
	 $display("%0s:>%0s<",note,resultsq[pop]);
      end
      //$display("*********************************");
   endfunction

   initial begin
      aclass1=new();

      aclass1.ulp.get_args(resultsq);
      show_matches("All the commandline args");


      if (aclass1.ulp.get_arg_matches("god",resultsq)) begin
	 show_matches("0) blank ");
      end

      if (aclass1.ulp.get_arg_matches("red",resultsq)) begin
	 show_matches("1) red ");
      end

      if (aclass1.ulp.get_arg_matches("+red",resultsq)) begin
	 show_matches("2) +red ");
      end

      if (aclass1.ulp.get_arg_matches("/red/",resultsq)) begin
	 show_matches("3) /red/ ");
      end

      if (aclass1.ulp.get_arg_matches("/\\+red/",resultsq)) begin
	 show_matches("4) /^red.*/ ");
      end

      if (aclass1.ulp.get_arg_matches("/\\+red$/",resultsq)) begin  //get exact match
	 show_matches("5) red ");
      end

      if (aclass1.ulp.get_arg_matches("/^\\+red$/",resultsq)) begin  //get with equal sign match
	 show_matches("6) red= ");
      end

      $display("************* ENDING SHOW ********************");
   end
endmodule : top
