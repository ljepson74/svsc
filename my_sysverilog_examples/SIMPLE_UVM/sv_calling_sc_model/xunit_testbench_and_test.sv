// Testbench of SV consumer over SC prodcuer:
// Instantiating a SV consumer, connecting it to a SC producer of test results


`ifndef SV_OVER_SC_TB_SV
`define SV_OVER_SC_TB_SV

`include "uvm_macros.svh"

module xunit_testbench_and_test;   
   
import uvm_pkg::*; 

// enable multi-language UVM communication
import ml_uvm::*;

`include "xunit_test_input.sv"
`include "stimulus.sv"

`include "xunit_test_output.sv"
`include "consumer.sv"

   // tb contains a consumer and connects it to the SC producer
  class xunit_tb extends uvm_env;
     consumer #(xunit_test_output) cons;
     stimulus #(xunit_test_input)  stimu;

     `uvm_component_utils(xunit_tb)

     function new (string name="xunit_tb", uvm_component parent=null);
	super.new(name, parent);
     endfunction

     function void build_phase(uvm_phase phase);
	super.build_phase(phase);
	cons   = consumer::type_id::create("consumer", this);
	stimu  = stimulus::type_id::create("stimulus", this);
     endfunction

     function void connect_phase(uvm_phase phase);
	super.connect_phase(phase);
	// register the uvm_blocking_put_imp of consumer for
	// multi-language UVM communication
	ml_uvm::external_if(cons.in, "xunit_test_output"); 
	ml_uvm::connect_names("sc_p_env.producer.out",
                              "xunit_tb.consumer.in");

	ml_uvm::external_if(stimu.stimulator, "xunit_test_input");	
	ml_uvm::connect_names("sc_p_env.producer.in",
			      "xunit_tb.stimulus.stimulator");

//?? why is the above xunit_tb.consumer.in instead of same with cons?

     endfunction

     task run_phase(uvm_phase phase);
        phase.raise_objection(this);
	cons.watchdog(200);
        phase.drop_objection(this);
     endtask

  endclass

endmodule

`endif //  `ifndef SV_OVER_SC_TB_SV

