//
// Producer of testresults - Contains TLM analysis port of xunit_test_output. Generates
// xunit_test_output, and write them to the port


`ifndef PRODUCER_SV
`define PRODUCER_SV


module topmodule;
import uvm_pkg::*; 
`include "uvm_macros.svh"
`include "xunit_test_output.sv"

// The producer class derives from uvm_component;
class producer extends uvm_component;
   uvm_analysis_port #(xunit_test_output) out; 
   `uvm_component_utils(producer)
   
   // constructor
   function new(string name="producer", uvm_component parent=null);
      super.new(name,parent);
      out = new("out", this);
      ml_uvm::external_if(out, "xunit_test_output");
   endfunction

   // produce tokens in the run() process
   task run_phase (uvm_phase phase);
      xunit_test_output pkt = xunit_test_output::type_id::create("pkt");

      phase.raise_objection(this);
      for (int i = 0; i < 5; i++) begin
	 bit success = pkt.randomize() with {data > 0 && data < 10;}; 
	 $display($realtime,," lkj, SV producer is putting out an xunit_test_output with data ", 
		  pkt.data);
	 out.write(pkt);
	 #10;
      end
      #100;
      $display($realtime,," stopping the test");
      phase.drop_objection(this);
   endtask
endclass
endmodule

`endif //  `ifndef PRODUCER_SV

