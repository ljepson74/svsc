class stimulus #(type TT=xunit_test_input) extends uvm_component; //try using this?
//class stimulus extends uvm_component;
   uvm_analysis_port #(TT) stimulator;  //lkj ??
   `uvm_component_utils(stimulus)

   function new(string name="stimulus", uvm_component parent=null);
      super.new(name,parent);
      stimulator=new("stimulator",this);
      ml_uvm::external_if(stimulator, "TT");
   endfunction

//   typedef stimulus#(TT) that_type;
// THIS WONT WORK
//  `uvm_component_utils_begin(that_type)
//  `uvm_component_utils_end

   task run_phase(uvm_phase phase);
      TT start_data 	    = TT::type_id::create("start_data");

      phase.raise_objection(this);

      for (int jj=0; jj<5; jj++) begin
	 start_data.xstimulus  = jj;
	 $display($realtime,," %m: lkj, SV stimulus is creating data. %0d.", start_data.xstimulus);

	 stimulator.write(start_data);
	 #10;
      end

      #100;
      $display($realtime,," stopping the test");
      phase.drop_objection(this);
    endtask

endclass

