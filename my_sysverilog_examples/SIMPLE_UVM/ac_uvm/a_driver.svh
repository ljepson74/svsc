import uvm_pkg::*;   //WHY DO I NEED THIS HERE?

class a_driver extends uvm_driver#(a_transaction);
   `uvm_component_utils(a_driver)

     virtual a_if.master_mp a_if_inst;

     function new (string name, uvm_component parent);
	super.new(name,parent);
     endfunction // new

   task reset();
      a_if_inst.master_cb.a_signal <= 0;
   endtask


/* -----\/----- EXCLUDED -----\/-----
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      void'(uvm_resource_db#(virtual my_if)::read_by_name(.scope("ifs"),.name("my_if"),.val(my_if_is)));
   endfunction: build_phase
 -----/\----- EXCLUDED -----/\----- */

   task run_phase(uvm_phase phase);
      //would instantiate transaction here

	 forever begin
	    @a_if_inst.master_cb;
	    `uvm_info(" my little simple test", $psprintf("toggling a_signal.")  , UVM_LOW)
	      a_if_inst.master_cb.a_signal <= 1'b1;
	    @a_if_inst.master_cb;
	    `uvm_info(" my little simple test", $psprintf("toggling a_signal.")  , UVM_LOW)
	    a_if_inst.master_cb.a_signal <= 1'b1;
	    @a_if_inst.master_cb;
	    `uvm_info(" my little simple test", $psprintf("toggling a_signal.")  , UVM_LOW)
	    a_if_inst.master_cb.a_signal <= 1'b0;
	 end
   endtask: run_phase


endclass: a_driver
