`timescale 1 ns / 1 ps

module topmodule;
import uvm_pkg::*;
import ml_uvm::*;
`include "uvm_macros.svh"
`include "packet.sv"

  // producer produces input data at port_out to drive the dut
  class producer #(type T=packet) extends uvm_component;
    uvm_blocking_put_port #(T) port_out;

    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      port_out=new("port_out",this);
    endfunction

    typedef producer#(T) this_type;
    `uvm_component_utils_begin(this_type)
    `uvm_component_utils_end

    task run_phase (uvm_phase phase);
      T p;
      phase.raise_objection(this);
        p = new();
        for (int i = 0; i < 5; i++) begin
          p.next();
          $display("\n#################");
          $display($realtime,, "SV producer::run, putting ", p.get_data());
          port_out.put(p);
          #50;
        end

        #100;
        $display("\n#################");
        $display($realtime,,"stopping test");
      phase.drop_objection(this);

    endtask

  endclass

  // checker accepts output data from the dut at imp_in
  class checker #(type T=packet) extends uvm_component;
    uvm_blocking_put_imp #(T,checker #(T)) imp_in;

    function new(string name, uvm_component parent=null);
      super.new(name,parent);
      imp_in=new("in",this);
    endfunction

    typedef checker#(T) this_type2;
    `uvm_component_utils_begin(this_type2)
    `uvm_component_utils_end

    task put (T p);
      $display($realtime,,"SV checker : received ",p.data);
    endtask

  endclass

  class env extends uvm_env;
    producer #(packet) prod;
    checker #(packet) chk;
  
    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction

    function void build();
      super.build();
      prod = new("producer", this);
      chk = new("checker", this);
    endfunction

    function void connect();
      $display("env::connect");
      // use mixed-language UVM connection function to connect
      // producer's port_out to SystemC DUT's export_in, and
      // checker's imp_in to SystemC DUT's port_out
      ml_uvm::connect(prod.port_out, "tbtop.dut.export_in", "packet");
      ml_uvm::connect(chk.imp_in, "tbtop.dut.port_out", "packet");
    endfunction

    `uvm_component_utils(env)

  endclass

  class test extends uvm_test;
    env top_env;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction
    
    function void build();
      super.build();
      top_env = new("top_env", this);
    endfunction

    `uvm_component_utils(test)

  endclass    
    
endmodule

