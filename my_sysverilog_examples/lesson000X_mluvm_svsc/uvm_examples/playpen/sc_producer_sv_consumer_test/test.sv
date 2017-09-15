
module topmodule;
// import the ml_uvm package to enable mixed-language UVM communication
import uvm_pkg::*;
import ml_uvm::*;

`include "uvm_macros.svh"
`include "packet.sv"
`include "consumer.sv"
  class env extends uvm_env;
    consumer #(packet) cons;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction

    function void build();
      $display("env::build");
      super.build();
      cons = new("consumer", this);
    endfunction

    function void connect();
      $display("env::connect");
      // register the uvm_blocking_put_imp of consumer for mixed-language
      // UVM communication
      ml_uvm::external_if(cons.in, "packet");
    endfunction

    `uvm_component_utils(env)

  endclass    

  class svtest extends uvm_env;
    env top_env;

    function new (string name, uvm_component parent=null);
      super.new(name,parent);
    endfunction

    function void build();
      $display("svtest::build");
      super.build();
      top_env = new("top_env", this);
    endfunction

    `uvm_component_utils(svtest)
  endclass    

endmodule
