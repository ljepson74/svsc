
// Filename: uvm_reg_layer.sv

//----------------------------------------------------------------------
//  Copyright (c) 2011-2012 by Doulos Ltd.
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.
//----------------------------------------------------------------------

// First Steps with UVM - source code examples

// Author: John Aynsley, Doulos
// Date:   14-Sep-2012


`include "uvm_macros.svh"

interface dut_if;

  // Simple synchronous bus interface
  logic clock, reset;
  logic en;
  logic cmd;
  logic [7:0] addr;
  logic [7:0] wdata;
  logic [7:0] rdata;

endinterface


module dut(dut_if dif);

  import uvm_pkg::*;

  // Two memory-mapped registers at addresses 0 and 1
  logic [7:0] r0;
  logic [7:0] r1;
  
  always @(posedge dif.clock)
  begin
 
    if (dif.en)
    begin
      logic [7:0] value;
      
      if (dif.cmd == 1 )
        if (dif.addr == 0)
          r0 <= dif.wdata;
        else if (dif.addr == 1)
          r1 <= dif.wdata;
        
      if (dif.cmd == 0)
        if (dif.addr == 0)
          value = r0;
        else if (dif.addr == 1)
          value = r1;
        else
          value = $random;

      if (dif.cmd == 1)
        `uvm_info("", $sformatf("DUT received cmd=%b, addr=%d, wdata=%d",
                            dif.cmd, dif.addr, dif.wdata), UVM_MEDIUM)
      else
        `uvm_info("", $sformatf("DUT received cmd=%b, addr=%d, rdata=%d",
                            dif.cmd, dif.addr, value), UVM_MEDIUM)
      dif.rdata <= value;
    end
  end
  
endmodule


package my_pkg;

  import uvm_pkg::*;
  
  class my_reg extends uvm_reg;
    `uvm_object_utils(my_reg)
    
    // An 8-bit register containing a single 8-bit field

    rand uvm_reg_field f1;

    function new (string name = "");
      super.new(name, 8, UVM_NO_COVERAGE);   // #bits = 8
    endfunction
    
    function void build;                     // NB build, not build_phase
      f1 = uvm_reg_field::type_id::create("f1");
      f1.configure(this, 8, 0, "RW", 0, 0, 1, 1, 0);  
                // reg, bitwidth, lsb, access, volatile, reselVal, hasReset, isRand, fieldAccess
    endfunction

  endclass


  class my_reg_model extends uvm_reg_block;
    `uvm_object_utils(my_reg_model)
    
    // A register model containing two registers
    
    rand my_reg r0;
    rand my_reg r1;
    
    function new (string name = "");
      super.new(name, build_coverage(UVM_NO_COVERAGE));
    endfunction

    function void build;
      r0 = my_reg::type_id::create("r0");
      r0.build();
      r0.configure(this);
      r0.add_hdl_path_slice("r0", 0, 8);      // name, offset, bitwidth

      r1 = my_reg::type_id::create("r1");
      r1.build();
      r1.configure(this);
      r1.add_hdl_path_slice("r1", 0, 8);      // name, offset, bitwidth

      default_map = create_map("my_map", 0, 2, UVM_LITTLE_ENDIAN); // name, base, nBytes
      default_map.add_reg(r0, 0, "RW");  // reg, offset, access
      default_map.add_reg(r1, 1, "RW");  // reg, offset, access
      
      lock_model();
    endfunction

  endclass
  

  class my_transaction extends uvm_sequence_item;
  
    `uvm_object_utils(my_transaction)
  
    rand bit cmd;
    rand int addr;
    rand int data;
  
    constraint c_addr { addr >= 0; addr < 256; }
    constraint c_data { data >= 0; data < 256; }
    
    function new (string name = "");
      super.new(name);
    endfunction
    
    function string convert2string;
      return $sformatf("cmd=%b, addr=%0d, data=%0d", cmd, addr, data);
    endfunction

    function void do_copy(uvm_object rhs);
      my_transaction tx;
      $cast(tx, rhs);
      cmd  = tx.cmd;
      addr = tx.addr;
      data = tx.data;
    endfunction
    
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      my_transaction tx;
      bit status = 1;
      $cast(tx, rhs);
      status &= (cmd  == tx.cmd);
      status &= (addr == tx.addr);
      status &= (data == tx.data);
      return status;
    endfunction

  endclass: my_transaction


  class my_adapter extends uvm_reg_adapter;
    `uvm_object_utils(my_adapter)
    
    // The adapter to connect the register model to the sequencer
    
    function new (string name = "");
      super.new(name);
    endfunction
 
    function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      my_transaction tx;
      tx = my_transaction::type_id::create("tx");
      tx.cmd = (rw.kind == UVM_WRITE);
      tx.addr = rw.addr;
      if (tx.cmd)
        tx.data = rw.data;
      return tx;
    endfunction
    
    function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      my_transaction tx;
      assert( $cast(tx, bus_item) )
        else `uvm_fatal("", "A bad thing has just happened in my_adapter")

      if (tx.addr < 2) // Address is valid
      begin     
        rw.kind = tx.cmd ? UVM_WRITE : UVM_READ;
        rw.addr = tx.addr;
        rw.data = tx.data;  // For monitoring, need write data as well as read data
        rw.status = UVM_IS_OK;
      end
      else
        rw.status = UVM_NOT_OK;
    endfunction
      
  endclass
  
  
  class my_reg_seq extends uvm_sequence;

    `uvm_object_utils(my_reg_seq)

    function new (string name = "");
      super.new(name);
    endfunction
    
    my_reg_model regmodel;

    task body;
      uvm_status_e   status;
      uvm_reg_data_t incoming;
      
      if (starting_phase != null)
        starting_phase.raise_objection(this);

      regmodel.r0.write(status, .value(111), .parent(this));
      assert( status == UVM_IS_OK );

      regmodel.r1.write(status, .value(222), .parent(this));
      assert( status == UVM_IS_OK );

      regmodel.r0.read(status, .value(incoming), .parent(this));
      assert( status == UVM_IS_OK );
      assert( incoming == 111 )
        else `uvm_warning("", $sformatf("incoming = %4h, expected = 111", incoming))

      regmodel.r1.read(status, .value(incoming), .parent(this));
      assert( status == UVM_IS_OK );
      assert( incoming == 222 )
        else `uvm_warning("", $sformatf("incoming = %4h, expected = 222", incoming))

      if (starting_phase != null)
        starting_phase.drop_objection(this);  
    endtask
    
  endclass
  
  
  class my_driver extends uvm_driver #(my_transaction);
  
    `uvm_component_utils(my_driver)

    virtual dut_if dut_vi;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      // Get interface reference from config database
      if( !uvm_config_db #(virtual dut_if)::get(this, "", "dut_if", dut_vi) )
        `uvm_error("", "uvm_config_db::get failed")
    endfunction 
   
    task run_phase(uvm_phase phase);
      forever
      begin
        seq_item_port.get_next_item(req);

        // Wiggle pins of DUT
        dut_vi.en    <= 1;
        dut_vi.cmd   <= req.cmd;
        dut_vi.addr  <= req.addr;
        if (req.cmd)
          dut_vi.wdata <= req.data;
          
        @(posedge dut_vi.clock);        
        dut_vi.en <= 0;
        
        if (req.cmd == 0)
        begin
          @(posedge dut_vi.clock);
          req.data = dut_vi.rdata;
        end
        
        seq_item_port.item_done();
      end
    endtask

  endclass: my_driver
  
  
  typedef uvm_sequencer #(my_transaction) my_sequencer;


  class my_env extends uvm_env;

    `uvm_component_utils(my_env)
    
    my_reg_model  regmodel;   // Recommended name
    my_adapter    m_adapter;

    my_sequencer m_seqr;
    my_driver    m_driv;
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
 
    function void build_phase(uvm_phase phase);
    
      // Instantiate the register model and adapter
      regmodel = my_reg_model::type_id::create("regmodel", this);
      regmodel.build();
      
      m_adapter = my_adapter::type_id::create("m_adapter",, get_full_name());
      
      m_seqr = my_sequencer::type_id::create("m_seqr", this);
      m_driv = my_driver   ::type_id::create("m_driv", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
      regmodel.default_map.set_sequencer( .sequencer(m_seqr), .adapter(m_adapter) );
      regmodel.default_map.set_base_addr(0);        
      regmodel.add_hdl_path("top.dut1");

      m_driv.seq_item_port.connect( m_seqr.seq_item_export );
    endfunction
    
  endclass: my_env
  
  
  class my_test extends uvm_test;
  
    `uvm_component_utils(my_test)
    
    my_env m_env;
    
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
      m_env = my_env::type_id::create("m_env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
      my_reg_seq seq;
      seq = my_reg_seq::type_id::create("seq");
      if ( !seq.randomize() )
        `uvm_error("", "Randomize failed")
      seq.regmodel = m_env.regmodel;   // Set model property of uvm_reg_sequence
      seq.starting_phase = phase;
      seq.start( m_env.m_seqr ); 
    endtask
     
  endclass: my_test
  
  
endpackage: my_pkg


module top;

  import uvm_pkg::*;
  import my_pkg::*;
  
  dut_if dut_if1 ();
  
  dut    dut1 ( .dif(dut_if1) );

  // Clock generator
  initial
  begin
    dut_if1.clock = 0;
    forever #5 dut_if1.clock = ~dut_if1.clock;
  end

  initial
  begin
    uvm_config_db #(virtual dut_if)::set(null, "*", "dut_if", dut_if1);
    
    uvm_top.finish_on_completion = 1;
    
    run_test("my_test");
  end

endmodule: top
