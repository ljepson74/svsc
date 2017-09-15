---------------------------------------------------------------
File name   :  xbus_accel.e
Title       :  Acceleration extensions
Project     :  XBus UVC
Developers  :  Cadence Design Systems
Created     :  November 2010
Description :  This file implements extensions required for acceleration.
            :  - Implementing UVM_ACCEL BFM and collector.
            :  - Disconnecting all ports, connects the clocks to sys.any
Notes       :
---------------------------------------------------------------
// (C) COPYRIGHT, Cadence Design Systems, Inc. 2010
// All Rights Reserved
// Licensed Materials - Property of Cadence Design Systems
//
// No part of this file may be reproduced, stored in a retrieval system,
// or transmitted in any form or by any means --- electronic, mechanical,
// photocopying, recording, or otherwise --- without prior written
// permission of Cadence Design Systems, Inc.
//
// WARRANTY:
// Use all material in this file at your own risk.  Cadence Design
// Systems makes no claims about any material contained in this file.
//
//---------------------------------------------------------------

<'
package cdn_xbus;

'>



UVM_ACCEL master bfm
====================

Connected to HW BFM

<'

extend UVM_ACCEL MASTER xbus_bfm_u {
    
    // The name of the instance of the HDL transactor, the xbus_master_driver_bfm
    keep hdl_path() == "driver_bfm";

    // Input - SW to HW
    m_ip : uvm_accel_input_pipe_proxy of MASTER xbus_trans_s is instance;
    // The name of the instance of the transactor input scemi port:
    keep m_ip.hdl_path() == "ipipe"; 

    // Output - HW to WW
    m_op : uvm_accel_output_pipe_proxy of MASTER xbus_trans_s is instance;
    // The name of the instance of the transactor output scemi port:
    keep m_op.hdl_path() == "opipe"; 

    // TLM ports, connected to the scemi
    m_in :  interface_port of tlm_put of MASTER xbus_trans_s is instance;
    m_out : interface_port of tlm_get of MASTER xbus_trans_s is instance;

    connect_ports() is also { 
        m_in.connect(m_ip.m_in);
        m_out.connect(m_op.m_out);
    };

    private drive_transfer(t : MASTER xbus_trans_s) @tf_phase_clock is {
       
        message(LOW, abstraction_level, " master_bfm drive: ", t,
                " address : ", t.addr,
                " read_write : ", t.read_write, 
                " size : ", t.size ); 

        if(t.read_write == WRITE) {
            m_in$.put(t);
        };
        if(t.read_write == READ) {
            t.data.resize(1);
            m_in$.put(t);
            m_out$.get(t);
        };
        message(HIGH, abstraction_level, " master_bfm done: ", t);
    };
    
    // in acceleration - do not wait for resetindication before starting 
    // driving transfers
    tf_env_setup() @tf_phase_clock is also {
       start drive_transfers();
    };
    
    private drive_transfers() @tf_phase_clock is only {
        
        // Until pases supported in Acceleration
        
        if tf_get_domain_mgr().get_current_phase() != ENV_SETUP {
            return;
        };
          
        while TRUE {
            var next_trans := driver.get_next_item();
            drive_transfer(next_trans);
            emit driver.item_done;
        };
    };
};


extend MONITOR xbus_trans_s {
    package log_transfer(leader : string) : string is only {
    };
};
extend xbus_trans_s {
    do_unpack(options:pack_options, l: list of bit, begin: int): int is only {
        var L : list of bit = l[begin..];
          
        unpack(packing.low, L, addr, size_ctrl, read_write);
        
        case size_ctrl {
            0 : {size = 1};
            1 : {size = 2};
            2 : {size = 4};
            3 : {size = 8};
        };
        
        for i from 0 to size-1 {
            data.add(pack(packing.low,L[24+i*8..24+i*8+7]))
        };
        
    };
};
extend xbus_trans_s {
    do_pack(options : pack_options, l :*list of bit) is also {
        
        // These bits are where HW BFM expects to see wait-states
        l[20] = 0;
        l[21] = 0;
        l[22] = 0;
        l[23] = 0;
   
        l.resize(24, TRUE, 0, TRUE);
            
        // Add the data
        for each in data {
            l.add(pack(packing.low,it));
        };
        
        l.resize(88, TRUE, 0, TRUE);
        
    };
};
'>


UVM_ACCEL MASTER monitor
========================

Connected to HW collector

<'

extend UVM_ACCEL MASTER xbus_agent_monitor_u {

    // The name of the instance of the HDL transactor, the xbus_master_driver_bfm
    keep hdl_path() == "monitor_bfm";

    // Output - HW to WW
    m_op : uvm_accel_output_pipe_proxy of MONITOR xbus_trans_s is instance;
    // The name of the instance of the transactor output scemi port:
    keep m_op.hdl_path() == "opipe"; 

    // TLM ports, connected to the scemi
    m_out : interface_port of tlm_get of MONITOR xbus_trans_s is instance;

    // Port exporting to upper levels 
    transfer_got_from_hw : out interface_port of tlm_analysis of
                                         MONITOR xbus_trans_s is instance;
    
    connect_ports() is also { 
        // Getting data -  Connect to Pipe Proxy port
        m_out.connect(m_op.m_out);
        
        // Sending data - Connect to monitor TLM port
        transfer_got_from_hw.connect(transfer_ended_o);
    };
    
    !transfer : MONITOR xbus_trans_s;
    
    collect_transfers() @sys.any is {

        while TRUE {
            transfer = NULL;       
            m_out$.get(transfer);
            transfer.master_name = agent_name;
            case transfer.size_ctrl {
                0 : {transfer.size = 1};
                1 : {transfer.size = 2};
                2 : {transfer.size = 4};
                3 : {transfer.size = 8};
            };
        
            message(LOW, abstraction_level, " Master monitor got transfer ",
                    transfer,
                    " address : ", transfer.addr,
                    " read_write : ", transfer.read_write,
                    " size : ", transfer.size); 
                        
            transfer_got_from_hw$.write(transfer);
        };
    };

   run() is also {
       start collect_transfers();
   };

};

'>


UVM_ACCEL slave bfm
===================

<'
extend UVM_ACCEL SLAVE xbus_bfm_u {

    // The name of the instance of the HDL transactor, the xbus_master_driver_bfm
    keep hdl_path() == "slave_driver_bfm";

    // Input - SW to HW
    m_ip : uvm_accel_input_pipe_proxy of xbus_slave_response_s is instance;
    // The name of the instance of the transactor input scemi port:
    keep m_ip.hdl_path() == "ipipe"; 


    // TLM ports, connected to the scemi
    m_in :  interface_port of tlm_put of xbus_slave_response_s is instance;

    connect_ports() is also { 
        m_in.connect(m_ip.m_in);
    };

    private drive_responses() @tf_phase_clock is only {
        // Do nothing. Responses will be done according to indication of 
        // transfer started, from the monitor
    };
    
    
    // Port getting started-transfers I should respond to 
     transfer_started_ip : in interface_port of tlm_analysis of
                                         MONITOR xbus_trans_s is instance;

    !next_response : xbus_slave_response_s;
      keep next_response.driver == me.driver;
      keep next_response.error_pos == UNDEF;
      
    // Port implementation 
    // Respond to transfer
    write(transfer : MONITOR xbus_trans_s) is {
        driver.transfer = transfer;
        
        transfer.data.clear();
        for i from 0 to transfer.size-1 {
            transfer.data.add(ram.read_byte(transfer.addr + i));
        };
        
        // Generate once, will be overriden during the run, 
        // according to current transfer
        if next_response == NULL then {
            gen next_response;
        };
        next_response.transfer = transfer;
        
        start respond(next_response);
    };
    
    respond(response : xbus_slave_response_s) @sys.any is {
        message(LOW, "Send response ", response);
        m_in$.put(response);
    };   
};


'>



UVM_ACCEL SLAVE monitor
========================

Connected to HW collector


<'

extend UVM_ACCEL SLAVE xbus_agent_monitor_u {
    !ram : simple_ram_env_u;

    // The name of the instance of the HDL transactor, the xbus_master_driver_bfm
    keep hdl_path() == "slave_monitor_bfm";

    // Output - HW to WW
    // This port is for data captured during the transaction
    m_op_partial : uvm_accel_output_pipe_proxy of MONITOR xbus_trans_s is instance;
    
    // The name of the instance of the transactor output scemi port:
    keep m_op_partial.hdl_path() == "opipe"; 

    // TLM ports, connected to the scemi
    m_out_partial : interface_port of tlm_get of MONITOR xbus_trans_s is instance;
   
    // Output - HW to WW
    // This port is for full transfer, captured at end ofthe transaction
    m_transfer_op : uvm_accel_output_pipe_proxy of MONITOR xbus_trans_s is instance;
    // The name of the instance of the transactor output scemi port:
    keep m_transfer_op.hdl_path() == "opipe_data"; 

    // TLM ports, connected to the scemi
    m_transfer_out : interface_port of tlm_get of MONITOR xbus_trans_s is instance;

    // Port exporting to upper levels 
    // Passing partial 
    partial_transfer_got_from_hw : out interface_port of tlm_analysis 
                                                      of MONITOR xbus_trans_s is instance;
     
    connect_ports() is also { 
        // Getting data -  Connect to Pipe Proxy port
        m_out_partial.connect(m_op_partial.m_out);
        
        // Getting data -  Connect to Pipe Proxy port
        m_transfer_out.connect(m_transfer_op.m_out); 
    };                           
    
    !transfer_partial : MONITOR xbus_trans_s;
    
    !during_transfer  : bool;
    
    // collect_transfers_full()
    //
    // Getting from a port that passes transfers both on started and and ended.
    // This method will handle only those passing on transfer started
    //
    collect_transfers_full() @sys.any is {
        while TRUE {
            transfer_partial = NULL;       
            m_out_partial$.get(transfer_partial);
            
            if during_transfer then {
                continue;
            };
            during_transfer = TRUE;
            transfer_partial.slave_name = agent_name;

            case transfer_partial.size_ctrl {
                0 : {transfer_partial.size = 1};
                1 : {transfer_partial.size = 2};
                2 : {transfer_partial.size = 4};
                3 : {transfer_partial.size = 8};
            };
            message(MEDIUM, abstraction_level, " Slave monitor got transfer started ", 
                    transfer_partial,
                    " address : ", transfer_partial.addr,
                    " read_write : ", transfer_partial.read_write,
                    " size : ", transfer_partial.size);
            partial_transfer_got_from_hw$.write(transfer_partial);
        };
    };

    !transfer : MONITOR xbus_trans_s;
    
    collect_transfers() @sys.any is {
        
        while TRUE {
            transfer = NULL;       
            m_transfer_out$.get(transfer);
            if not during_transfer then {
                continue;
            };
            
            transfer.slave_name = agent_name;

            var l : list of byte = pack(packing.low, transfer);
            case transfer.size_ctrl {
                0 : {transfer.size = 1};
                1 : {transfer.size = 2};
                2 : {transfer.size = 4};
                3 : {transfer.size = 8};
            };
            

            message(LOW, abstraction_level, 
                    " Slave monitor got transfer " ,
                    transfer,
                    " address : ", transfer.addr,
                    " read_write : ", transfer.read_write,
                    " size : ", transfer.size);
            
            if transfer.read_write == WRITE {
                for each in transfer.data {
                    ram.write_byte(transfer.addr + index, it);
                };
            };
            during_transfer = FALSE;
            
       };
    };

   run() is also {
       during_transfer = FALSE;
       start collect_transfers_full();
       start collect_transfers();
   };

};




extend ACTIVE UVM_ACCEL SLAVE xbus_agent_u {
      
    connect_pointers() is also {      
        // Connect collected transfer, to the BFM so it will respond
        agent_monitor.as_a(UVM_ACCEL SLAVE xbus_agent_monitor_u).ram = ram;
    };
          
    connect_ports() is also {      
        // Connect collected transfer, to the BFM so it will respond
        agent_monitor.as_a(UVM_ACCEL SLAVE xbus_agent_monitor_u).partial_transfer_got_from_hw.connect(bfm.as_a(UVM_ACCEL SLAVE xbus_bfm_u).transfer_started_ip); 
        
       
    };
};


extend UVM_ACCEL MASTER xbus_agent_u {

    connect_ports() is also {              
        // Connect transfer end - for the monitor to use
        agent_monitor.as_a(UVM_ACCEL MASTER xbus_agent_monitor_u).transfer_got_from_hw.connect(get_enclosing_unit(xbus_env_u).bus_monitor.transfer_ended_i);
    };
};

extend UVM_ACCEL xbus_bus_monitor_u {
    ended_write(new_transfer : MONITOR xbus_trans_s ) is first {  
        transfer = new_transfer;
    };
};

'>

UVM_ACCEL arbiter bfm
=====================
TBD
extend UVM_ACCEL ARBITER xbus_bfm_u {
};


UVM_ACCEL bus_collector
=======================

<'

// Dummy data, just getting 
struct hw_address {
    %value : uint (bits : 24);
};
struct hw_grant {
    %value : uint (bits : 16);
};
struct hw_data {
    %value : uint (bits : 72);
};
struct hw_reset {
    %value : uint (bits : 8);
};

extend UVM_ACCEL xbus_bus_collector_u {

    keep hdl_path() == "bus_monitor_bfm";
    
   
    // Output - HW to WW
    
    hw_address_op : uvm_accel_output_pipe_proxy of hw_address is instance;
    // The name of the instance of the transactor output scemi port:
    keep hw_address_op.hdl_path() == "opipe_a"; 

    hw_address_out : out interface_port of tlm_get of hw_address is instance;

    hw_grant_op : uvm_accel_output_pipe_proxy of hw_grant is instance;
    // The name of the instance of the transactor output scemi port:
    keep hw_grant_op.hdl_path() == "opipe_r"; 

    hw_grant_out : out interface_port of tlm_get of hw_grant is instance;
 
    hw_data_op : uvm_accel_output_pipe_proxy of hw_data is instance;
    // The name of the instance of the transactor output scemi port:
    keep hw_data_op.hdl_path() == "opipe_d"; 

    hw_data_out : out interface_port of tlm_get of hw_data is instance;
    
    hw_reset_op : uvm_accel_output_pipe_proxy of hw_reset is instance;
    // The name of the instance of the transactor output scemi port:
    keep hw_reset_op.hdl_path() == "opipe_reset"; 

    hw_reset_out : out interface_port of tlm_get of hw_reset is instance;

    connect_ports() is also {
        hw_address_out.connect(hw_address_op.m_out);
        hw_grant_out.connect(hw_grant_op.m_out);
        hw_data_out.connect(hw_data_op.m_out);
        hw_reset_out.connect(hw_reset_op.m_out);
    };

    collect_input_from_hw() @sys.any is {
       // For now do nothing
    };

   tf_env_setup() @tf_phase_clock is also {
       start collect_input_from_hw();
   };
};

'>


Use only one clock, which is connected to sys.any
=================================================

<'
extend UVM_ACCEL xbus_env_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_bus_monitor_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_bus_collector_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_slave_driver_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_bfm_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_master_driver_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_arbiter_driver_u {
    event tf_phase_clock is only cycle @sys.any;
};
extend UVM_ACCEL xbus_agent_u {
    event tf_phase_clock is only cycle @sys.any;
};


'>


Disconnect ports, connect one central clock to sys.any
======================================================

<'

extend UVM_ACCEL xbus_synchronizer_u {
    connect_ports() is also {
        sig_clock.disconnect();
        do_bind (sig_clock, empty);
        sig_reset.disconnect();
        do_bind (sig_reset, empty);
    };
    
    event never;
    
    // These clocks are not required in acceleration
    event unqualified_clock_rise  is only cycle @never;
    event unqualified_clock_fall  is only cycle @never;
    event reset_change  is only cycle @never;
    event clock_fall    is only cycle @never;
   
    // Envoironment one and only clock. 
    // Ticking only on each context switch from HW
    event clock_rise  is only cycle @sys.any;
}; 



extend UVM_ACCEL xbus_signal_map_u {
    connect_ports() is also {
        sig_start.disconnect();
        do_bind (sig_start, empty);
        sig_addr.disconnect();
        do_bind (sig_addr,  empty);
        sig_addr.disconnect();
        do_bind (sig_addr,  empty);
        sig_size.disconnect();
        do_bind (sig_size,  empty);
        sig_read.disconnect();
        do_bind (sig_read,  empty);
        sig_write.disconnect();
        do_bind (sig_write, empty);
        sig_bip.disconnect();
        do_bind (sig_bip,   empty);
        sig_wait.disconnect();
        do_bind (sig_wait,  empty);
        sig_error.disconnect();
        do_bind (sig_error, empty);
        sig_data.disconnect();
        do_bind (sig_data,  empty);
    };
};



extend UVM_ACCEL xbus_master_signal_map_u {
    connect_ports() is also {
        sig_request.disconnect();
        do_bind(sig_request, empty);
        sig_grant.disconnect();
        do_bind(sig_grant,   empty);    
    };
};
'>

Disable low level activities
============================

<'
extend UVM_ACCEL xbus_bfm_u {
    tf_reset() @tf_phase_clock is only { };

    tf_main_test() @tf_phase_clock is only { };
};


extend UVM_ACCEL xbus_agent_u {
    tf_reset() @tf_phase_clock is only {};
};
'>


End of Test in unclocked model
==============================

<'
extend MAIN POST_TEST xbus_master_sequence {
    keep soft drain_time == 10;
};
'>


