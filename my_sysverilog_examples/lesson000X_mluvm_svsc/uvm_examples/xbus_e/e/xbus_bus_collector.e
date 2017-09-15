
/*------------------------------------------------------------------------- 
File name   : xbus_bus_collector.e
Title       : Bus monitor implementation
Project     : XBus UVC
Created     : 2008
Description : This file contains the bus collector unit implementation
Notes       : The bus collector collects all activity on the bus and collects
            : information on each transfer that occurs.
            : It passes the collected info, after basic processing, to the
            : monitor.
            : The monitor performs higher level process, coverage and checks 
--------------------------------------------------------------------------- 
//----------------------------------------------------------------------
//   Copyright 2008-2010 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------
-------------------------------------------------------------------------*/ 

<'
package cdn_xbus;

import xbus_bus_collector_h.e;
'>


=====================================
          Collector
=====================================

<'
extend xbus_bus_collector_u {
    -- The collected transfer is built up in this field.
    package !transfer : MONITOR xbus_trans_s;
  
    current_master_name : xbus_agent_name_t;
       keep soft current_master_name == NO_AGENT;
    current_slave_name  : xbus_agent_name_t;
       keep soft current_slave_name == NO_AGENT;

    -- This event is emitted by the monitor at the end of a transfer after
    -- it has finished filling in all the fields of the transfer field
    event transfer_end; 
    
    -- This event is the rising edge of the START signal.
    event start_rise is only
        rise(smp.sig_start$) @synch.clock_rise;
        
    -- This event is the falling edge of the START signal.
    event start_fall is only
        fall(smp.sig_start$) @synch.clock_rise;

    -- This event is emitted at the rising edge of clock at the end of each
    -- Arbitration Phase.
    event arbitration_phase is only
        {@synch.reset_end or @nop_cycle or @data_end; [1]} @synch.clock_rise;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- Address Phase.
    event address_phase is only
        {@start_rise; [1]} @synch.clock_rise;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- NOP Address Phase.
    event nop_cycle is only
        true((smp.sig_read$ == 0) and (smp.sig_write$ ==0)) @address_phase;
    
    
    
    event read_normal_address_phase is
      true(smp.sig_read$ == 1 and !smp.sig_read.has_z()) @address_phase;
    event write_normal_address_phase is
      true(smp.sig_write$ == 1 and !smp.sig_write.has_z()) @address_phase;
  
    -- This event is emitted at the rising edge of clock at the end of each
    -- non-NOP Address Phase
    event normal_address_phase is only (@read_normal_address_phase or 
                                        @write_normal_address_phase)  @address_phase;
    
    -- This event is emitted at the rising edge of clock at the end of the
    -- first cycle of Data Phase.
    event data_start is only
        {@normal_address_phase; [1]} @synch.clock_rise;
    
    -- This event is emitted at the rising edge of clock at the end of the
    -- last cycle of the Data Phase. This event signifies that a transfer
    -- (not a NOP) has completed. At this stage the transfer field contains
    -- a record of the transfer that occurred.
    event data_end is only
        {@normal_address_phase; [..]; 
         true((smp.sig_error$ == 1) or 
              (smp.sig_bip$ == 0 and smp.sig_wait$ == 0 ))
        } @synch.clock_rise;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- cycle of Data Phase.
    event data_phase is only
        ({(@data_start and not @data_end); ~[..] * not @data_end} or 
         @data_end) @synch.clock_rise;
    
    -- This event is emitted each time a wait state is inserted on the bus.
    event wait_state is only
        true(smp.sig_wait$ == 1) @data_phase;
    
    -- This event is emitted each time a byte of data is valid on the bus.
    event data_valid is only
        true(smp.sig_wait$ == 0) @data_phase; 
    
    -- This event is emitted each time the Data Phase is terminated by an
    -- error.
    event data_error is only
        true(smp.sig_error$ == 1) @data_phase;
    
    -- This event is emitted each time a single byte transfer occurs in the
    -- Address Phase.
    event single_data is only
        true(smp.sig_size$ == 0) @normal_address_phase;   

    -- Collect information at the end of each arbitration phase.
    on arbitration_phase {
        monitor_arbitration_phase();
    };
    
    -- This method determines which master (if any) won the Arbitration Phase.
    private monitor_arbitration_phase() is {
        for each (msmp) in msmps {
            if (msmp.sig_grant$ == 1) {
                current_master_name = msmp.master.agent_name;
                break;
            };
        };
    }; -- monitor_arbitration_phase()
    
    -- Collect information at the end of each normal (i.e. not a NOP) address
    -- phase.
    on normal_address_phase {
        monitor_address_phase();
    };
    
    -- This method creates a transfer instance and fills in the Address
    -- Phase fields. This method also determines which slave should 
    -- respond to the transfer.
    private monitor_address_phase() is {

        -- create a new instance of a MONITOR xbus_tran_s;
        transfer = new MONITOR xbus_trans_s with { 
            it.addr = smp.sig_addr$;
            it.size = smp.get_size();
            it.read_write = smp.get_read_write();
            it.master_name = current_master_name;
        };
        transfer.waits.add(0);
        msg_started(HIGH, "Bus Collecting transfer", transfer);
        transfer_started_o$.write(transfer);
    }; -- monitor_address_phase()    
    
    -- Count any wait states that get inserted.
    on wait_state {
        monitor_wait_state();
    };
    
    -- This method increments the wait state counter for the current data
    -- byte of the transfer. Note that we are guaranteed that the waits list
    -- in the transfer has at least one item on it because the
    -- monitor_address_phase() method creates the first item in this list and
    -- the wait_state event cannot be emitted unless the normal_address_phase
    -- event has first been emitted.
    private monitor_wait_state() is {
        transfer.waits.push(transfer.waits.pop() +1);
    }; -- monitor_wait_state()
    
    -- Collect each data byte during the transfer.
    on data_valid {
        monitor_data_byte();
    };
    
    -- This method captures a single data byte of the transfer and
    -- adds it to the data field of transfer.
    private monitor_data_byte() is {
        transfer.data.add(smp.sig_data$);
        if (smp.sig_error$ ==1) {
            transfer.error_pos_mon = transfer.data.size();
        } else {
            transfer.error_pos_mon = 0;
        };
        if (transfer.data.size() == transfer.size) or
           (transfer.error_pos_mon > 0) {
            // Export to higher leyer component
            msg_ended(HIGH, "Bus Collecting transfer", transfer);
            transfer_ended_o$.write(transfer);
        } else {
            transfer.waits.add(0);
        };
    }; -- monitor_data_byte()
    
    
};
'>

























