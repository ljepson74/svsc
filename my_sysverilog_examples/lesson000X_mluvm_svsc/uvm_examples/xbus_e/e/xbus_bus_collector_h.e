/*-------------------------------------------------------------------------  
File name   : xbus_bus_collector_h.e
Title       : Bus collector declaration
Project     : XBus UVC
Created     : 2009
Description : This file declares the bus colelctor unit.
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



-- This code creates a sub-type of the transfer struct that is used for
-- collecting monitor information.
extend xbus_trans_kind_t : [MONITOR];



-- This code provides a message tag that can be used to direct certain message
-- actions to a log file.
extend message_tag: [XBUS_FILE];



-- This code adds fields and methods to the transfer struct for use by the
-- monitor to collect and log extra information.
extend MONITOR xbus_trans_s {

    -- This field is used by the monitor to collect the actual number of waits
    -- states for each byte of the transfer.
    !waits : list of uint;
    
    -- This field is used by the monitor to log the position of any error. A
    -- 0 value means no error occurred.
    !error_pos_mon : uint;

}; -- extend MONITOR xbus_trans_s
            
'>


===================================
           Collector
===================================

<'
-- This unit is the Bus Collector. The Bus Monitor monitors all activity on the
-- bus and collects information on each transfer that occurs.
unit xbus_bus_collector_u like uvm_collector {
    
    -- This field holds the logical name of the bus containing this bus
    -- monitor. This field is automatically constrained by the UVC and should
    -- not be constrained by the user.
    bus_name : xbus_bus_name_t;

    // Belong to the XBUS_TF TestFlow domain
    tf_testflow_unit;
    keep soft tf_domain == XBUS_TF;
    event tf_phase_clock is only @synch.unqualified_clock_rise;

    -- This field holds the abstraction level:
    -- UVM_SIGNAL, UVM_TLM, UVM_ACCEL, UVM_SIGNAL_SC
    abstraction_level : uvm_abstraction_level_t;
      keep soft abstraction_level == UVM_SIGNAL;

    -- If this field is TRUE then the bus collector performs protocol checking.
    -- This field is normally controlled by the main field of the same
    -- name in the env, but the user can override this for the bus monitor.
    has_checks : bool;

    -- This field is a pointer to the synchronizer.
    synch : xbus_synchronizer_u;
    
    -- This field is a pointer to the bus signal map.
    smp : xbus_signal_map_u;

    -- This is a list of pointers to the master signal maps.
    msmps : list of xbus_master_signal_map_u;

    -- Events
    
    -- This event is the rising edge of the START signal.
    event start_rise;
        
    -- This event is the falling edge of the START signal.
    event start_fall;

    -- This event is emitted at the rising edge of clock at the end of each
    -- Arbitration Phase.
    event arbitration_phase;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- Address Phase.
    event address_phase;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- NOP Address Phase.
    event nop_cycle;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- non-NOP Address Phase
    event normal_address_phase;
    
    -- This event is emitted at the rising edge of clock at the end of the
    -- first cycle of Data Phase.
    event data_start;
    

    -- This event is emitted at the rising edge of clock at the end of the
    -- last cycle of the Data Phase. This event signifies that a transfer
    -- (not a NOP) has completed. At this stage the transfer field contains
    -- a record of the transfer that occurred.
    event data_end;
    
    -- This event is emitted at the rising edge of clock at the end of each
    -- cycle of Data Phase.
    event data_phase;
    
    -- This event is emitted each time a wait state is inserted on the bus.
    event wait_state;
    
    -- This event is emitted each time a byte of data is valid on the bus.
    event data_valid;
    
    -- This event is emitted each time the Data Phase is terminated by an
    -- error.
    event data_error;
    
    -- This event is emitted each time a single byte transfer occurs in the
    -- Address Phase.
    event single_data;

    // These ports are for exporting the collected transfer
    transfer_started_o : out interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s is instance;
    transfer_ended_o : out interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s is instance;
};
'>


