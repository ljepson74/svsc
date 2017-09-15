/*-------------------------------------------------------------------------  
File name   : xbus_bus_monitor_h.e
Title       : Bus monitor declaration
Project     : XBus UVC
Created     : 2008
Description : This file declares the bus monitor unit.
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
'>


===================================
           Monitor
===================================

<'
-- This unit is the Bus Monitor. The Bus Monitor gets the information from 
-- the collector, performs coverage and checks, and export information to
-- other components via ports.
unit xbus_bus_monitor_u like uvm_monitor {
    
    -- This field holds the abstraction level:
    -- UVM_SIGNAL, UVM_TLM, UVM_ACCEL, UVM_SIGNAL_SC
    abstraction_level : uvm_abstraction_level_t;
      keep soft abstraction_level == UVM_SIGNAL;

    collector : xbus_bus_collector_u is instance;
      keep collector.has_checks == value(has_checks);
    
    // Belong to the XBUS_TF TestFlow domain
    tf_testflow_unit;
    keep soft tf_domain == XBUS_TF;
    event tf_phase_clock is only @synch.unqualified_clock_rise;
    
    -- This field holds the logical name of the bus containing this bus
    -- monitor. This field is automatically constrained by the UVC and should
    -- not be constrained by the user.
    bus_name : xbus_bus_name_t;
       keep collector.bus_name == value(bus_name);
    
    -- This field is a pointer to the synchronizer.
    synch : xbus_synchronizer_u;
       keep collector.synch == value(synch);
    
    -- This is a list of pointers to the slave configuration units.
    slave_configs : list of xbus_slave_config_u;

    -- If this field is TRUE then the bus monitor performs protocol checking.
    -- This field is normally controlled by the main field of the same
    -- name in the env, but the user can override this for the bus monitor.
    has_checks : bool;

    -- If this field is not "" then the bus monitor writes a log file of that
    -- name (with a ".elog" extension). By default, the filename is
    -- "xbus.elog".
    log_filename : string;
        keep soft log_filename == "xbus";

    -- This is the logger used for creating bus log files. The user should not
    -- normally constrain this field.
    file_logger : message_logger is instance;
        keep file_logger.tags == {XBUS_FILE};
        keep soft file_logger.to_screen == FALSE;
        keep file_logger.to_file == log_filename;
        keep soft file_logger.format == none;
        keep soft file_logger.verbosity == FULL;
        
    
    
    -- This field is used to count the total number of transfers monitored
    -- during the test.
    !num_transfers : uint;

    // These ports get the collected transfer from the collector
    transfer_started_i : in interface_port of tlm_analysis
                                         of MONITOR xbus_trans_s
                                         using prefix=started_
                                         is instance;
       keep bind (transfer_started_i, collector.transfer_started_o);
    transfer_ended_i : in interface_port of tlm_analysis
                                         of MONITOR xbus_trans_s
                                         using prefix=ended_
                                         is instance;
       keep bind (transfer_ended_i, collector.transfer_ended_o);
    
    started_write(new_transfer : MONITOR xbus_trans_s ) is {};
    ended_write(new_transfer : MONITOR xbus_trans_s ) is {};

    -- This method port is the scoreboard hook for the bus monitor. This
    -- method port will be called at the completion of each transfer on the
    -- bus. Note that the scoreboard hook is bound to empty so that no error
    -- is issued if the hook is not in use.
    transfer_ended_o : out interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s 
                                          is instance;
        keep bind (transfer_ended_o, empty);

}; -- unit xbus_bus_monitor_u

'>




















