/*-------------------------------------------------------------------------  
File name   : xbus_agent_monitor_h.e
Title       : Agent Monitor Declaration
Project     : XBus UVC
Created     : 2008
Description : This file declares the agent monitor unit.
Notes       : The agent monitor (used in masters and slaves) filters the
            : information collected by the bus monitor to isolate those
            : transfers being handled by a specific agent.
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



-- This unit is the Agent Monitor. The Agent Monitor (used in masters and
-- slaves) filters the information collected by the bus monitor to isolate
-- those transfers being handled by a specific agent.
unit xbus_agent_monitor_u like uvm_monitor {

    -- This field is the logical name of the bus this agent monitor is
    -- monitoring. This field is automatically constrained by the UVC and
    -- should not be constrained by the user.
    bus_name: xbus_bus_name_t;
    
    -- This field is the logical name of the agent this agent monitor is
    -- monitoring. This field is automatically constrained by the UVC and
    -- should not be constrained by the user.
    agent_name : xbus_agent_name_t;

    -- This field holds the abstraction level:
    -- UVM_SIGNAL, UVM_TLM, UVM_ACCEL, UVM_SIGNAL_SC
    abstraction_level : uvm_abstraction_level_t;
      keep soft abstraction_level == UVM_SIGNAL;
    
    -- This field indicates whether this agent monitor for a MASTER, SLAVE or
    -- ARBITER. Note that arbiter monitors don't actually have any
    -- functionality. This field is automatically constrained by the UVC and
    -- should not be constrained by the user.
    kind : xbus_agent_kind_t;

    -- This field is TRUE if the UVC does protocol checking. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    has_checks : bool;
        
    -- If this field is not "" then the agent monitor writes a log file of
    -- that name (with a ".elog" extension). By default, no log file is
    -- written by the agent monitor.
    log_filename : string;
        keep soft log_filename == "";
        
    -- This is the logger used for creating log files. The user should not
    -- normally constrain this field.
    file_logger : message_logger is instance;
        keep file_logger.tags == {XBUS_FILE};
        keep soft file_logger.to_screen == FALSE;
        keep file_logger.to_file == log_filename;
        keep soft file_logger.format == none;
        keep soft file_logger.verbosity == FULL;

    // This port is for getting the collected transfer from the bus monitor
    transfer_ended_i : in interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s is instance;
       keep bind (transfer_ended_i, empty);
    
    write(transfer : MONITOR xbus_trans_s ) is empty;

    -- This method port is the scoreboard hook for the agent monitor. This
    -- method port will be called at the completion of each transfer that
    -- is relevant to the agent monitor. Note that the scoreboard hook is
    -- bound to empty so that no error is issued if the hook is not in use.
    transfer_ended_o : out interface_port of tlm_analysis of
                                          MONITOR xbus_trans_s
                                                            is instance;
        keep bind (transfer_ended_o, empty);

    -- This field counts the number of transfers monitored at this agent
    -- during the test. The user should not alter this field.
    !num_transfers : uint; 
    
}; -- unit xbus_agent_monitor_u

'>


<'
extend MASTER xbus_agent_monitor_u {

    -- This field is a pointer to the synchronizer. This pointer is needed for
    -- protocol checking.
    synch : xbus_synchronizer_u;
    
    -- This is a pointer to the specific signals of the master. This pointer is
    -- needed for protocol checking.
    msmp : xbus_master_signal_map_u;
};
'>

























