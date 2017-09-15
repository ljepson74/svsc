/*------------------------------------------------------------------------- 
File name   : xbus_agent_monitor.e
Title       : Agent Monitor implementation
Project     : XBus UVC
Created     : 2008
Description : This file implements the agent monitor unit.
Notes       : 
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



extend xbus_agent_monitor_u {

    -- This field is a pointer to the bus monitor. Note that this is set
    -- procedurally using connect_pointers().
    !bus_monitor : xbus_bus_monitor_u;
    

    -- This method writes a header for use at the top of log files.
    private write_log_header() is {
        -- Write date and time, filename etc. along with field headings
        message(XBUS_FILE, LOW, 
                append(append(file_logger.to_file, ".elog"), 
                       " - created ", date_time()));
        message(XBUS_FILE, LOW, "");
        message(XBUS_FILE, LOW,
                "    TIME    AGENT       ADDRESS SIZE R/W   DATA WAITS STATUS");
        message(XBUS_FILE, LOW,
                "    ****    *****       ******* **** ***   **** ***** ******");
        message(XBUS_FILE, LOW, "");
    }; -- write_log_header()
    
    -- This field is used to ensure that the log file header is not rewritten
    -- if reset is reapplied during the test.
    private !log_header_written : bool;
    
    -- If this is the beginning of the test, write a file log header. The
    -- log_header_written field is used to prevent the log header being
    -- written again if rerun() is called.
    run() is also {
        if not log_header_written {
            write_log_header();
            log_header_written = TRUE;
        };
    }; -- run()
    
    -- This method reports the current status of the agent monitor.
    show_status() is {
        if kind != ARBITER {
            message(LOW, "Agent monitor detected ", dec(num_transfers), 
                    " transfers");
        };
    }; -- show_status()
    
    -- This event emitted when this agent monitor detects a
    -- transfer that is relevant to it.
    event agent_trans_end;
    
    // Implement the in port 
    write(new_transfer : MONITOR xbus_trans_s) is {  
        if (new_transfer.slave_name == agent_name or 
            new_transfer.master_name == agent_name) {
            emit agent_trans_end;
            transfer_ended_o$.write(new_transfer); 
            num_transfers += 1;
            msg_ended(MEDIUM, "Monitoring transfer", new_transfer);
            message(XBUS_FILE, MEDIUM, 
                    new_transfer.log_transfer(appendf("%8d    %-11.11s ",
                                                      sys.time, 
                                                      agent_name)));
        };
    }; -- transfer_ended_i()

}; -- extend xbus_agent_monitor_u


'>





























