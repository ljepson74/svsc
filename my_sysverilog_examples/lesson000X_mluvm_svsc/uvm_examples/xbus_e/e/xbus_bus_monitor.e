/*------------------------------------------------------------------------- 
File name   : xbus_bus_monitor.e
Title       : Bus monitor implementation
Project     : XBus UVC
Created     : 2008
Description : This file contains the bus monitor unit implementation
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



-- This code adds fields and methods to the transfer struct for use by the
-- monitor to collect and log extra information.
extend MONITOR xbus_trans_s {

    -- This method returns the string value of a byte of data or "XX" if
    -- the data is invalid. It is used for writing log files.
    private log_data_byte(read : bool, d : byte, err : bool) : string is {
        if err and read {
            result = "XX";
        } else {
            result = appendf("%02x", d);
        };
    }; -- log_data_byte()
    
    -- This method returns a string representation of the data, wait states
    -- and error condition of a transfer.
    private log_data(read : bool, data : uint, waits : uint, err : bool) : 
                                                                    string is {
        result = appendf("%s   %-6d", log_data_byte(read,data, err), waits);
        if err {
            result = append(result, "ERROR");
        } else {
            result = append(result, "OK");
        };
    }; -- log_data()
    
    -- This method returns a log file entry for this transfer. The first
    -- line of the entry is indented with the string specified in the
    -- 'leader' parameter. Subsequent lines are indented to line up with
    -- the first line.
    package log_transfer(leader : string) : string is {
        for i from 1 to size {
            if i == 1 {
                result = appendf("%s%04x    %-5d%-6s", leader,
                                 addr, size, read_write);
            } else {
                result = appendf("%s\n%s", result, 
                                 str_pad("", str_len(leader)+19));
            };
            result = appendf("%s%s", result, 
                             log_data(read_write == READ,
                                      data[i-1], 
                                      waits[i-1], 
                                      i == error_pos_mon));
            if i == error_pos_mon {
                break;
            };
        };
    }; -- log_transfer()

}; -- extend MONITOR xbus_trans_s

'>



=====================================
          Monitor
=====================================

<'
extend xbus_bus_monitor_u {

    keep soft collector.abstraction_level == read_only(abstraction_level);

    -- The monitored transfer is built up in this field.
    package !transfer : MONITOR xbus_trans_s;

    -- This event is emitted by the monitor at the end of a transfer after
    -- it has finished filling in all the fields of the transfer field
    event transfer_end;  

    
    -- This method writes a header for use at the top of the bus log file.
    private write_log_header() is {
        -- Write date and time, filename etc. along with field headings
        message(XBUS_FILE, LOW, 
                append(append(file_logger.to_file, ".elog"), 
                       " - created ", date_time()));
        message(XBUS_FILE, LOW, "");
        message(XBUS_FILE, LOW,
                "    TIME    MASTER      SLAVE       ",
                "ADDRESS SIZE R/W   DATA WAITS STATUS");
        message(XBUS_FILE, LOW,
                "    ****    ******      *****      ",
                "******* **** ***   **** ***** ******");
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
        message(LOW, "Bus monitor started");
    }; -- run()

    -- Implement the in ports
    started_write(new_transfer : MONITOR xbus_trans_s ) is also {  
        transfer = new_transfer;
        msg_started(MEDIUM, "Bus Monitoring transfer", transfer);
    };
    
    ended_write(new_transfer : MONITOR xbus_trans_s ) is also {  
        num_transfers += 1;
        emit transfer_end;
        -- determine which slave is responsible for this transfer.
        transfer.slave_name = find_slave_of_addr(transfer.addr);
        
        message(HIGH, "bus_monitor got transfer ", num_transfers,
                " ", transfer);
        
        msg_ended(MEDIUM, "Bus Monitoring transfer", transfer);
        
        -- Ensure that each transfer is written to the log file.
        message(XBUS_FILE, MEDIUM,
                transfer.log_transfer(appendf("%8d    %-11.11s %-11.11s ", 
                    sys.time, transfer.master_name, transfer.slave_name)));

        transfer_ended_o$.write(transfer);
    }; -- transfer_ended_i
    
    -- This method returns the current status of the bus monitor.
    show_status() is {
        message(LOW, "Bus monitor detected ", dec(num_transfers), 
                " transfers");
    }; -- show_status()
    
    -- This method determines which slave is responsible for this address.
    find_slave_of_addr(addr : xbus_addr_t) : xbus_agent_name_t is {
        for each (config) in slave_configs {
            if config.in_range(addr) {
                result = config.slave.agent_name;
                break;
            };
        };
        
    };
}; -- extend xbus_bus_monitor_u

'>


