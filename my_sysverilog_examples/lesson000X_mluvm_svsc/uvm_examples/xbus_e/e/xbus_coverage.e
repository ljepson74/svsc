/*-------------------------------------------------------------------------  
File name   : xbus_coverage.e
Title       : Coverage
Project     : XBus UVC
Created     : 2008
Description : This file provides functional coverage in the bus and agent
            : monitors.
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



-- The following code collects coverage for all transfers per bus.
extend xbus_bus_monitor_u {
    cover transfer_end is {
        item addr : uint(bits:16) = transfer.addr;
        item read_write :xbus_read_write_t = transfer.read_write 
            using ignore = (read_write == NOP);
        item size : uint [1, 2, 4, 8] = transfer.size;
    };
}; -- extend_xbus_bus_monitor_u



-- The following code collects coverage for transfers on a per agent basis.
extend xbus_agent_monitor_u {
    cover agent_trans_end is {
        item name : xbus_agent_name_t = agent.agent_name
            using per_instance;
        item addr : uint(bits:16) = bus_monitor.transfer.addr;
        item read_write :xbus_read_write_t = bus_monitor.transfer.read_write 
            using ignore = (read_write == NOP);
        item size : uint [1, 2, 4, 8] = bus_monitor.transfer.size;
    };
}; -- extend xbus_agent_monitor_u



-- The following code ensures that coverage data for transfers is only shown
-- for each agent instance and not for the combination of all agents.
extend sys {
    finalize() is also {
        set_cover("xbus_agent_monitor_u.agent_trans_end(per_type).*", FALSE);
    };
}; -- extend sys

'>

