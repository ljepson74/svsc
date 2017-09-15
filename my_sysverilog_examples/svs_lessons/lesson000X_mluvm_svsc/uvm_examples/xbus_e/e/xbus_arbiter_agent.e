/*------------------------------------------------------------------------- 
File name   : xbus_slave_agent.e
Title       : XBus Slave Agent
Project     : UVM XBus UVC
Developers  :  
Created     : 2008
Description : 
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

extend ACTIVE ARBITER xbus_agent_u {

    -- This is the sequence driver for an ACTIVE ARBITER agent.
    driver: xbus_arbiter_driver_u is instance;
        keep soft driver.abstraction_level == read_only(abstraction_level);
        keep driver.synch == read_only(synch);
        keep driver.bus_name == read_only(bus_name);
        keep driver.arbiter_name == read_only(agent_name);

    -- This is the BFM for an ACTIVE ARBITER agent.
    bfm : ARBITER xbus_bfm_u is instance;
        keep soft bfm.abstraction_level == read_only(abstraction_level);
        keep bfm.driver == read_only(driver);
        keep bfm.synch == read_only(synch);
        keep bfm.smp == read_only(smp);

}; -- extend ACTIVE ARBITER xbus_agent_u

'>
