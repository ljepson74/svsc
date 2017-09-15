/*------------------------------------------------------------------------- 
File name   : xbus_master_agent.e
Title       : XBus Master Agent
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


-- The following code adds fields to the MASTER agent that define the
-- arbitration signals.
extend MASTER xbus_agent_u {

    -- This is the instance of the master signal map.
    msmp : xbus_master_signal_map_u is instance;
        keep soft msmp.abstraction_level == read_only(abstraction_level);
        keep msmp.bus_name == read_only(bus_name);
        keep msmp.master_name == read_only(agent_name);
        keep msmp.master == read_only(me);


    keep agent_monitor is a MASTER xbus_agent_monitor_u (mam) =>
        mam.synch == read_only(synch) and
        mam.msmp == read_only(msmp);
    
}; -- extend MASTER xbus_agent_u



extend ACTIVE MASTER xbus_agent_u {
    
    
    // testflow main methods are expected to be found in the top portion of the
    // unit to better recognize the functional behavior of the unit
    tf_reset() @tf_phase_clock is also {
        reset_dut();
    };
    
    reset_dut() @synch.unqualified_clock_rise is {
        message(TESTFLOW_EX, LOW, "reset start");
        synch.sig_reset$ = 1;
        wait[5];
        synch.sig_reset$ = 0;
        message(TESTFLOW_EX, LOW, "reset done");
    };
    

    -- This is the sequence driver for an ACTIVE MASTER agent.
    driver: xbus_master_driver_u is instance;
        keep soft driver.abstraction_level == read_only(abstraction_level);
        keep driver.bus_name == read_only(bus_name);
        keep driver.master_name == read_only(agent_name);
        keep driver.synch == read_only(synch);

    -- This is the BFM for an ACTIVE MASTER agent.
    bfm : MASTER xbus_bfm_u is instance;
        keep soft bfm.abstraction_level == read_only(abstraction_level);
        keep bfm.driver == read_only(driver);
        keep bfm.synch == read_only(synch);
        keep bfm.smp == read_only(smp);
        keep bfm.msmp == read_only(msmp);

}; -- extend ACTIVE MASTER xbus_agent_u

'>
