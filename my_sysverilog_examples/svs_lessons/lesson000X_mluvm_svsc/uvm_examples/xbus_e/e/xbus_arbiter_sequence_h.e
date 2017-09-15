/*------------------------------------------------------------------------- 
File name   : xbus_arbiter_sequence.e
Title       : Sequence interface for ACTIVE arbiter agents
Project     : XBus UVC
Created     : 2008
Description : This file provides a sequence interface for the arbiter. By
            : default, this sequence driver will take a random decision for
            : each arbitration phase. However, the user can over-ride the
            : default behaviour to control specific arbitration decisions.
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



-- This struct is used as the sequence item for arbiter sequences
struct xbus_arbiter_decision_s like any_sequence_item {

    -- This field holds the logical name of the physical bus. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    bus_name : xbus_bus_name_t;
        keep bus_name == read_only(driver.bus_name);    
   
    -- This field is used to sub-type the decision struct according to which
    -- arbiter agent it is for. This field is automatically constrained by the
    -- UVC and should not be constrained by the user.
    arbiter_name : xbus_agent_name_t;
        keep arbiter_name == read_only(driver.arbiter_name);
    
    -- This field contains the list of masters that are requesting the bus.
    -- This field is automatically constrained by the UVC and should not be
    -- constrained or altered by the user.
    requests : list of MASTER xbus_agent_u;
        keep requests == read_only(driver.requests);

    -- This field contains the decision on which of the requesting masters
    -- should be granted the bus. This must be one of the masters in
    -- mentioned in the requests field or NULL.
    granted_master : MASTER xbus_agent_u;
        keep read_only(requests).is_empty() => granted_master == NULL;
        keep not read_only(requests).is_empty() => 
                                      granted_master in read_only(requests);
    
}; -- struct xbus_arbiter_decision_s



-- This struct is the generic sequence for the arbiter agent sequence
-- interface.
sequence xbus_arbiter_sequence using
    testflow = TRUE,
    item = xbus_arbiter_decision_s,
    created_driver = xbus_arbiter_driver_u;



extend xbus_arbiter_sequence {

    -- This field holds the logical name of the physical bus. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    bus_name : xbus_bus_name_t;
        keep bus_name == read_only(driver.bus_name);    
   
    -- This field holds the logical name of the arbiter. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    arbiter_name : xbus_agent_name_t;
        keep arbiter_name == read_only(driver.arbiter_name);

    -- This is a utility field for basic sequences. This allows the user to
    -- do "do decision ...".
    !decision : xbus_arbiter_decision_s;

    // Cover the sequence. 
    // Ignore the pre-defined kinds, they do not add info to the coverage
    cover ended is {
        item kind using ignore = (kind == RANDOM or
                                  kind == SIMPLE or
                                  kind == MAIN);
    }; 
}; -- extend xbus_arbiter_sequence


// since arbitration should begin immediately after reset this sequence is 
// an init_dut phase seq and not main_test seq
extend MAIN INIT_DUT xbus_arbiter_sequence {
    
    -- The arbiter sequence driver is a reactive sequence driver so, by
    -- default we don't want it to ever run out of sequence items.
    keep soft count == MAX_UINT;
      
    body() @driver.clock is only {
        for i from 0 to MAX_UINT {
            do decision;
        };
    };
}; -- extend MAIN xbus_arbiter_sequence



-- The following code hooks up the sequence driver to the arbiter BFM.
extend xbus_arbiter_driver_u {

    keep soft tf_domain == XBUS_TF;

    -- This field holds the abstraction level:
    -- UVM_SIGNAL, UVM_TLM, UVM_ACCEL, UVM_SIGNAL_SC
    abstraction_level : uvm_abstraction_level_t;
      keep soft abstraction_level == UVM_SIGNAL;

    synch : xbus_synchronizer_u;

    // tf_phase_clock if the testflow clock and might change according to
    // current test phase. it is recommended to bind driver.clock to this 
    // clock;
    event tf_phase_clock is only @synch.unqualified_clock_fall;
    on tf_phase_clock {
        emit clock;
    };
    
    // sequences are influenced by test phases but do not influence
    // the test flow (usually they use while TRUE loops) this behavior is
    // declared by this flag
    keep tf_nonblocking == TRUE;

    -- This field holds the logical name of the physical bus. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    bus_name : xbus_bus_name_t;
   
    -- This field holds the logical name of the arbiter. This field is
    -- automatically constrained by the UVC and should not be constrained by
    -- the user.
    arbiter_name : xbus_agent_name_t;

    -- This field is where the arbiter BFM puts the list of masters that are
    -- currently requesting the bus immediately prior to calling
    -- try_next_item().
    package !requests : list of MASTER xbus_agent_u;
    
}; -- extend xbus_arbiter_driver_u




'>

