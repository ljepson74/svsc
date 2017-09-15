/*------------------------------------------------------------------------- 
File name   : test_multi_reset.e
Title       : XBus eVC demo - example of multiple reset handling
Project     : XBus eVC
Created     : 2008
Description : Example testcase file for demo purposes
Notes       : This file demonstrates the ability of the eVC to cope with
            : multiple resets. Master_0 perform 6 resets 
            :
            : For seeing messages from the Testflow utilitiy (note - there 
            : are many of them) issue  in Specman prompt:
            :     trace testflow
-------------------------------------------------------------------------*/ 
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

-- import the eVC configuration file (which in turn imports the XBus eVC)
import xbus_e/examples/xbus_config;


-- All masters will do between 20 and 30 transfers
extend MAIN MAIN_TEST xbus_master_sequence {
    keep count in [20..30];
}; -- extend MAIN MAIN_TEST xbus_master_sequence

-- Issue an extra reset half way through the test
extend xbus_master_driver_u {
    do_extra_reset() @sys.any is {
        if tf_get_domain_mgr().get_invocation_count(MAIN_TEST) < 6 
                                                                  then {
            var delay : uint;
            gen delay keeping {it in [1..200]};
            wait [delay];
            message(LOW, "Calling rerun_phase(RESET)");
            tf_get_domain_mgr().rerun_phase(RESET);
        };
    }; -- do_extra_reset()
    
    tf_main_test() @tf_phase_clock is also {
        do_extra_reset();
    }; -- tf_main_test()

    init() is also {
        specman("set check IGNORE");
    };
}; -- extend sys

'>

