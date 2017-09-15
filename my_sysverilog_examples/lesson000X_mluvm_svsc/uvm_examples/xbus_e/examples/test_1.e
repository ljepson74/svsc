/*------------------------------------------------------------------------- 
File name   : test_1.e
Title       : XBus eVC demo - example testcase file
Project     : XBus eVC
Created     : 2008
Description : Example testcase file for demo purposes.
            : Master0 sends 10..12 transfers
            : Master1 sends 1..5 transfers
            : The slaves respond with error for every transfer longer than 4
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

-- import the eVC configuration file (which in turn imports the XBus eVC)
import xbus_e/examples/xbus_config;


-- SLAVE_0 responds to all transfers > 4 bytes long with an error in byte
-- position 4.
extend xbus_slave_response_s {
    keep read_only(transfer.size > 4) => error_pos == 4;
}; 

-- Make sure masters expect errors as described above.
extend MASTER xbus_trans_s {
    
    keep read_only(size > 4) =>  error_pos_master == 4;
    
};


extend MASTER_0 MAIN MAIN_TEST xbus_master_sequence {
    keep count in [10..12];
};

extend MASTER_1 MAIN MAIN_TEST xbus_master_sequence {
    keep count in [1..5];
};


'>



<'
extend xbus_bus_monitor_u {
    on transfer_end {
        message(LOW, "bus_monitor saw transfer sent from ",
                transfer.master_name, 
                " of length ", transfer.data.size(), 
                transfer.error_pos_mon == 0 ? "" : " and Error raised"); 
    };
};
'>


