/*------------------------------------------------------------------------- 
File name   : test_tba.e
Title       : XBus eVC demo - example testcase file
Project     : XBus eVC
Created     : 2008
Description : Example testcase file for demo purposes.
            : 
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
import xbus_e/examples/xbus_arbiter_dut_tba_config.e;




-- Make sure masters expect errors as described above.
extend MASTER xbus_trans_s {
    keep read_only(size > 4) =>  error_pos_master == 4;
};


extend MASTER_0 MAIN xbus_master_sequence {
     body() @driver.clock is only {
         // do nothing
     };
};

extend MASTER_0 MAIN ENV_SETUP xbus_master_sequence {
    
    body() @driver.clock is only {
        // Generate one transfer
        gen trans keeping {it.driver == driver; it.size == 4};


        for i from 0 to 20 {
            // Use the same transfer, just change read/write, and address
            trans.read_write = WRITE;
            trans.addr = 0x0000 + 4 + i;
            for i from 0 to trans.size-1 {
                trans.data[i] = 100 + i;
            };
            driver.queue_item(me, deep_copy(trans));
            trans.read_write = READ;
            trans.addr = 0x0000 + 4 + i;
            driver.queue_item(me, deep_copy(trans));             
        };    
    };
};


extend MAIN POST_TEST xbus_master_sequence {
    keep drain_time == 40;
};


extend MASTER xbus_trans_s {
    keep for each in wait_states  {
        soft it == 0;
    };
}; 

// For self checking - see what the monitor saw

extend xbus_bus_monitor_u {
    on transfer_end {
        message(LOW, "Got transfer ", transfer.data);
    };
};

extend MAIN xbus_slave_sequence {
    keep count == 0;
    body() @driver.clock is only {
        // Don't
    };
};


'>

