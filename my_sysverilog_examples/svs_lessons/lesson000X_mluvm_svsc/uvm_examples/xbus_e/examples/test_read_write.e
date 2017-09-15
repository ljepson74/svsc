/*------------------------------------------------------------------------- 
File name   : test_read_write.e
Title       : XBus eVC demo - example testcase file
Project     : XBus eVC
Created     : 2008
Description : This file demonstrates the read() and write() sequence
            : methods.
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

-- import the eVC configuration file (which in turn imports the XBus eVC)
import xbus_e/examples/xbus_config;
import xbus_e/e/xbus_basic_seq_lib;

extend sys {

    setup() is also {
        -- Print in hexadecimal by default
        set_config(print, radix, hex);
    };
    
}; -- extend sys

-- Create a sequence for MASTER_0
-- direct calls of write()/read() TCMS
extend MASTER_0 MAIN MAIN_TEST xbus_master_sequence {
    body() @driver.clock is only {
        var data : uint(bits:64);
        var i    : uint = 0;
        
        data = 0x1122334455667788;
        write(8, 0x1000 + i * 64, data);
        message(LOW, "WRITE DATA = ", data);
        data = read(8, 0x1000 + i * 64);
        message(LOW, "READ DATA = ", data);
        
        i = 1;
        data = 0xaabbccdd;
        write(4, 0x1000 + i * 64, data);
        message(LOW, "WRITE DATA = ", data);
        data = read(8, 0x1000 + i * 64);
        message(LOW, "READ DATA = ", data);
        
        i = 2;
        data = 0x11;
        write(1, 0x1000 + i * 64, data);
        message(LOW, "WRITE DATA = ", data);
        data = read(8, 0x1000 + i * 64);
        message(LOW, "READ DATA = ", data);
        
        i = 3;
        data = 0x4422886611335577;
        write(8, 0x1000 + i * 64, data);
        message(LOW, "WRITE DATA = ", data);
        data = read(8, 0x1000 + i * 64);
        message(LOW, "READ DATA = ", data);
        
    };   
};

-- Create a sequence for MASTER_1
-- using the WRITE_TRANSFER/READ_TRANSFER sequences
extend MASTER_1 MAIN MAIN_TEST xbus_master_sequence {
    !wr_seq : WRITE_TRANSFER xbus_master_sequence;
    !rd_seq : READ_TRANSFER xbus_master_sequence;
    
    body() @driver.clock is only {
        var data : uint(bits:64);
        var addr : uint(bits:64);
        
        for i from 0 to 3 {
            gen addr keeping {it in [0x2000..0x3000]};
            gen data;
            
            do wr_seq keeping {
                .base_addr == addr;
                .data == data;
                .size == 1 << i;
            };
            message(LOW, "WRITE DATA = ", data);
            do rd_seq keeping {
                .base_addr == addr;
                .size == 1 << i;
            };
            message(LOW, "READ DATA = ", rd_seq.data);
        };
    };
};




'>

<'

'>
