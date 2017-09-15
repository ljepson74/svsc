/*------------------------------------------------------------------------- 
File name   : test_reconfiguration.e
Title       : XBus eVC demo - example of multiple reset handling
Project     : XBus eVC
Created     : 2008
Description : Example testcase file for demo purposes
Notes       : This file demonstrates the ability of the eVC to cope with
            : multiple configurations. 
            :  
            : Call xbus_env configure method several times, each time
            : with different set of parameters, and check the result.
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
extend xbus_env_u {

    tf_main_test() @tf_phase_clock is also {
        
        wait [100] * cycle;
        
        message(LOW, "Config MIN_ADDR of SLAVE_0 to 0x12 ",
                     "and its MAX_ADDR to 0xffe");
        //            ------------------------------------
        uvm_configure 1 me {slave_name;  min_addr; max_addr} 
                {xbus_agent_name_t'SLAVE_0; 0x12; 0xffe};


        // Check:
        check that slaves[0].config.params.min_addr == 0x12 else
          dut_error("2nd configuration failed, config.min_addr == ",
                    slaves[0].config.params.min_addr);
        check that slaves[0].config.params.max_addr == 0xffe else
          dut_error("2nd configuration failed, config.max_addr == ",
                    slaves[0].config.params.max_addr);

        
        message(LOW, "Config MAX_ADDR of SLAVE_1 to 0xbeef");
        //            ----------------------------------------
        uvm_configure 2 me {slave_name;  max_addr} 
                {xbus_agent_name_t'SLAVE_1; 0xbeef};
       
        
        // Check:
        check that slaves[1].config.params.max_addr == 0xbeef else
          dut_error("1st configuration failed, config.max_addr == ",
                    slaves[1].config.params.max_addr);
         
        
        
        wait cycle;
        message(LOW, "Min address of slave0 to 0, ",
                     "Max address of slave0 to 0x7ff0");
        //           -------------------------------
        uvm_configure 3 me {slave_name;  min_addr; max_addr} 
                {xbus_agent_name_t'SLAVE_0; 0x0; 0x7fff};

        // Check:
        check that slaves[0].config.params.min_addr == 0x0 else
          dut_error("3rd configuration failed, config.min_addr == ",
                    slaves[0].config.params.min_addr);
        check that slaves[0].config.params.max_addr == 0x7fff else
          dut_error("3rd configuration failed, config.max_addr == ",
                    slaves[0].config.params.max_addr);
      

        wait cycle;
        message(LOW, "Min address of slave1 to 0x8000, ",
                     "Max address of slave0 to 0xffff");
        //           -------------------------------
        uvm_configure 4 me {slave_name;  min_addr; max_addr} 
                {xbus_agent_name_t'SLAVE_1; 0x8000; 0xffff};

        // Check:
        check that slaves[1].config.params.min_addr == 0x8000 else
          dut_error("4th configuration failed, config.min_addr == ",
                    slaves[1].config.params.min_addr);
        check that slaves[1].config.params.max_addr == 0xffff else
          dut_error("4th configuration failed, config.max_addr == ",
                    slaves[1].config.params.max_addr);
    
        wait [150] * cycle;

    }; -- tf_main_test()

}; 

'>


