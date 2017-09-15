/*------------------------------------------------------------------------- 
File name   : xbus_slave_bfm.e
Title       : Slave BFM
Project     : XBus UVC
Created     : 2008
Description : This file adds slave functionality to the generic BFM.
Notes       : This is a re-active sequence driver
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



extend SLAVE xbus_bfm_u {
    
    // testflow main methods are expected to be found in the top portion of the
    // unit to better recognize the functional behavior of the unit
    // Run the main slave BFM in MAIN_TEST phase.
    tf_main_test() @tf_phase_clock is also {
        start drive_responses();
        // Register the thread as running until POST_TEST, non blocking
        tf_get_domain_mgr().register_thread_by_name(me, "drive_responses", 
                                                    POST_TEST, FALSE);
    }; // tf_main_test()

    // default values during reset phase
    tf_reset() @tf_phase_clock is also {
        smp.sig_wait.put_mvl_string("1'bz");
        smp.sig_error.put_mvl_string("1'bz");
        smp.sig_start$ = 0;
        
        smp.sig_addr$ = 0;
        smp.sig_read$ = 0;
        smp.sig_write$ = 0;
        smp.sig_data.put_mvl_string("8'bz"); 
    };
    
    // This field is a pointer to the slave's configuration unit.
    // (e.g. min/max address).
    config : xbus_slave_config_u;
        
    // This field is a copy of the use_ram field in the SLAVE agent.   
    use_ram : bool;

    // This field is a pointer to the ram field in the SLAVE agent.
    ram : simple_ram_env_u;
    
    // This TCM is the main BFM loop that continually detects transfers
    // received by this slave and responds to them as required. 
    private drive_responses() @tf_phase_clock is { 
        message(LOW, "Slave BFM started");
     
        while TRUE {
           
            -- Wait for the start of a non-NOP Address Phase.
            wait @bus_collector.normal_address_phase;                
            -- Is the current transfer addressed at this slave?
            if config.in_range(bus_collector.transfer.addr) {
                driver.transfer = deep_copy(bus_collector.transfer);
                message(MEDIUM, "Transfer detected: ", driver.transfer);
                
                var resp := driver.try_next_item();
                if resp == NULL {
                    error("Slave sequence driver provided NULL response");
                };
                respond_to_transfer(resp);
                emit driver.item_done;
               
            };
        }; -- while TRUE
        message(LOW, "Slave BFM ended");        
    }; -- drive_responses()
    
    -- This TCM gets called once the sequence driver has returned a transfer
    -- response item. It causes the BFM to respond with an appropriate Data
    -- Phase.
    private respond_to_transfer(resp : xbus_slave_response_s)
                                        @tf_phase_clock is {
        msg_started(MEDIUM, "Driving response", resp);
        msg_transformed(MEDIUM, "responding to", resp, bus_collector.transfer);
        
        
        case resp.transfer.read_write {
            WRITE   : { do_slave_write(resp); };
            READ    : { do_slave_read(resp); };
            default : { wait; error("UVC internal error"); };
        };
        msg_ended(MEDIUM, "Driving response", resp);
        
        
   }; -- respond_to_transfer()
                                    
    -- This TCM handles the Data Phase of a write transfer.
    private do_slave_write(resp : xbus_slave_response_s) 
                                                @tf_phase_clock is {
        smp.sig_error$ = 0;
        resp.transfer.data.resize(resp.transfer.size);
        for i from 0 to (resp.transfer.size-1) {
            message(FULL, "Byte number ", dec(i), " : ",
                          dec(resp.wait_states[i]), " wait states");
            if resp.wait_states[i] > 0 {
                smp.sig_wait$ = 1;
                wait [resp.wait_states[i]] * cycle;
            };

            smp.sig_wait$ = 0;
            if i == resp.error_pos {
                smp.sig_error$ = 1;
                message(FULL, "Byte number ", dec(i), " : ERROR");
                wait cycle;
                break; -- an error terminates the transfer
            };
            wait cycle;
            var data : byte = smp.sig_data$;
            if use_ram {
                ram.write_byte(resp.transfer.addr + i, data);
            };
            resp.transfer.data[i] = data;
            message(HIGH, "Byte number ", dec(i), " : data = ", data);
        };
        smp.sig_wait.put_mvl_string("1'bz");  
        smp.sig_error.put_mvl_string("1'bz");  
        message(MEDIUM, "Write transfer completed: ", resp.transfer);
    }; -- do_slave_write()
    
    -- This TCM handles the Data Phase of a read transfer.
    private do_slave_read(resp : xbus_slave_response_s) 
                                                      @tf_phase_clock is { 
        smp.sig_error$ = 0;
        resp.transfer.data.resize(resp.transfer.size);
        for i from 0 to (resp.transfer.size-1) {
            message(FULL, "Byte number ", dec(i), " : ", resp.wait_states[i],
                          " wait states");

            if resp.wait_states[i] > 0 {
                smp.sig_wait$ = 1;
                 smp.sig_data.put_mvl_string("8'bz");
                wait [resp.wait_states[i]] * cycle;
            };
            smp.sig_wait$ = 0;
            if i == resp.error_pos {
                smp.sig_error$ = 1;
                message(FULL, "Byte number ", dec(i), " : ERROR");
                wait cycle;
                break; -- an error terminates the transfer
            };
            var data : byte;
            if use_ram {
                data = ram.read_byte(resp.transfer.addr + i);
                resp.transfer.data[i] = data;
            } else {
                data = resp.transfer.data[i];
            };
            smp.sig_data$ = data;
            message(HIGH, "Byte number ", dec(i), " : data = ", data);
            wait cycle;
        };
        smp.sig_wait.put_mvl_string("1'bz");
        smp.sig_error.put_mvl_string("1'bz");   
        smp.sig_data.put_mvl_string("8'bz"); 
        message(MEDIUM, "Read transfer completed: ", resp.transfer);
    }; -- do_slave_read()
    
    
    
    // Calculate recoreded attributes 
    tr_get_attribute_value(inst: any_struct, name: string): string is also {
        if inst is a xbus_slave_response_s (r) then {
            result = r.get_attribute_value(name);
        };
    };

}; -- extend SLAVE xbus_bfm_u {

-- in case of rerun_phase - clean the driver from previous bfm calls
extend xbus_slave_driver_u {
    tf_to_clean_previous_bfm_call(next_phase: tf_phase_t) : bool is {
        result = TRUE;
    };
};
'>

