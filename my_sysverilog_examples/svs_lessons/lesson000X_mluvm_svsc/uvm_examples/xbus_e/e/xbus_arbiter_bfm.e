/*------------------------------------------------------------------------- 
File name   : xbus_arbiter_bfm.e
Title       : Arbiter BFM
Project     : XBus UVC
Created     : 2008
Description : This file adds arbiter functionality to the generic BFM.
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


extend ARBITER xbus_bfm_u {
    
    // testflow main methods are expected to be found in the top portion of the
    // unit to better recognize the functional behavior of the unit
    
    tf_env_setup() @tf_phase_clock is also {
        -- Make sure that all gnt signals start the test low.
        for each (msmp) in msmps {
            msmp.sig_grant$ = 0;
        };
    }; 
    
    tf_reset() @tf_phase_clock is also {
        -- drive START low during reset
        smp.sig_start$ = 0;
    };
    
    tf_init_dut() @tf_phase_clock is also {
        start drive_transfers();
        // Register the thread as running until POST_TEST, non blocking
        tf_get_domain_mgr().register_thread_by_name(me, "drive_transfers", 
                                                    POST_TEST, FALSE);
    };
    
    -- This is a list of pointers to the master signal maps.
    msmps : list of xbus_master_signal_map_u; 

    -- This field indicates the currently granted master.
    private !current_granted_master : MASTER xbus_agent_u;
    
    -- This event is emitted for each arbitration phase.    
    event start_asserted is rise
      (smp.sig_start$ == 1 and not synch.reset_asserted) @synch.clock_fall;
    
    -- This code starts the arbitration BFM each time a new transfer starts.
    on start_asserted {
        start handle_arbitration();
    }; -- on start_asserted
    
    -- This TCM handles the arbitration phase. It gets started each time the
    -- 'start' signal is asserted.
    package handle_arbitration() @tf_phase_clock is {

        -- Get a list of the masters requesting the bus and pass this to the
        -- sequence driver.
        driver.requests = msmps.all(.sig_request$ == 1).apply(it.master);
            
        -- Ask the sequence driver for a decision on this arbitration phase.
       
        var decision := driver.try_next_item();
        if decision == NULL {
            error("Arbiter sequence driver provided NULL arbitration decision");
        };
        
        current_granted_master = decision.granted_master;
        
        messagef(HIGH, "Abitration chose: ") {
            if current_granted_master == NULL {
                out(" NULL (no requests pending)");
            } else {
                out(current_granted_master.agent_name);
            };
        };
        
        -- Drive the appropriate gnt signal high (and the others low).
        for each (msmp) in msmps {
            if msmp.master == current_granted_master {
                msmp.sig_grant$ = 1;
            } else {
                msmp.sig_grant$ = 0;
            };
        };
        
        -- Wait until end of arbitration phase.
        wait cycle;
        
        -- Inform the sequence driver that the arbitration phase is over.
        emit driver.item_done; 
         
        -- Between arbitration phases, drive all gnt signals low.
        for each (msmp) in msmps {
            msmp.sig_grant$ = 0;
        };
    }; -- handle_arbitration()

    -- This TCM handles the responsibilities of the arbiter during a
    -- single transfer. This includes driving the start signal and driving
    -- a NOP transfer if necessary.
    private drive_transfer() @synch.clock_rise is {
    
        -- Drive start high during Arbitration Phase.
        smp.sig_start$ = 1;
        wait cycle;
        smp.sig_start$ = 0;
        
        -- Now we're at the start of the Address Phase.
        -- Check to see if any masters have been granted the bus - 
        -- if not, then do a NOP transfer.
        if current_granted_master == NULL {
            -- This is a NOP transfer
            message(HIGH, "Arbiter drove NOP cycle");
            smp.sig_addr$  = 0x0000;
            smp.drive_size(1);
            smp.drive_read_write(NOP);
            wait cycle;
            smp.sig_addr.put_mvl_string("32'bz");
            smp.sig_size.put_mvl_string("2'bz");
            smp.sig_read.put_mvl_string("1'bz");
            smp.sig_write.put_mvl_string("1'bz");
            -- NOP transfer has no Data Phase, so we're done
        } else {
            -- This is a normal transfer, so wait for the end of the
            -- Address Phase.
            wait cycle;
            -- Now wait until the end of the Data Phase.
            wait @bus_monitor.transfer_end;
        }; -- if current_granted_master == NULL;
    }; -- drive_transfer()
    
    -- This TCM continually calls do_transfer() 
    
    private drive_transfers() @tf_phase_clock is {      
        while TRUE {
            drive_transfer();
        }; -- while TRUE
    }; -- drive_transfers()
                
    
}; -- extend ARBITER xbus_bfm_u {

'>

