/*------------------------------------------------------------------------- 
File name   : xserial_bfm.e
Title       : XSerial BFM implementation
Project     : XSerial eVC
Created     : 2008
Description : This file contains private implementation of the BFM unit.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;


extend xserial_bfm_u {
   
    -- This method is called to set the BFM to it's correct state during
    -- and after reset.
    private init_bfm() is {
        -- ensure TX_DATA is driven inactive during and just after reset.
        sig_tx_data$ = 1;
        message(LOW, "TX BFM initialised");
    };
    
      
    -- This TCM drives a single frame onto the TX_DATA signal.
    private drive_frame(frame : TX xserial_frame_s) 
                                   @tf_phase_clock is {
    
        message(HIGH, "transmit frame generated and ready to be sent: ",
                                                                  frame);
        
        wait [frame.transmit_delay] * cycle;
    
        -- If this is not a MESSAGE frame, then make sure receiver is ready.
        if frame.payload is not a MESSAGE xserial_frame_payload_s {
            while (rx_monitor != NULL) and (not rx_monitor.ready) {
                wait cycle;
            };
        };
        
        msg_started(MEDIUM, "Sending frame", frame);

        -- transmit frame
        var bit_list : list of bit;
        bit_list = frame.pack_frame();
        for each (b) in bit_list {
	    wait delay (1);
            sig_tx_data$ = b;
            wait cycle;
        };

        -- Make sure data goes high again even if stop bit is corrupted.
        sig_tx_data$ = 1;
        
        msg_ended(MEDIUM, "Sending frame", frame);

    }; -- drive_frame()

    -- This TCM runs continually pulling sequence items from the sequence
    -- driver and passing them to the BFM.
    private main_bfm() @tf_phase_clock is {
        while TRUE {
            
            var next_frame := driver.get_next_item();
            drive_frame(next_frame);
            emit driver.item_done;
        }; -- while TRUE
    }; -- main_bfm()
    
    tf_reset() @tf_phase_clock is also {
        init_bfm();
    };
    
    tf_main_test() @tf_phase_clock is also {
        start main_bfm();
        // Register the thread as running until POST_TEST, non blocking
        tf_get_domain_mgr().register_thread_by_name(me, "main_bfm", 
                                                    POST_TEST, FALSE);
    }; 

    
    
    // Calculate recoreded attributes 
    tr_get_attribute_value(inst: any_struct, name: string): string is also {
        if inst is a xserial_frame_s (f) then {
            result = f.get_attribute_value(name);
        };
    };

}; -- extend xserial_bfm_u


-- in case of rerun_phase - clean the driver from previous bfm calls
extend xserial_driver_u {
 tf_to_clean_previous_bfm_call(next_phase: tf_phase_t) : bool is {
        result = TRUE;
    };
};
'>

