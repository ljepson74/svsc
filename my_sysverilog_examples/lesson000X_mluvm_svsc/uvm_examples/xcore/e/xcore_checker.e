/*------------------------------------------------------------------------- 
File name   : xcore_check.e
Title       : Checking definitions XCore 
Project     : XCore eVC
Created     : 2008
Description : 
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'
package cdn_xcore;

#ifdef SPECMAN_FULL_VERSION_09_20 {
import  uvm_e/e/uvm_scbd_top.e;
};
#ifndef SPECMAN_FULL_VERSION_09_20 {
import uvm_scbd/e/uvm_scbd_top.e;
};
'>
   


Using the UVM Scoreboard

<'
unit xserial_to_xserial_scbd like uvm_scoreboard {
    scbd_port add_p   : add MONITOR xserial_frame_s;
    scbd_port match_p : match MONITOR xserial_frame_s;
    
    add_p_predict(originator: MONITOR xserial_frame_s) is only {
        if (originator.payload.frame_format != DATA) {
            // Ignore, non Data
        } else {
            var frame := originator.copy();
            frame.parity = frame.calc_parity();
            add_to_scbd(frame);
        };
    }; // add_port_predict()
    
    match_p_reconstruct(originator: MONITOR xserial_frame_s) is only {
        if (originator.payload.frame_format != DATA) {
            // Ignore, non Data
        } else {
            var frame :  MONITOR xserial_frame_s;
            frame = originator.copy();
            match_in_scbd(frame);
        };
    }; // match_port_reconstruct()
};
'>


   
   Flow Control

<'
extend has_checks xcore_monitor_u { 
    
    -- Check the internal signal indicating fifo overflow
    expect no_overflow_signal is @ref_model_fifo_full => {
       [1..100] * cycle;
       @overflow or true(overflow_state != TRUE) } else
      dut_error("XCore did not raise the overflow signal after its ",
                "RX fifo got full");
    
    -- If a frame was sent when the was fifo full - 
    -- check that xcore sent HALT
    expect no_halt_frame is @overflow => {
       [1..200] * cycle;
       @xcore_sent_halt} else
      dut_error("XCore did not send a HALT frame after overflow");
    
}; -- extend xcore_monitor_u
'>




