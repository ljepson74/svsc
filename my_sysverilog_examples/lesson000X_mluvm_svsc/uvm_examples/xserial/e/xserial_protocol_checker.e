/*------------------------------------------------------------------------- 
File name   : xserial_protocol_checker.e
Title       : Protocol checker 
Project     : XSerial eVC
Created     : 2008
Description : This file contains the optional protocol checker 
            : functionality within the monitor.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

extend has_protocol_checker xserial_monitor_u {

    -- This event is emitted in each clock cycle where the remote device
    -- has signalled that it is not ready to receive data frames. 
    -- The falling edge of clock is used to ensure that there are no race
    -- conditions in the case where both monitors are clocked off the same
    -- clock signal. If the rising edge is used then the order in which the
    -- RX and TX monitors
    -- react to the rising edge of clock can affect the protocol checker.
    event halted is true((reverse_monitor != NULL) and 
                         (not reverse_monitor.ready)) @clock_fall;
                         
    -- This event is the same as halted but delayed to the next rising
    -- edge of clock.
    event halted_del is {@halted; [1]} @clock_rise;

    -- This event is emitted each time a frame starts while the remote
    -- device is not ready. 
    event frame_start_halted is (@halted_del and 
                                 @frame_started and
                                 @halted)
                                                          @clock_rise;
             
    -- This event is emitted each time a message frame ends
    event message_frame_ended is
        true(monitor_frame.payload is a MESSAGE xserial_frame_payload_s) 
                                                              @frame_ended;
             
    -- At the end of each frame, check that either it was a message frame 
    -- or the remote device hadn't signalled a HALT before the start of 
    -- the frame. Only message frames are allowed to start while the 
    -- remote device is not ready.
    expect exp_send_while_not_ready is
        (not @frame_start_halted) or @message_frame_ended @frame_ended
        else dut_error("Non-message frame sent while remote device ",
                       "was not ready");

}; -- extend has_protocol_checker xserial_monitor_u



'>

