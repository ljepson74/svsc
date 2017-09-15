/*------------------------------------------------------------------------- 
File name   : xcore_cover.e
Title       : DUT coverage
Project     : XCore eVC
Created     : 2008
Description : This file implements coverage of the major functions of
            : of the XCore core. 
            : Covering the actual HDL signals and also the state of the 
            : reference model.
Notes       : This file could also contain coverage of HDL nodes. In this
            : case, the signals to be covered would need to be specified
            : as part of the API for the eVC along with checks to ensure
            : that they are correctly constrained.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

'>

   

   Coverage definitions of the XBus
      
   
<'
extend has_coverage xcore_monitor_u {

    cover tx_frame_written is {
       item name using per_instance; 
       
       item data : byte =  cur_xbus_transfer.data[0] using 
          radix = HEX,
          ranges = {
            range([0]);
            range([1..0xFE]);
            range([0xFF]);
          };

    }; -- cover  tx_frame_written  


    cover rx_frame_read is {
        item name using per_instance; 
       
        item data : byte =  cur_xbus_transfer.data[0] using 
          radix = HEX,
          ranges = {
            range([0]);
            range([1..0xFE]);
            range([0xFF]);
          };
    }; -- cover rx_frame_read 
  
}; -- extend has_coverage xcore_monitor_u 
'>

   
   Coverage of XCore internals
   
   RX FIFO
   

<'
extend has_coverage xcore_monitor_u {
    
    
    -- Fifo state when XSerial agent transmits to XCore
    cover rx_frame_started is {      
       item name using per_instance;

       -- XCore status when XSerial sends frames to it
       item items_in_fifo : uint (bits : 2) = sig_item_count$
         using
         ignore = items_in_fifo == 3 ;
    }; -- cover tx_frame_started

    -- Was overflow, according to DUT
    cover overflow is {
       item name using per_instance;
       item sig_flow : bool = (sig_flow$ == 1 and sig_halt_int$ == 1 )
       using
          ignore = (sig_flow == FALSE) ,
         at_least = 5;
    }; -- cover overflow 

    
    cover fifo_overflow_sequence is {
       item name using per_instance;
       item full_of_sequence : bool = TRUE 
         using
          ignore = (full_of_sequence == FALSE),
           at_least = 5;
    }; -- cover fifo_overflow_sequence

    
    
}; -- extend has_coverage xcore_monitor_u

'>
   
   
   Modify existing coverage definitions according to XCore

   
   XSerial:

   
<'
extend MONITOR xserial_frame_s {
    cover tx_frame_done using also text = "eVC agent sending frames to XCore";
    cover rx_frame_done using also text = "XCore sending frames to eVC agent";

    
    cover tx_frame_done   is also {
        
        item data 
         using also
           ranges = {
             range([0]);
             range([1..0xFE]);
             range([0xFF]);
           }; --

       item inter_frame_delay 
         using also
           ranges = {
             range([1]);
             range([2..100]);
             range([101..1000]);
           };
        
        item frame_message using also ignore = frame_message == UNDEFINED;
        item frame_format using also ignore = frame_format == UNDEFINED;
    }; -- cover tx_frame_...

    cover rx_frame_done is also {

        item data 
         using also
           ranges = {
             range([0]);
             range([1..0xFE]);
             range([0xFF]);
           }; --

       item inter_frame_delay 
         using also
           ranges = {
             range([1]);
             range([2..100]);
             range([101..MAX_UINT]);
           };
        item frame_message using also ignore = frame_message == UNDEFINED;
    }; -- cover rx_frame_...

    
 }; --

'>
  
   
   XBus:
   
<'
extend xbus_bus_monitor_u {
    cover transfer_end is also {
        item size using also ignore = size != 1;
    };
};
extend xbus_agent_monitor_u {
    cover agent_trans_end is also {
        item size using also ignore = size != 1;
    };
};



extend xcore_monitor_u {
   post_generate() is also {
      covers.set_cover("xbus_agent_monitor_u.agent_trans_end(name==NO_AGENT)", 
       FALSE);

   }; -- post_generate() is also

}; -- extend xcore_monitor_u 

'>
   
   
   
   
   Registers:

   
<'
extend vr_ad_reg {
        
    cover reg_access (kind == XCORE_TX_MODE) is also {
       item direction 
         using also 
           ignore = (direction == READ);
    }; -- cover reg_acces...

    cover reg_access (kind == XCORE_RX_DATA) is also {
       item direction 
         using also 
           ignore = (direction == WRITE);
    }; -- cover reg_acces...
 
    cover reg_access (kind == XCORE_RX_MODE) is also {
       item direction 
         using also 
           ignore = (direction == WRITE);
    }; -- cover reg_acces...
 
}; -- extend vr_ad_reg



'>
   

   Interactions

   
   XCore receives HALT message right-before/during/right-after transmit
   
<'
extend xcore_monitor_u {
     halt_frame_started : time;
        keep soft halt_frame_started == 0;

    time_from_halt_to_program : uint;
        keep soft time_from_halt_to_program == MAX_UINT;

    event halt_after_tx_program is {
       -- Log time RX began
       @rx_frame_started exec {halt_frame_started = sys.time}; 
       [..];
       -- RX frame should be HALT message frame
       @rx_frame_ended and 
           true (cur_rx_frame.payload is a 
                            MESSAGE xserial_frame_payload_s (MP) and
                 MP.frame_message == HALT);
       
       [..];
       
       -- Save delay from end of HALT frame to end of programming the XCor
       @tx_frame_written 
         exec {time_from_halt_to_program = sys.time - halt_frame_started}; 
    }; 
    
    
    when has_coverage xcore_monitor_u {
        cover halt_after_tx_program is {
            item time_from_halt_to_program 
              using 
              text = 
              "Time from sending HALT to XCore, to time programmed it to TX",
              ignore = time_from_halt_to_program == MAX_UINT,
              ranges = {
                range([0..1]);
                range([2..10]);
                range([11..MAX_UINT]);
            };
        };
    };
   
 }; -- extend has_coverage xcore_monitor_u
 
'>


