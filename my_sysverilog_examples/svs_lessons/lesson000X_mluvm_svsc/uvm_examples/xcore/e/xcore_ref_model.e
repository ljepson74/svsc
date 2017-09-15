/*------------------------------------------------------------------------- 
File name   : xcore_ref_model.e
Title       : Reference model for XCore HDL
Project     : XCore eVC
Created     : 2008
Description : This file implements a 'reference model' of the XCore HDL.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

define XCORE_RX_FIFO_DEPTH 2;

-- Reference model behaviour 
extend xcore_monitor_u {
   
    -- Fields updated during the run, keeping DUT current status
   
    -- This field keeps track of whether it is safe to write to the TX_DATA
    -- register.
    !tx_write_safe : bool;

    -- This field keeps track of whether it is safe to read from the RX_DATA
    -- register.
    !rx_read_safe : bool;
    
        
    -- This field is used to build up the transmitted frame which is 
    -- expected to be transmitted by the XCore as a result of a WRITE 
    -- transaction. 
    !tx_frame : MONITOR xserial_frame_s;
    
    -- This field is used to build up the received frame which is read
    -- from the bus in a READ transaction
    !rx_frame : MONITOR xserial_frame_s;
    
    -- This field is used to monitor the number of items in the 
    -- XCore RX fifo
    !items_in_rx_fifo: uint;

    -- This field is used to keep RX fifo overfow status
    overflow_state : bool;
    
    -- Implementation of the in port, called by the XBus monitor
    xbus_write(transfer : MONITOR xbus_trans_s ) is also {
        if legal_access(transfer) {
            update_reg_file(transfer); 
        };
    };
    
    
    -- These events are for post tranfer activities
    event tx_frame_written;
    event rx_frame_read;

    
    -- On end of frame - pass info to upper level/s (including the scoreboard)
    on tx_frame_written {
        tx_frame_written_o$.write(tx_frame);  
    };
    on rx_frame_read {
        rx_frame_read_o$.write(rx_frame);  
    };
 
    -- This method initialises the reference model (e.g. after reset).
    init_model() is {
        tx_write_safe = FALSE;
        rx_read_safe = FALSE;    
        items_in_rx_fifo = 0;
        overflow_state = FALSE;
    }; -- init_model()
    
    run() is also {
        init_model();
    }; -- run()
    
    -- This method takes an XBus transfer and returns TRUE if this 
    -- transfer would result in this XCore producing a bus error.
    legal_access(t :  xbus_trans_s) : bool is {
        result = TRUE;
        
        if (t.as_a(MONITOR xbus_trans_s).error_pos_mon != 0) {
            result = FALSE;            
        };
        var offset : int = t.addr - base_address;
        if offset in [0..0xff] {
            if (t.size != 1) or
               (offset not in [0..3]) or
               ((offset == 0) and (t.read_write == WRITE) and 
                   (not tx_write_safe)) or
               ((offset == 2) and (t.read_write == READ) and 
                   (not rx_read_safe)) or
               ((offset in [2, 3]) and (t.read_write == WRITE)) {
                result = FALSE;
            };
        };
    }; -- error_expected()

   

    -- Update the register file after each XBus transfer
    
    update_reg_file( transfer: MONITOR xbus_trans_s ) is {
          if transfer.read_write == WRITE then {
              reg_file.update(transfer.addr - base_address, 
                        %{transfer.data},{});
          } else {
            compute reg_file.compare_and_update(transfer.addr - base_address,
                                                %{transfer.data});
        };
    }; 

}; -- extend xcore_monitor_u

'>


Create frames from registers accesses.

Writing TX frame, to Xcore TX fifo - 
      READ TX_DATA_REG until reading 0, 
      WRITE to TX_DATA_REG the data to transmit
Reading RX frame from Xcore RX fifo   


<'
extend XCORE vr_ad_reg_file {
    !monitor : xcore_monitor_u;
};


// Build frames from registers access:
//  Writing TX frame to TX fifo:
//   Write to XCORE_TX_MODE the frame destination and kind
//   Write to XCORE_TX_DATA the frame data
//  Reading RX frame from RX fifo:
//   Read from XCORE_RX_MODE the frame destination and kind
//   Read from XCORE_RX_DATS the frame data

extend XCORE_TX_MODE vr_ad_reg {
    post_access(d : vr_ad_rw_t) is {
        var monitor := static_info.access_path.as_a(XCORE vr_ad_reg_file).monitor;
        if d == WRITE {
            -- Start building the frame which is expected to be transmited 
            -- as a result of this register access
            monitor.tx_frame = new with {
                .start_bit = 0;
                .stop_bit = 1;
            };
            monitor.tx_frame.payload = new with {
                .destination = dest;
                .physical_frame_format = frame_kind;
            };
            if frame_kind in all_values(xserial_frame_format_t).
              apply(it.as_a(uint)) {
                monitor.tx_frame.payload.frame_format =
                  frame_kind.as_a(xserial_frame_format_t);
            } else {
                monitor.tx_frame.payload.frame_format = UNDEFINED;
            };
            msg_started(MEDIUM, 
                        "Building TX frame from regs accesses",
                        monitor.tx_frame);
        };
        
    };
};

extend XCORE_TX_DATA vr_ad_reg {
    post_access(d : vr_ad_rw_t) is {
        var monitor := static_info.access_path.as_a(XCORE vr_ad_reg_file).monitor;
    
        if d == READ {
            if (data & 0b00000001) == 0 {
                monitor.tx_write_safe = TRUE;
            };
        } else {
            monitor.tx_write_safe = FALSE;
            monitor.tx_frame.parity = monitor.tx_frame.calc_parity();
           
            if monitor.tx_frame.payload is a DATA
              xserial_frame_payload_s (d_p) {
                d_p.data = data;
            };
            
            if monitor.tx_frame.payload is a MESSAGE 
              xserial_frame_payload_s (d_m) {
                if d_m.frame_message in [HALT, RESUME] {
                    d_m.frame_message = IDLE;
                };
            };
            msg_ended(MEDIUM, 
                      "Building TX frame from regs accesses",
                      monitor.tx_frame);
            
            emit monitor.tx_frame_written;
        };
    };
};



extend XCORE_RX_MODE vr_ad_reg {
    post_access(d : vr_ad_rw_t) is {
        var monitor := static_info.access_path.as_a(XCORE vr_ad_reg_file).monitor;
        if valid_frame == 1 {
            monitor.rx_read_safe = TRUE;
            -- Start building the frame which is expected to be transmited 
            -- as a result of this register access
            monitor.rx_frame = new with {
                .bad_parity = par_err;
                .start_bit = 0;
                .stop_bit = 1;
            };
            monitor.rx_frame.payload = new with {
                .destination = dest;
                .physical_frame_format = frame_kind;
            };
           
            if frame_kind in all_values(xserial_frame_format_t).apply(it.as_a(uint)) {
                monitor.rx_frame.payload.frame_format = frame_kind.as_a(xserial_frame_format_t);
            } else {
                monitor.rx_frame.payload.frame_format = UNDEFINED;
            };
            msg_started(MEDIUM, 
                        "Building RX frame from regs accesses",
                        monitor.rx_frame);
        };
    };
};

extend XCORE_RX_DATA vr_ad_reg {
    post_access(d : vr_ad_rw_t) is {
        var monitor := static_info.access_path.as_a(XCORE vr_ad_reg_file).monitor;
      
        monitor.rx_read_safe = FALSE;
         
        if monitor.rx_frame.payload is a DATA
          xserial_frame_payload_s (d_p) {
            d_p.data = data;
        };
        
        monitor.rx_frame.parity =  monitor.rx_frame.calc_parity();
        if monitor.rx_frame.bad_parity then {
            monitor.rx_frame.status.add(BAD_PARITY);
        };
        
        msg_ended(MEDIUM, 
                  "Building RX frame from regs accesses",
                  monitor.rx_frame);
        emit monitor.rx_frame_read;
    };
};
'>


   Flow Control mechanism
   
   
<'
extend xcore_monitor_u { 
    
    event fifo_event;
    
    -- This event is emited when XCore indicates RX fifo overflow
    event overflow;

    -- This event is emited when reference model indicates RX fifo overflow
    event ref_model_fifo_full;

    -- This event is emited when the XCore transmits a HALT message
    event xcore_sent_halt;

    -- This event is emited when the XCore transmits a RESUME message
    event xcore_sent_resume;

    -- This event is emited when the XCore receives a HALT message
    event xcore_got_halt;

    -- This event is emited when the XCore receives a RESUME message
    event xcore_got_resume;


    on rx_frame_read {
        items_in_rx_fifo -= 1;
        if (items_in_rx_fifo < XCORE_RX_FIFO_DEPTH) then {
            overflow_state = FALSE;
        };
    }; 
    
    on rx_frame_ended {
       if cur_rx_frame.payload is a DATA xserial_frame_payload_s  then {
          items_in_rx_fifo += 1;
       }; 
       if items_in_rx_fifo == 2 then {
           emit ref_model_fifo_full;
           overflow_state = TRUE;
       }; -- if items_in_rx_...
    }; -- on rx_frame_end...
    
    on tx_frame_ended { 
       if cur_tx_frame.payload is a MESSAGE xserial_frame_payload_s (MP) {
          if MP.frame_message == HALT then {
             emit xcore_sent_halt;
          }; -- if MF.payload.m...
          if MP.frame_message == RESUME then {
             emit xcore_sent_resume;
          }; -- if MF.payload.m...
       }; -- if cur_tx_frame...
    }; -- on tx_frame_end...

    on rx_frame_ended { 
       if cur_rx_frame.payload is a MESSAGE xserial_frame_payload_s (MP) {
          if MP.frame_message == HALT then {
             emit xcore_got_halt;
          }; -- if MF.payload.m...
          if MP.frame_message == RESUME then {
             emit xcore_got_resume;
          }; -- if MF.payload.m...
       }; -- if cur_rx_frame...
    }; -- on rx_frame_end...

    event fifo_overflow_sequence is {
       @ref_model_fifo_full;
       [1..50] * cycle;
       @overflow;
       [1..120] * cycle;
       @xcore_sent_halt;
    }; -- event fifo_over...
    
}; 


extend xcore_monitor_u { 
    
    event fifo_event is only rise(sig_flow$) @sim;
    
    -- This event is emited when XCore indicates RX fifo overflow
    event overflow is only rise(sig_halt_int$) @fifo_event;
};
'>

