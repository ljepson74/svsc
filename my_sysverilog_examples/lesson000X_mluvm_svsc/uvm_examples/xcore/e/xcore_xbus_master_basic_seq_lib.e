/*------------------------------------------------------------------------- 
File name   : xcore_xbus_master_basic_seq_lib.e
Title       : XBus sequence lib
Project     : XCore eVC
Created     : 2008
Description : Defines XBus sequences for reading/writing to XCore
            : based on the seuqcnes define in the xbus eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

'>


<'   
extend xbus_master_sequence_kind : [XCORE_WRITE_FRAME, 
                                       XCORE_READ_FRAME, 
                                       XCORE_READ_WRITE_FRAME];


-- The WRITE_FRAME sequence writes a frame to an instance of the XCore.
-- It will poll the XCore to ensure that it is ready before writing the
-- frame data.
extend XCORE_WRITE_FRAME xbus_master_sequence {

    -- This field specifies the XCore base address
    base_addr : uint(bits:16);
        keep soft base_addr == 0;

    -- This field specifies the frame format of the frame to be written.
    frame_format : xserial_frame_format_t;
        keep soft frame_format == DATA;
    
    -- This field controls the physical representation of the frame_format
    -- field.
    private frame_format_physical : uint(bits:2);
        keep frame_format_physical == read_only(frame_format).as_a(uint);
    
    -- This field controls the destination of the frame to be written.
    destination : uint(bits:2);
    
    -- This field contains the payload of the frame to be written.
    data : byte;
    
    body() @driver.clock is only {


       var poll : byte; -- the result of polling the XCore
       repeat {
           poll = read(1, base_addr+0);
        } until poll[0:0] == 0;
       write(1, base_addr+1, pack(packing.low, destination, 
                                   frame_format_physical));
       write(1, base_addr+0, data);
       
    }; -- body()
    
}; -- extend XCORE_WRITE_FRAME xbus_master_sequence


-- The XCORE_READ_FRAME sequence reads a frame from an instance of the 
-- XCore. It will poll the XCore to ensure that there is valid data ready 
-- before reading the frame data.
extend XCORE_READ_FRAME xbus_master_sequence {

    -- This field specifies the XCore base address
    base_addr : uint(bits:16);
        keep soft base_addr == 0;
    
    -- This field is used to store the payload of the received frame.
    !data : byte;
    
    -- This field is used to store the frame format of the received frame.
    !frame_format : xserial_frame_format_t;
    
    -- This field is used to store the destination of the received frame.
    !destination : uint(bits:2);
    
    -- This field is used to store the error flag of the received frame.
    !error_flag : bool;
    
    body() @driver.clock is only {
        
       var poll : byte; -- the result of polling the XCore
       repeat {
          poll = read(1, base_addr+3);
       } until poll[5:5] == 1;
       destination = poll[1:0];
       if poll[3:2] in all_values(xserial_frame_format_t).
         apply(it.as_a(uint)) {
          frame_format = poll[3:2].as_a(xserial_frame_format_t);
       } else {
          frame_format = UNDEFINED;
       };
       error_flag = poll[4:4].as_a(bool);
       data = read(1, base_addr+2);
       
    }; -- body()
    
}; -- extend XCORE_READ_FRAME xbus_master_sequence


-- The XCORE_READ_WRITE_FRAME sequence reads a frame from an instance 
-- of the XCore and writes it immediately back to an instance of the XCore. 
-- If a frame is received with an error, it is discarded.
extend XCORE_READ_WRITE_FRAME xbus_master_sequence {

    -- This field specifies the base address of the XCore device the frame 
    -- is read from.
    rx_base_addr : uint(bits:16);
        keep soft rx_base_addr == 0;
    
    -- This field specifies the base address of the XCore device the frame 
    -- is written to.
    tx_base_addr : uint(bits:16);
        keep soft tx_base_addr == 0;
    

    -- This field is provide to facilitate "do xcore_read".
    !xcore_read : XCORE_READ_FRAME xbus_master_sequence;
    
    -- This field is provide to facilitate "do xcore_write".
    !xcore_write : XCORE_WRITE_FRAME xbus_master_sequence;
    
    body() @driver.clock is only {

        do xcore_read keeping { .base_addr == rx_base_addr };
        if not xcore_read.error_flag {
            do xcore_write keeping {
                .base_addr    == tx_base_addr;
                .frame_format == xcore_read.frame_format;
                .destination  == xcore_read.destination;
                .data         == xcore_read.data;
            };
        };
        
    }; -- body()
    
}; -- extend XCORE_READ_WRITE_FRAME xbus_master_sequence


'>

