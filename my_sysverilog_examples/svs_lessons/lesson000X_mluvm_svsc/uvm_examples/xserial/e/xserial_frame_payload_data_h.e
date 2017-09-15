/*------------------------------------------------------------------------- 
File name   : xserial_frame_payload_data_h.e
Title       : XSerial eVC frame payload structure for data frames 
Project     : XSerial eVC
Created     : 2008
Description : This file declares the format of the DATA subtype of the
            : XSerial frame payload. 
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide

-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- Extend the frame format type to provide a new format called DATA.
extend xserial_frame_format_t : [DATA = 2'b00];


-- Make DATA the default payload format
extend xserial_frame_payload_s {
    keep soft frame_format == DATA;
}; -- extend xserial_frame_payload_s


-- Extend the DATA sub-type of the payload.
extend DATA xserial_frame_payload_s {

    -- This field contains the data bits for a DATA payload. Bit 0 is sent
    -- first down the serial interface.
    %data : byte;
    
    -- Unpack the data part of a DATA payload
    unpack_payload(bitstream : list of bit, check_protocol : bool) is also {
        unpack(packing.low, bitstream[4..11], data);
    }; -- unpack_payload()

    -- Add the data value to the 'nice string'.
    nice_string(): string is also {
        result = appendf("%s DATA:%02x       ", result, data);
    }; -- nice_string()
   
    -- Compare data fields of DATA payloads.
    compare_payloads(exp_payload : xserial_frame_payload_s, 
                     compare_dest : bool) : list of string is also {
        if exp_payload is a DATA xserial_frame_payload_s (d) and
           d.data != data {
            result.add(append("Expected data field: ", 
                              hex(d.data),
                              ", Actual data field: ", 
                              hex(data)));
        };
    }; -- compare_payloads()

    -- Called by Structured Messages 
    get_attribute_value(name: string): string is also {
        if name == "data" {
            result = append(data);
        };
    };
}; -- extend DATA xserial_frame_payload_s

'>

