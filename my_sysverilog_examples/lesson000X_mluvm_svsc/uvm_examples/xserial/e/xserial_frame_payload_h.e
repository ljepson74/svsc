/*------------------------------------------------------------------------- 
File name   : xserial_frame_payload_h.e
Title       : XSerial eVC frame payload structure
Project     : XSerial eVC
Created     : 2008
Description : his file declares the format of the generic XSerial frame
            : payload. 
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

-- This type is used to enumerate the 2-bit frame_format field in the frame.
-- The various possible sub-types are extended in the files that declare
-- the sub-type formats. Note that the UNDEFINED value is used in the case
-- where the user wants to generate a payload with an illegal frame_format
-- value. 
type xserial_frame_format_t : [UNDEFINED = UNDEF];



-- This type is used to indicate the status of a frame. In this file, 
-- only the values that are relevant to payloads are declared. 
-- The xserial_frame.e file extends this type to give other status
-- values. Note that because the XSerial protocol does not provide any
-- means of identifying the end of a frame other than the value of the
-- stop bit, it does not make sense to generate illegally short or
-- illegally long frames - the receiver will always take 15 bits from the
-- data signal regardless of how many we transmit. As such there is no
-- status value for an illegal length frame. Both the payload and the
-- frame structs use a list of this type so that multiple errors can
-- potentially be indicated.
type xserial_frame_status_t : [BAD_FORMAT]; -- illegal format field value



-- This struct contains the payload for a frame.
struct xserial_frame_payload_s {

    -- For generated payloads, this field is automatically updated by the
    -- eVC during post_generate() to indicate what error conditions are
    -- present in the payload. The user should not attempt to constrain 
    -- or assign a value to this field. When a payload is unpacked, this 
    -- field reflects the result of the unpacking. If this field is an 
    -- empty list then no errors are present in the payload.
    !status : list of xserial_frame_status_t;
        
    -- This field holds the destination address for the frame. This can be
    -- used by routers but is otherwise ignored.
    %destination : uint(bits:2);

    -- This field specifies the format of frame. 
    -- The xserial_frame_format_t type can be extended to define 
    -- various frame formats as required. Note that this field can only
    -- take values that are declared legal frame formats or UNDEFINED. 
    -- For this reason, the actual physical coding of this field in the 
    -- payload is held in the physical_frame_format field - which allows
    -- the user to generate frames with specific illegal formats.
    -- For generated frames, this field will not be UNDEFINED by default. 
    -- To generate frames will random illegal frame format values,
    -- constrain this field to UNDEFINED. To generate frames with specific
    -- illegal frame format values, constrain this field to UNDEFINED and
    -- also constrain the physical_frame_format field to the specific
    -- value. For unpacked frames, this field will indicate the enumerated
    -- frame format or UNDEFINED for illegal frame formats.
    frame_format : xserial_frame_format_t;
        keep soft frame_format != UNDEFINED;
     
    -- This field is the actual physical frame format field as encoded
    -- in the frame. See the frame_format field for more details.
    %physical_frame_format : uint(bits:2);
        keep (read_only(frame_format) != UNDEFINED) =>
            physical_frame_format == read_only(frame_format).as_a(uint);
        keep (read_only(frame_format) == UNDEFINED) =>
            physical_frame_format not in
                all_values(xserial_frame_format_t).all(it != UNDEFINED).
                           apply(it.as_a(uint));
        
    post_generate() is also {
        update_status();
    }; -- post_generate()
    
    -- This method returns the payload as a list of bits. By using this
    -- method rather than explicitly packing the struct, the user does 
    -- not need to be aware of the details of how a payload is packed.
    -- Note that in the XSerial eVC example, this is trivial, but in more
    -- complex eVCs, the process of packing a struct may be complex.
    pack_payload() : list of bit is {
        result = pack(packing.low, me);
    }; -- pack_payload()
    
    -- This method takes a bitstream and unpacks it into the payload struct.
    -- As with pack_payload(), this method hides the implementation details
    -- of the struct packing/unpacking from the user. In addition, if the
    -- check_protocol field is TRUE, then this method checks the protocol
    -- of the bitstream and reports dut errors where the protocol is
    -- illegal.
    unpack_payload(bitstream : list of bit, check_protocol : bool) is {

        unpack_payload_internal(bitstream, check_protocol);
        update_status();
    
    }; -- unpack_payload()
    
    -- The unpack_payload() method calls the unpack_payload_internal()
    -- method and then calls update_status(). This allows sub-types of 
    -- the payload to extend the unpacking behaviour while still ensuring
    -- that update_status() gets called last.
    unpack_payload_internal(bitstream      : list of bit, 
                            check_protocol : bool) is {
    
    
        -- The payload should always be exactly 12 bits long. NOTE: this
        -- isn't a DUT error (as the protocol provides no means of 
        -- detecting that a DUT has sent a frame that isn't 15 bits long) 
        -- - so this is really an eVC usage error.
        if bitstream.size() != 12 {
            error("FATAL: Frame payload is not 12 bits long");
        };

        -- Unpack the destination and frame_format fields.
        unpack(packing.low, bitstream, destination, physical_frame_format);
        if physical_frame_format in all_values(xserial_frame_format_t).
                      apply(it.as_a(uint)) {
            frame_format = physical_frame_format.
                            as_a(xserial_frame_format_t);
        } else {
            frame_format = UNDEFINED;
        };
        
        -- Make sure we've got a legal frame format. We'll assume that if
        -- the user extends xserial_frame_format_t then this makes the
        -- new value a legal frame format and the user will extend this
        -- subtype appropriately.
        if check_protocol {
            check illegal_frame_format that frame_format != UNDEFINED
                else dut_error("Illegal frame format found: ", 
                               physical_frame_format);
        };
        
    }; -- unpack_payload_internal()
    
    -- This method returns a convenient string representation of the 
    -- contents of the payload. This is used for logging, waveform viewing,
    -- etc.
    nice_string(): string is {
        result = appendf("DEST:%01d", destination);
    }; -- nice_string()
    
    -- This method compares this payload with a payload supplied as a
    -- parameter. If the compare_dest field is false, then differences in
    -- the destination fields are ignored. It returns a list of strings that
    -- contains all detected differences.
    compare_payloads(exp_payload : xserial_frame_payload_s, 
                     compare_dest : bool) : list of string is {
        if compare_dest and exp_payload.destination != destination {
            result.add(append("Expected destination field: ", 
                              bin(exp_payload.destination),
                              ", Actual destination field: ", 
                              bin(destination)));
        };
        if exp_payload.frame_format != frame_format {
            result.add(append("Expected format field: ", 
                              exp_payload.frame_format,
                              ", Actual format field: ", 
                              frame_format));
            return result;
        };
    }; -- compare_payloads()
    
    -- This method is called in post_generate() and also in unpack_payload()
    -- to update the status field according to the detected errors in the
    -- payload.
    update_status() is {

        -- Assume that this payload is going to be legal until we discover
        -- otherwise.
        status = {};

        -- If the frame format is illegal, then set the status field
        -- accordingly.
        if frame_format == UNDEFINED {
            status.add(BAD_FORMAT);
        };

    }; -- update_status()
    
    -- Called by Structured Messages 
    get_attribute_value(name: string): string is {
        if name == "destination" {
            result = append(destination);
        };
    };
}; -- struct xserial_frame_payload_s


-- If we have an illegal frame_format field, then none of the sub-typed
-- extensions will come into play so the remaining 8 bits of the payload
-- won't be there. We need the payload to always be 12 bits long, so extend
-- payloads with illegal frame formats to provide a dummy 8 bit field.
extend UNDEFINED xserial_frame_payload_s {

    -- This field pads out the remaining 8 bits if the frame format is
    -- illegal.
    %dummy : byte;

    -- Unpack the remaining bits into the dummy field
    unpack_payload(bitstream : list of bit, check_protocol : bool) is also {
        unpack(packing.low, bitstream[4..11], dummy);
    }; -- unpack_payload()
    
    -- Make sure that if this payload gets printed, the bad frame format
    -- is included in the string.
    nice_string(): string is also {
        result = appendf("%s BAD_FORMAT:%02b ", 
                         result, 
                         physical_frame_format.as_a(uint(bits:2)));
    }; -- nice_string()
   
    
}; -- extend UNDEFINED xserial_frame_payload_s

'>

