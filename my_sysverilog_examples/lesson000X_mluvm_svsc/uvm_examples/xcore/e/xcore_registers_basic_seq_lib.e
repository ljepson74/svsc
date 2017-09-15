/*------------------------------------------------------------------------- 
File name   : xcore_registers_basic_seq_lib.e
Title       : Registers sequence lib
Project     : XCore eVC
Created     : 2008
Description : Defines sequences for programming the XCore via its registers
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

'>


<'

extend vr_ad_sequence_kind : [XCORE_XBUS_WRITE,
                              XCORE_XBUS_READ,
                              XCORE_XBUS_READ_WRITE];


extend vr_ad_sequence_driver {
    event device_reset_done;
}; 

extend vr_ad_sequence {
    // Cover the sequence. 
    // Ignore the pre-defined kinds, they do not add information to 
    // the coverage
    cover ended is {
        item kind using ignore = (kind == RANDOM or
                                  kind == SIMPLE or
                                  kind == MAIN);
    }; 

};

extend MAIN vr_ad_sequence {
  
   -- If this field is TRUE, then an objection to TEST_DONE
   -- is raised for the duration of the MAIN sequence. If this field is FALSE
   -- then the MAIN sequence does not contribute to the determination of
   -- end-of-test.
   keep soft prevent_test_done == FALSE;
   
   -- Raise an objection to TEST_DONE whenever a MAIN sequence is started.
   pre_body() @sys.any is first {
       // The vr_ad does not participate in the testflow, in this eVC,
       // so we have to add the synhcronization with reset.
       // If vr_ad uses the testflow, no need for this synch
       sync @driver.device_reset_done;

       message(LOW, "MAIN sequence started");
      if prevent_test_done {
         driver.raise_objection(TEST_DONE);
      };
   }; -- pre_body()
         
   -- Drop the objection to TEST_DONE after the MAIN sequence ends.
   post_body() @sys.any is also {
      message(LOW, "MAIN sequence finished");
      if prevent_test_done {
         driver.drop_objection(TEST_DONE);
      };
   }; -- post_body()
   
}; -- extend MAIN ...


-- The XCORE_XBUS_WRITE sequence writes a frame to the XCore. 
-- It polls the XCore to ensure that it is ready before writing the
-- frame data.
  
extend XCORE_XBUS_WRITE vr_ad_sequence {
     
   -- By defualt - take the first reg_file
   keep soft static_item == driver.addr_map.reg_file_list[0];


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
   
   !tx_data : XCORE_TX_DATA vr_ad_reg;
   !tx_mode : XCORE_TX_MODE vr_ad_reg ;

   body() @driver.clock is only {

      repeat {

            read_reg tx_data;
        } until pack(packing.low, tx_data) == 0;
      
      write_reg tx_mode {.dest == destination;
                         .frame_kind == frame_format_physical;
                         .resv == 0};

      write_reg tx_data {.data == data};
      
    }; -- body()

}; -- extend XCORE_XBUS_WRITE vr_ad_sequence



-- The XCORE_XBUS_READ sequence reads a frame from an instance of the
-- XCore. It will poll the XCore to ensure that there is valid data ready
-- before reading the frame data.
extend XCORE_XBUS_READ vr_ad_sequence {

    -- This field is used to store the payload of the received frame.
    !data : byte;
    
    -- This field is used to store the frame format of the received frame.
    !frame_format : xserial_frame_format_t;
    
    -- This field is used to store the destination of the received frame.
    !destination : uint(bits:2);

   -- By defualt - take the first reg_file
   keep soft static_item == driver.addr_map.reg_file_list[0];

    -- This field is used to store the error flag of the received frame.
   !error_flag : bool(bits : 1);

   !rx_data : XCORE_RX_DATA vr_ad_reg;
   !rx_mode : XCORE_RX_MODE vr_ad_reg ;

   body() @driver.clock is only {      

      repeat {
         read_reg rx_mode;
      } until rx_mode.valid_frame == 1;

      destination = rx_mode.dest;
      frame_format = rx_mode.frame_kind.as_a(xserial_frame_format_t);
      error_flag = rx_mode.par_err;
      read_reg rx_data;
      data = rx_data.data;

   };

}; -- extend XCORE_XBUS_READ vr_ad_sequence 



-- The XCORE_XBUS_READ_WRITE sequence reads a frame from an instance of
-- the XCore and writes it immediately back to a (potentially differenct)
-- instance of the XCore. If a frame is received with an error, it is
-- discarded.
extend XCORE_XBUS_READ_WRITE vr_ad_sequence {

    -- This field specifies the base address of the XCore device the frame is
    -- read from.
    
    -- This field specifies the base address of the XCore device the frame is
    -- written to.

   -- This field is provide to facilitate "do xcore_read".
   !xcore_read : XCORE_XBUS_READ vr_ad_sequence ;
   
   -- This field is provide to facilitate "do xcore_write".
   !xcore_write : XCORE_XBUS_WRITE vr_ad_sequence;
    
   read_reg_file : vr_ad_reg_file;
       keep soft read_reg_file  == driver.addr_map.reg_file_list[0];
   write_reg_file : vr_ad_reg_file;
       keep soft write_reg_file == driver.addr_map.reg_file_list[0];

   
   body() @driver.clock is only {
       
       do xcore_read keeping { 
          .static_item == read_reg_file ;
       }; -- body() @driver....

        if not xcore_read.error_flag {
            do xcore_write keeping {
               .frame_format == xcore_read.frame_format;
               .destination  == xcore_read.destination;
               .data         == xcore_read.data;
               .static_item  == write_reg_file;
            };
        };
        
   }; -- body()
    
}; -- extend XCORE_XBUS_READ_WRITE vr_ad_sequence 

'>

