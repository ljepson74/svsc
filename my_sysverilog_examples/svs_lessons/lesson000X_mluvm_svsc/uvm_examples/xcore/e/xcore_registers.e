/*------------------------------------------------------------------------- 
File name   : xcore_registers.e
Title       : Registers of the XCore
Project     : XCore eVC
Created     : 2008
Description : This file defines the XCore registers
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide.

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;


'>

<'
extend vr_ad_reg_file_kind : [XCORE];

-- DUT Shadow Register definitions
--
--       NAME              REGFILE   ADDR 
--       -------           -------   ---- 
reg_def  XCORE_TX_DATA  XCORE  8'h00 { 
   -- Custom Fields
   reg_fld data       : uint(bits:8) : RW : 0 : cov;

    // Disable compare
    set_static_info() is {
        set_compare_mask(0);
    };
};

reg_def    XCORE_TX_MODE  XCORE  8'h01 { 
   -- Custom Fields
    reg_fld resv       : uint(bits:4) : RW : 0 ;
    reg_fld frame_kind : uint(bits:2) : RW : 0 ;
    reg_fld dest       : uint(bits:2) : RW : 0 : cov;

    // Disable compare
    set_static_info() is {
        set_compare_mask(0);
    };
};

reg_def    XCORE_RX_DATA  XCORE  8'h02 { 
   -- Custom Fields
   reg_fld data        : uint(bits:8) : RW : 0 : cov;

    // Disable compare
    set_static_info() is {
        set_compare_mask(0);
    };
};

reg_def    XCORE_RX_MODE  XCORE  8'h03 { 
   -- Custom Fields
    reg_fld resv       : uint(bits:2) : RW : 0 ;
    reg_fld valid_frame: uint(bits:1) : RW : 0 : cov;
    reg_fld par_err    : bool(bits:1) : RW : FALSE : cov;
    reg_fld frame_kind : uint(bits:2) : RW : 0 ;
    reg_fld dest       : uint(bits:2) : RW : 0 : cov;

    // Disable compare
    set_static_info() is {
        set_compare_mask(0);
    };

};



------------------------------------------------------------------------------
-- Integrate the register package
------------------------------------------------------------------------------
extend xbus_master_driver_u {
    vr_ad_execute_op(op_item : vr_ad_operation) : list of byte @clock is only {
        if op_item is a REG vr_ad_operation (reg_op) {
            if sequence == NULL then {
                gen sequence keeping {
                    .driver == me;
                };
            };
            if op_item.direction == WRITE {
                sequence.write(reg_op.reg.get_size(),reg_op.address, 
                    reg_op.reg.read_reg_val());
            } else {
                result = pack(packing.low,sequence.read(reg_op.reg.get_size(),
                    reg_op.address));
            };
        };
    };
};



'>
