/*------------------------------------------------------------------------- 
File name   : xcore_top.e
Title       : Top level of XCore eVC
Project     : XCore eVC
Created     : 2008
Description : This file imports all files in the eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

import xcore_compile_base.e;


import xcore_xserial_basic_seq_lib;

import xcore_registers;
import xcore_monitor;
import xcore_ref_model;
import xcore_checker;
import xcore_env;


import xcore_registers_basic_seq_lib;
import xcore_xbus_master_basic_seq_lib;
import xcore_combined_seq_lib;
import xcore_cover;

-- Configure the eVCs
-- Configuration which is applicable in all XCore devices is in these files.
-- Configuration applicable only in specific devices or VEs, is in the SVE
import xcore_xserial_config;
import xcore_xbus_config;
import xcore_config;

'>

