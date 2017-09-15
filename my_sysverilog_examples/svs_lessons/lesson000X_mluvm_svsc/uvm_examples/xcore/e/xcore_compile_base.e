/*------------------------------------------------------------------------- 
File name   : xcore_compile_base.e
Title       : Compile base of XCore eVC
Project     : XCore eVC
Created     : 2008
Description : This file imports the files that are to be compiled before 
            : everything
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;


import vr_ad/e/vr_ad_top;


#ifdef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_lib/e/uvm_e_top.e;
};

#ifndef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_e/e/uvm_e_top.e;
};


-- the interface eVCs
import xserial/e/xserial_top;
import xbus_e/e/xbus_top;

'>

