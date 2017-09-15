/*----------------------------------------------------------    
File name   : ex_otm_layering_top.e
Title       : Top file 
Project     : one to many layering example
Created     : 2007
Description : Imports the required files.
Notes       : This is one of four layering examples: One to One, One to many,
            : Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 

<'

#ifdef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_lib/e/uvm_e_top.e;
};

#ifndef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_e/e/uvm_e_top.e;
};


import ex_otm_layering_base.e;
import ex_otm_layering_atm_env.e;
import ex_otm_layering_packet_env.e;
import ex_otm_layering_system_env.e;
import ex_otm_layering_packet_seq_lib.e;
import ex_otm_layering_atm_seq_lib.e;
import ex_otm_layering_system_seq_lib.e;
'>
