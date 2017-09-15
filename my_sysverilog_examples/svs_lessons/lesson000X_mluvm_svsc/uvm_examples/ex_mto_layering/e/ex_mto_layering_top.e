/*----------------------------------------------------------    
File name   : ex_mto_layering_top.e
Title       : Top file 
Project     : many to one layering example
Created     : 2007
Description : Imports the required files.
Notes       : This is one of four layering examples: One to one, 
            : One to many, Many to one and Many to many
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





import ex_mto_layering_base.e;
import ex_mto_layering_ll_pkt_env.e;
import ex_mto_layering_ul_pkt_env.e;
import ex_mto_layering_system_env.e;
import ex_mto_layering_ul_pkt_seq_lib.e;
#ifdef SPECMAN_VERSION_8_2_OR_LATER {
    import ex_mto_layering_ll_pkt_seq_lib.e;
}
#else {
    import ex_mto_layering_ll_pkt_seq_lib_using_do.e;
};
import ex_mto_layering_system_seq_lib.e;
'>
