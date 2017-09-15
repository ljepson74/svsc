/*------------------------------------------------------------------------- 
File name   : xserial_top.e
Title       : Top level of XSerial eVC
Project     : XSerial eVC
Created     : 2008
Description : This file imports all files in the eVC
Notes       : Files ending in _h.e are public files for the user to read
            : all other files could potentially be encrypted.
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

#ifdef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_lib/e/uvm_e_top.e;
};

#ifndef SPECMAN_FULL_VERSION_08_20_001 {
  import uvm_e/e/uvm_e_top.e;
};


import xserial/e/xserial_types_h.e;
import xserial/e/xserial_frame_payload_h;
import xserial/e/xserial_frame_h;
import xserial/e/xserial_frame_payload_data_h;
import xserial/e/xserial_frame_payload_message_h;
import xserial/e/xserial_sequence_h;
import xserial/e/xserial_collector_h;
import xserial/e/xserial_monitor_h;
import xserial/e/xserial_bfm_h;
import xserial/e/xserial_agent_h;
import xserial/e/xserial_coverage;
import xserial/e/xserial_bfm;
import xserial/e/xserial_collector;
import xserial/e/xserial_monitor;
import xserial/e/xserial_agent;
import xserial/e/xserial_env_h;
import xserial/e/xserial_env;
import xserial/e/xserial_protocol_checker;
import xserial/e/xserial_end_test;

'>

