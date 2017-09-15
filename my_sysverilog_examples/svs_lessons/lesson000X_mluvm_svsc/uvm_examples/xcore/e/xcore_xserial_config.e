/*------------------------------------------------------------------------- 
File name   : xcore_xserial_config.e
Title       : XSerial eVC configuration
Project     : Xcore eVC
Created     : 2008
Description : Configures XSerial eVC for the XCore
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

extend xserial_env_name_t   : [XCORE_XSERIAL];


extend xserial_env_u {
    keep soft name == XCORE_XSERIAL;
};

'>
   
   
   Configurate the XSerial eVC
   
   Using soft constraints, so can be overwritten in the SVE

   
<'


extend XCORE_XSERIAL xserial_agent_u {
    keep soft tx_clock_period == 20 ns;
    
    keep soft tx_log_filename == "XCORE_XSERIAL_TX";
    keep soft rx_log_filename == "XCORE_XSERIAL_RX";
}; 


extend xserial_agent_u {
    -- Do not check the frames sent by the eVC agent
    keep soft check_tx_protocol == FALSE;
}; -- extend xserial_agent_u

'>
