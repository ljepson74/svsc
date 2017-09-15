/*------------------------------------------------------------------------- 
File name   : xserial_port_config.e
Title       : Port config
Project     : 2008
Developers  : 
Created     : 2008
Description : This file binds the signal ports to external
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
  All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'
package cdn_xserial;


extend xserial_env_u {
    keep bind(agent.sig_reset, external);
    keep bind(agent.sig_tx_clock, external);
    keep bind(agent.sig_tx_data, external);
    keep bind(agent.sig_rx_clock, external);
    keep bind(agent.sig_rx_data, external);

    keep soft agent.sig_reset.hdl_path()    == "xbus_reset";
    keep soft agent.sig_tx_clock.hdl_path() ==  "xserial_rx_clock";
    keep soft agent.sig_tx_data.hdl_path() == "xserial_rx_data";
    keep soft agent.sig_rx_clock.hdl_path() ==  "xserial_tx_clock";
    keep soft agent.sig_rx_data.hdl_path()  ==  "xserial_tx_data";
    keep soft agent.sig_rx_data.verilog_wire() ==  TRUE;
};


extend xserial_collector_u { 
    keep bind(sig_clock, external);
    keep bind(sig_data, external);
  
    when TX xserial_collector_u { 
        keep soft sig_clock.hdl_path() == "xserial_tx_clock";
        keep soft sig_data.hdl_path() == "xserial_tx_data";
    };
     when RX xserial_collector_u { 
        keep soft sig_clock.hdl_path() == "xserial_rx_clock";
        keep soft sig_data.hdl_path() == "xserial_rx_data";
    };
}; -- extend xserial_monitor_u


extend xserial_bfm_u {
    keep bind(sig_tx_clock, external);
    keep bind(sig_tx_data, external);
  
    keep soft sig_tx_clock.hdl_path() == "xserial_tx_clock";
    keep soft sig_tx_data.hdl_path() == "xserial_tx_data";
}; -- extend xserial_bfm_u 

'>
