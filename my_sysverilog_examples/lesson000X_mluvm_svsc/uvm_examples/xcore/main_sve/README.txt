Incisive Plan-to-Closure Methodology 
Version 2.0.1, November 2008
Copyright (c) 2007-2010 Cadence Design Systems, Inc. 
All rights reserved worldwide.
******************************************************************************
* Title: XCore eVC Sample Environment 
* Version: 2.0.1 
* Description: 

This is an example of an SVE - Simulation & Verification Environment. 
It demonstrates a correct use of the xcore golden eVC. 

The XCore sample DUT, tested by this environment, is in shared/designs/xcore/

For more information of the XCore eVC, see xcore/PACKAGE_README

* Directory structure:

README.txt
    This file

main_sve_config.e
    Configuration file of the main_sve verification environment.
tests/
      Tests directory

   setup_test.e	
	Setup of all tests in this directory.		    
   xcore_lpbk_test.e
        Send 5 frames on XSerial. XBus reads and writes back all 5.
        This is the test of the demo.
   xcore_fill_rx_fifo_test.e	
        Send frames to the XCore. Do not read them on the XBus. XCore is 
	expected to transmit HALT frame.
   xcore_xbus_seq_test.e
        Send 5 frames on XSerial. XBus reads and writes back all 5.
	Use XBus transfer sequences instead of vr_ad.
   xcore_tx_frames_basic_test.e
        XBus writes several frames to the XCore, to be transmitted on the 
	XSerial. 
   xcore_error_rx_frames_test.e
        Send some RX frames on the XSerial. Some of them have bad parity.
   xcore_send_idle_frames_test.e
        Send frames to the XCore. Some of them are IDLE.
        This test uncovers a bug in the XCore, and a DUT error is reported.
   xcore_halt_test.e 
        Write to the XCore TX frames and send to it HALT frame. After a 
        while - send RESUME.
   xcore_virtual_seq_test.e
        Send 2 frames to the XSerial. The XBus reads the second and writes it 
        back.


* To demo:

For instructions on how to run the demo in this directory, see the
xcore/PACKAGE_README.txt.

For explanation of the configuration file and writing tests, see the 
xcore/docs/vr_xcore_overview.pdf.
