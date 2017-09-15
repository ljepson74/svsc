/*------------------------------------------------------------------------- 
File name   : xcore_xserial_basic_seq_lib.e 
Title       : XSerial sequence lib
Project     : XCore eVC
Created     : 2008
Description : Defines XSerial sequences for sending to XCore
            : based on the seuqcnes define in the xserial eVC
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME

-------------------------------------------------------------------------*/ 

<'

package cdn_xcore;

'>

<'
extend xserial_sequence_kind : [XCORE_SEND_FRAME];

extend XCORE_SEND_FRAME xserial_sequence {

   !send_frame_seq : SIMPLE xserial_sequence;

   body() @driver.clock is {
      do send_frame_seq;
   }; -- body() @driver....

}; -- extend XCORE...

'>
   


