/*------------------------------------------------------------------------- 
File name   : xserial_types_h.e
Title       : Common type declarations
Project     : UVM XSerial eVC 
Developers  :  
Created     : 2008
Description : This file declares common types used throughout the eVC.
Notes       : 
--------------------------------------------------------------------------- 
Copyright (c) 2008-2010 Cadence Design Systems,Inc.
All rights reserved worldwide
-------------------------------------------------------------------------*/ 

<'

package cdn_xserial;

type xserial_mode_t : [SLOW, NORMAL, FAST];

extend tf_domain_t: [XSERIAL_TF];

-- This type is used to indicate which direction of data
-- transfer the monitor is monitoring.
type xserial_direction_t : [TX, RX];


'>


