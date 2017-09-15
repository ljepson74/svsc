/*----------------------------------------------------------    
File name   : ex_oto_layering_base.e
Title       : Defines the base types for layering 
Project     : one to one layering example
Created     : 2007
Description : Defines the method port for layering and the basic 
            : layering struct.
Notes       : This is one of four layering examples: One to one,
            : One to many, Many to one and Many to many
----------------------------------------------------------    
Copyright (c) 2007 Cadence Design Systems, Inc. 
All rights reserved worldwide.
Please refer to the terms and conditions in $IPCM_HOME 
----------------------------------------------------------*/ 


o Layering interface declaration

<'
struct layering_data_struct_s {
    data: list of byte;             
    -- can also be list of bit for a more general data representation

    upper_layer_struct: any_struct; 
    -- can deliver structs across layers for user defined 
    -- application specific usage
};

method_type 
    item_layer_transfer(stream_id: uint):layering_data_struct_s @sys.any;
method_type 
    check_do_available(stream_id: uint): bool;

'>

