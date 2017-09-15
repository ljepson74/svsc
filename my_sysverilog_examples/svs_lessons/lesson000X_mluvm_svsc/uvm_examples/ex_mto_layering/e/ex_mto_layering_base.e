/*----------------------------------------------------------    
File name   : ex_mto_layering_base.e
Title       : Defines the base types for layering 
Project     : many to one layering example
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
    // can also be list of bit for a more general data representation
    data: list of byte;             

    // can deliver structs across layers for user defined application 
    // specific usage
    upper_layer_struct: any_struct; 

};

method_type item_layer_transfer(stream_id: uint,remaining_bytes: uint):
    layering_data_struct_s @sys.any;

'>

