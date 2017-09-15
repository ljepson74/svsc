
Acceleration demo runs on 9.2, which does not support SDM
  
<'
#ifdef SPECMAN_VERSION_10_2_OR_LATER {
} 
#else {
    define <msg_patch'action> "msg_<msg_text'exp>" as {
        // do nothing
    };

    struct recording_config {
         register_field_attribute(struct_name: string, 
                                  field_name: string) is empty;
         register_field_attributes(struct_name: string, 
                                   field_names: list of string) is empty;
        
        register_callback_attribute(struct_name: string, 

                                    attr_name: string) is empty;
   
    };

    extend any_unit {
        tr_get_attribute_value(inst : any_struct,
                               name : string) : string is empty;
        
        assign_recording_config(cfg: recording_config) is empty;
    };
};
'>
