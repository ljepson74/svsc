`define friend "frauline"`include "iclp_macros.svh"


//datatype name;
//
//int my_int;  //we want this.
`define plusarg1(argA,argB,argC=,argD=)  argA argB;
//
//
`define printit(valueit) $display("%0s",valueit);

`define argdef(datatype=datatype, name=name, desc=desc, adefault=adefault) \
datatype name; \
`define fred allow_plusarg(.valtype(datatype), .arg(name), .desc(desc), .dflt(adefault)); \
`define squid $display("yodeller");
