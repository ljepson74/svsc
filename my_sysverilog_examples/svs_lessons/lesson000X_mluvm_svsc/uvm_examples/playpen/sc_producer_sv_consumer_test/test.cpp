#include "producer.h"
#include "packet.h"

// register producer templated by packet;
// use the appropriate macro for registering components 
// with one template parameter

UVM_COMPONENT_REGISTER_T(producer, packet)

// define the top test module in SystemC;
// note that both sc_modules and uvm_components can be SystemC test tops
SC_MODULE(sctest) {
  producer<packet> prod;
  SC_CTOR(sctest) : prod("producer") {
    cerr << "sctest::sctest" << endl;

    // register the producer's port for mixed-language UVM communication
    ml_uvm_register(&prod.out); 

    // connect the producer's output port to SystemVerilog consumer's 
    // imp using a mixed-languag UVM connection function
    ml_uvm_connect(prod.out.name(), "svtest.top_env.consumer.in"); 
  }
};

NCSC_MODULE_EXPORT(sctest)

