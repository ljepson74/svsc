// p_env.cpp
//
// Environment module, containing a producer of test results


#include "xunit_test_input.h"
#include "xunit_test_output.h"
#include "producer.h"


// register producer templated by xunit_test_output;
// use the appropriate macro for registering components 
// with one template parameter

UVM_COMPONENT_REGISTER_T(producer, xunit_test_output)


SC_MODULE(sc_p_env) {
  producer<xunit_test_output> prod;
  SC_CTOR(sc_p_env) : prod("producer") {

    // register the producer's port for mixed-language UVM communication
    ml_uvm::ml_uvm_register(&prod.out); 

    //lkj    // register the producer's port for mixed-language UVM communication
    //    prod.in(*this);
    // ml_uvm::ml_uvm_register(&prod.in); //lkj
  }

};

NCSC_MODULE_EXPORT(sc_p_env)

