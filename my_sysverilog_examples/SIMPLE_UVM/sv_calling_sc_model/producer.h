// producer.h
//
// Producer template - Contains TLM analysis port. Generates
// items and write them to the port


#ifndef PRODUCER_H
#define PRODUCER_H

#include "ml_uvm.h"

using namespace tlm;
using namespace uvm;

// define a producer class that derives from uvm_component;
// producer is templated by the data type T
//good? template <typename T>
//lkj bad template <typename TT>
class producer : public uvm_component {
public:
  //lkj input port
  //lkj  sc_export<tlm::tlm_blocking_put_if<TT > > in;
  sc_export<tlm::tlm_blocking_put_if<xunit_test_input > > in;
  // output port
  //lkj  sc_port<tlm::tlm_analysis_if<T > > out;
  sc_port<tlm::tlm_analysis_if<xunit_test_output > > out;

  // constructor
  producer(sc_module_name nm) : uvm_component(nm), 
    in("in"),    
    out("out") { }

  // use macro to generate necessary methods that the factory needs
  UVM_COMPONENT_UTILS(producer)


  // produce tokens in the run() process - note that
  // you should NOT declare run as a thread process, UVM
  // automatically takes care of that
  void run() {
    for (int i = 0; i < 5; i++) {
      //      T* pkt = new T();
      //      T* pkt = new T(i);
      xunit_test_output* pkt = new xunit_test_output(i);

      cout << sc_time_stamp() << " SC producer, putting an output xunit_test_output/test-result with data " 
	                      << pkt->xresult << endl;
      out->write(*pkt);
      wait(10, SC_NS);
    }

    // Done producing tokens, wait a little, and then stop the test
    wait(1000, SC_NS);
    cout << sc_time_stamp() << " stopping the test";
    uvm_stop_request();
  }
};



#endif

