#include "ml_uvm.h"

using namespace tlm;
using namespace ml_uvm;
using namespace uvm;

// define a producer class that derives from uvm_component;
// producer is templated by the data type T
template <typename T>
class producer : public uvm_component {
public:
  // output port
  sc_port<tlm::tlm_blocking_put_if<T > > out;

  // constructor
  producer(sc_module_name nm) : uvm_component(nm), out("out") { }

  // use macro to generate necessary methods that the factory needs
  UVM_COMPONENT_UTILS(producer)

  // override the build phase
  void build() {
    cout << "In SC producer::build" << endl;
  }

  // produce tokens in the run() process - note that
  // you should NOT declare run as a thread process, UVM
  // automatically takes care of that
  void run() {
    for (int i = 17; i < 17+5; i++) {
      T pkt(i);
      cout << endl << "########################" << endl;
      cout << sc_time_stamp() << ": SC producer, putting ";
      pkt.print(cout);
      out->put(pkt);
      wait(10, SC_NS);
    }

    // done producing tokens, wait a little, and then stop the test
    wait(100, SC_NS);
    cout << endl << "########################" << endl;
    cout << sc_time_stamp() << ": stopping test";
    uvm_stop_request();
  }
};


