#include "ml_uvm.h"
#include "packet.h"

using namespace tlm;
using namespace ml_uvm;
using namespace uvm;

/////////////////

// the DUT module accepts input data at export_in,
// and produces output data at port_out
template <typename T>
class dut : public sc_module, public tlm_blocking_put_if<T> {
public:
  sc_export<tlm_blocking_put_if<T> > export_in;
  sc_port<tlm_blocking_put_if<T> > port_out;
  SC_CTOR(dut) : export_in("export_in"), port_out("port_out") {
    export_in(*this);
  }
  void put(const T& data_in) {
    T data_out;
    cout << sc_time_stamp() << ": SC dut received : " << data_in << endl;

    // transform input data and produce output data
    data_out = transform(data_in);
    cout << sc_time_stamp() << ": SC dut producing output " << data_out << endl;

    // put data out on port_out
    port_out->put(data_out);
  }
  T transform(const T& data_in) {
    // process input data and produce output data
    T data_out;
    wait(10, SC_NS);
    data_out = data_in;
    data_out.next();
    return data_out;
  }
};

// the tbtop module registers the dut_wrapper's export_in and port_out
// for mixed-language UVM communication
SC_MODULE(tbtop) {
  dut<packet> dut_i;
  SC_CTOR(tbtop) : dut_i("dut") {
    cout << "tbtop::tbtop" << endl;
    ml_uvm_register(&dut_i.export_in);
    ml_uvm_register(&dut_i.port_out);
  }
};

NCSC_MODULE_EXPORT(tbtop)

