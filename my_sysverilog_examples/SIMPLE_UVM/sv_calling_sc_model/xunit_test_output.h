// xunit_test_output.h
//
// define a data object "xunit_test_output" that derives from uvm_object;

#ifndef PACKET_H
#define PACKET_H

#include "ml_uvm.h"
using namespace tlm;
using namespace uvm;

/////////////////

// define your own data object that derives from uvm_object;
// for mixed-language UVM communication, this SystemC object has to
// match up with the corresponding uvm_object "xunit_test_output" in SystemVerilog

class xunit_test_output : public uvm_object {
public:

  // use macro to generate necessary methods that factory needs
  UVM_OBJECT_UTILS(xunit_test_output)

  xunit_test_output() { xresult = rand(); }
  xunit_test_output(int i) { xresult = i; }
  virtual ~xunit_test_output() { }

  // implement mandatory pure virtual methods

  virtual void do_print(ostream& os) const {
    os << "xunit_test_output: " << xresult << endl;
  }
  virtual void do_pack(uvm_packer& p) const {
    p << xresult;
  }
  virtual void do_unpack(uvm_packer& p) {
    p >> xresult;
  }
  virtual void do_copy(const uvm_object* rhs) {
    const xunit_test_output* drhs = DCAST<const xunit_test_output*>(rhs);
    if (!drhs) { cerr << "ERROR in do_copy" << endl; return; }
    xresult = drhs->xresult;
  }
  virtual bool do_compare(const uvm_object* rhs) const {
    const xunit_test_output* drhs = DCAST<const xunit_test_output*>(rhs);
    if (!drhs) { cerr << "ERROR in do_compare" << endl; return true; }
    if (!(xresult == drhs->xresult)) return false;
    return true;
  }
public:
  int xresult;
};

// register the data object with the factory
UVM_OBJECT_REGISTER(xunit_test_output)


#endif

