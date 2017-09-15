#ifndef PACKET_H
#define PACKET_H

#include "ml_uvm.h"
using namespace tlm;
using namespace uvm;

/////////////////

// define your own data object that derives from uvm_object;
// for mixed-language UVM communication, this SystemC object has to
// match up with the corresponding uvm_object "packet" in SystemVerilog

class packet : public uvm_object {
public:

  // use macro to generate necessary methods that factory needs
  UVM_OBJECT_UTILS(packet)

  packet() { data = 17; }
  packet(int i) { data = i; }
  virtual ~packet() { }

  // implement mandatory pure virtual methods

  virtual void do_print(ostream& os) const {
    os << "packet: " << data << endl;
  }
  virtual void do_pack(uvm_packer& p) const {
    p << data;
  }
  virtual void do_unpack(uvm_packer& p) {
    p >> data;
  }
  virtual void do_copy(const uvm_object* rhs) {
    const packet* drhs = DCAST<const packet*>(rhs);
    if (!drhs) { cerr << "ERROR in do_copy" << endl; return; }
    data = drhs->data;
  }
  virtual bool do_compare(const uvm_object* rhs) const {
    const packet* drhs = DCAST<const packet*>(rhs);
    if (!drhs) { cerr << "ERROR in do_compare" << endl; return true; }
    if (!(data == drhs->data)) return false;
    return true;
  }
public:
  int data;
};

// register the data object with the factory
UVM_OBJECT_REGISTER(packet)

/////////////////

#endif

