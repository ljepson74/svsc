
#include "ml_uvm.h"
using namespace tlm;
using namespace uvm;


class xunit_test_input : public uvm_object {
 public:
  
  UVM_OBJECT_UTILS(xunit_test_input)

    xunit_test_input()    {xstimulus=rand();}
    xunit_test_input(int i) {xstimulus=i;}
    virtual ~xunit_test_input() {}

    //mandatory virtual methods
    virtual void do_print(ostream& os) const {
      os << "xunit_test_input: " << xstimulus << endl;
    }

    virtual void do_pack(uvm_packer& p) const {
      p << xstimulus;
    }

    virtual void do_unpack(uvm_packer& p) const {
      p >> xstimulus;
    }

    virtual void do_copy(const uvm_object* rhs) {
      const xunit_test_input* drhs = DCAST<const xunit_test_input*>(rhs);
      if (!drhs) {cerr << "ERROR in do_copy" << endl; return; }
      xstimulus = drhs->xstimulus;
    }

    virtual bool do_compare(const uvm_object* rhs) const {
      const xunit_test_input* drhs = DCAST<const xunit_test_input*>(rhs);
      if (!dhrs) {cerr << "ERROR in do_compare" << endl; return true;
      if (!(xstimulus == drhs->xstimulus)) return false;
      return true;
    }

 public:
  input xstimulus;
};

UVM_OBJECT_REGISTER(xunit_test_input)

