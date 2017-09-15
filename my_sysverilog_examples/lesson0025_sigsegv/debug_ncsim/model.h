
#include "systemc.h"


class model : public sc_module {

public:

  sc_in<sc_logic> in;
  sc_out<sc_logic> out;

  SC_CTOR(model) : in("inPort"), out("outPort") {
    SC_METHOD(run);
    sensitive << in;
  }

  ~model() {}

  void run()
  {
    int makeSEGV = 0;
#ifdef _AIX
    makeSEGV = *((int *)(float *)( makeSEGV - 100000));
#else
    makeSEGV = *(int *)makeSEGV;
#endif

    out.write(in.read());
  }

};
