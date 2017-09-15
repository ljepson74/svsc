// consumer.sv
//
// Consumer of xunit_test_output - Contains implementation of TLM analysis port of xunit_test_output

`ifndef CONSUMER_SV
`define CONSUMER_SV


// define a consumer deriving from uvm_threaded_component
class consumer #(type T=xunit_test_output) extends uvm_component;
  uvm_analysis_imp #(T,consumer #(T)) in;

  function new(string name, uvm_component parent=null);
     super.new(name,parent);
     in=new("in",this);
  endfunction


  typedef consumer#(T) this_type;
  `uvm_component_utils_begin(this_type)
  `uvm_component_utils_end

  // implement the write() function of the port
  function void write(T t);
    $display($realtime,," SV consumer received a result (xunit_test_output):%0d  \n", t.xresult);
  endfunction

  // Watchdog : after few cycles with no input - stop the test
   task watchdog(int wd_ctr);
      #wd_ctr;
      $display($realtime,," stopping the test");
      global_stop_request();      
   endtask
   
endclass

`endif //  `ifndef CONSUMER_SV
