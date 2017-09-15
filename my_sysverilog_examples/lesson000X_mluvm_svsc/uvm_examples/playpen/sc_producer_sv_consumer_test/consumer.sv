// define a consumer deriving from uvm_component
class consumer #(type T=packet) extends uvm_component;
  uvm_blocking_put_imp #(T,consumer #(T)) in;
  uvm_tlm_fifo #(T) f;

  function new(string name, uvm_component parent=null);
    super.new(name,parent);
    $display("consumer::new");
    in=new("in",this);
    f = new("fifo", this);

  endfunction

  function void build();
    $display("In SV consumer::build()");
  endfunction

  typedef consumer#(T) this_type;
  `uvm_component_utils_begin(this_type)
  `uvm_component_utils_end
   
  // implement put() task
  task put(T t);
    $display($realtime,,"consumer putting in fifo ", t.data);
    // dump the token into the fifo
    f.put(t);
  endtask
 
  task run_phase (uvm_phase phase);
    T t;
    phase.raise_objection(this);
    for (int i = 0; i < 5; i++) begin
      // get tokens from the fifo
      f.get(t); 
      $display($realtime,,"consumer::run got from fifo: ", t.data);
    end
  endtask

endclass
