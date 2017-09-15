******************************************************************************
* Title: e SV & SC Simple TLM Example 
* Name: ex_e_sv_sc_tlm 
* Version: 2.0.1
* Requires:
  specman {8.20..}
  uvm_e {1.0..}
* Modified: 2008
* Category: examples
* Support:  
* Documentation: 
* Release notes: 

* Description:

This package contains 
	
	Three producers and three consumers, one in each language - e, SV 
	and SC.

	Several testbenches, connecting a consumer in one language, to a
        consumer in another language. 

	Several demo scripts, one for each testbench.

	The testbenches are organized under sve directory, and contain links 
        to the relevant files (files are located in the source directories -
	SV SC and e).


Available testbench examples:

     o Producer in SystemC, sending to consumer in e
     o Producer in SystemC, sending to consumer in SystemVerilog
     o Producer in e, sending to consumer in SystemVerilog
     o Producer in SystemVerilog, sending to consumer in SystemC


     Details on each example are below:



      Producer in SystemC, sending to consumer in e
      ---------------------------------------------

        <> Running the demo:

             $ML_EX_LIB/ex_e_sv_sc_tlm/sc_to_e_demo.sh

        <> Description:

             (We encourage you to open the files and see the full code.
              These files are very short and simple)

             A producer is defined in producer.h:
                 class producer : public uvm_component {
                    public:
                      sc_port<tlm::tlm_analysis_if<T > > out;

             Writing to the port, in producer.h:
                 out->write(*pkt);


             A producer is instantiated, with type of packet, in p_env.cpp:
		 UVM_COMPONENT_REGISTER_T(producer, packet)
		 SC_MODULE(sc_p_env) {
		    producer<packet> prod;
		    
             A consumer of packet is defined in consumer.e:
                 unit consumer like uvm_base_unit {
                    in_p : in interface_port of tlm_analysis of packet
                                                             is instance;


             Implementing the port, in consumer.e:
                 write (p: packet) is {


             The ports are connected in e_over_sc_tb.e:
                 unit e_over_sc_tb like uvm_env {
                     consumer     : consumer is instance;

                     connect_ports() is also {
                        ml_uvm.connect_names("sc_p_env.producer.out",
                                              consumer.in_p.e_path());
                        };


        <> Files:

             ex_e_sv_sc_tlm/examples/sc_to_e/
                 clocks_module.sv  
		 consumer.e  
		 e_over_sc_tb.e  
		 packet.e  
		 packet.h  
		 p_env.cpp  
		 producer.h
                 clocks_module.sv  


		 
      Producer in SystemC, sending to consumer in SystemVerilog
      ---------------------------------------------------------

        <> Running the demo:

             $ML_EX_LIB/ex_e_sv_sc_tlm/sc_to_sv_demo.sh

        <> Description:

             (We encourage you to open the files and see the full code.
              These files are very short and simple)

             A producer is defined in producer.h:
                 class producer : public uvm_component {
                    public:
                       sc_port<tlm::tlm_analysis_if<T > > out;

             Writing to the port, in producer.h:
                 out->write(*pkt);

             A producer is instantiated, with type of packet, in p_env.cpp:
		 UVM_COMPONENT_REGISTER_T(producer, packet)
		 SC_MODULE(sc_p_env) {
		    producer<packet> prod;
		    
             A consumer is defined in consumer.sv:
                 class consumer #(type T=packet) extends uvm_component;
                     uvm_analysis_imp #(T,consumer #(T)) in;
               
             Implementing the port, in consumer.sv:
                  task write(T t);


             The consumer is instantiated, with type of packet, and the 
	     ports are connected, in sv_over_sc_tb.sv:
                 consumer #(packet) cons;
                 ...
                 function void connect();
                    ml_uvm::external_if(cons.in, "packet"); 
                    ml_uvm::connect_names("sc_p_env.producer.out",
                                          "svtb.consumer.in");
                 endfunction



        <> Files:

             ex_e_sv_sc_tlm/examples/sc_to_sv/
		 consumer.sv 
		 sv_over_sc_tb.sv  
		 packet.sv 
		 packet.h  
		 p_env.cpp  
		 producer.h

		


      Producer in e, sending to consumer in SystemVerilog
      ---------------------------------------------------------

        <> Running the demo:

             $ML_EX_LIB/ex_e_sv_sc_tlm/e_to_sv_demo.sh

        <> Description:

             (We encourage you to open the files and see the full code.
              These files are very short and simple)

             A producer is defined in producer.e:
                unit producer like uvm_base_unit {
                    out_p : out interface_port of tlm_analysis of packet 
                                                               is instance;
           

             Writing to the port, in producer.e:
                  out_p$.write(packet);

             A producer is instantiated in e_producer_tb.e:
                unit e_producer_env like uvm_env {
                     producer     : producer is instance;
		
		    
             A consumer is defined in consumer.sv:
                 class consumer #(type T=packet) extends uvm_component;
                     uvm_analysis_imp #(T,consumer #(T)) in;
               

             Implementing the port, in consumer.sv:
                  task write(T t);


          The consumer is instantiated, with type of packet, and the 
	     ports are connected, in sv_over_e_tb.sv:
                 consumer #(packet) cons;
                 ...
                 function void connect();
                    ml_uvm::external_if(cons.in, "packet"); 
                    ml_uvm::connect_names("sys.tb.producer.out_p",
                                          "svtb.consumer.in");
                 endfunction



        <> Files:

             ex_e_sv_sc_tlm/examples/e_to_sv/
                 clocks_module.sv  
		 consumer.sv 
		 sv_over_e_tb.sv  
		 packet.sv 
		 packet.e 
		 e_producer_env.e  
		 producer.e

	




      Producer in SystemVerilog, sending to consumer in SystemC
      ---------------------------------------------------------

        <> Running the demo:

             $ML_EX_LIB/ex_e_sv_sc_tlm/sv_to_sc_demo.sh

        <> Description:

             (We encourage you to open the files and see the full code.
              These files are very short and simple)

             A producer is defined in producer.sv:
                 class producer extends uvm_component;
                       uvm_analysis_port #(packet) out; 
               

             Writing to the port, in producer.sv:
                  out.write(pkt);


             The producer is a top, as defined in the demo script:
                -uvmtop SV:producer 

		    
             A consumer is defined in consumer.h:
                   class consumer : public uvm_component, 
                                    public tlm_analysis_if<T> { 
                       public:
                           sc_export<tlm::tlm_analysis_if<T > > in;
               

             The consumer is instantiated and ports are connected, in 
             sc_over_sv_tb.cpp:
                 SC_MODULE(sctb) {
                    consumer<packet> cons;
                    SC_CTOR(sctb) : cons("consumer") 
                    {
                      ml_uvm::ml_uvm_connect("producer.out", cons.in.name());
                    }
                  };
               


        <> Files:

             ex_e_sv_sc_tlm/examples/sv_to_sc/
                 consumer.h  
		 packet.h  
		 packet.sv  
		 producer.sv  
		 sc_over_sv_tb.cpp





* Installation:

   1) For running demos:
 
      Define an environment variable, ML_EX_LIB, to be used in the demos,
      to point at location of the uvm_examples

       For example:
	     
           setenv ML_EX_LIB `ncroot`/tools/uvm/uvm_lib/uvm_ml/examples 


   2) For running demos that contain e:


      1) Make sure UVM-e is installed - uvm_lib should be in SPECMAN_PATH

         For example:

            setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm_ml/uvm_lib

           (this is done automatically to Specman users)

      2) Make sure uvm_examples is in SPECMAN_PATH
  
         For example:
	     
           setenv SPECMAN_PATH  ${SPECMAN_PATH}:/tools/uvm_ml/uvm_examples
    

  

* Content:

   sc - SystemC:
   -------------
   packet.h          : data item in SC
   producer.h        : producer in SC
   consumer.h        : producer in SC
   
   p_env.cpp         : producer env in SC - containing a producer of a packet
   sc_over_sv_tb.cpp : sctb - SC testbench -  SC consumer, 
                       connecting it to a SC producer

   sv - System Verilog:
   --------------------
   clocks_module.sv  : clock generator
   packet.sv         : data item in SV
   consumer.sv       : consumer in SV
   producer.sv       : producer in SV

   sv_over_sc_tb.sv  : svtb - SV testbench - containing a SV consumer, 
                       connecting it to a SC producer
   sv_over_e_tb.sv   : svtb - SV testbench - containing a SV consumer, 
                       connecting it to an e producer

   e:
   --
   packet.e          : data item in e
   consumer.e        : consumer in e
   producer.e        : producer in e
   e_producer_env.e  : e_producer_env - a testbench containing a producer, 
                       to be connected to a consumer in another language
   e_over_sc_tb.e    : e_over_sc_tb - e testbench - containing an e consumer, 
                       connecting it to a SC 



* To demo:

Run one of these scripts:
(See details above, under "Description" )

  $ML_EX_LIB/ex_e_sv_sc_tlm/e_to_sv_demo.sh
  $ML_EX_LIB/ex_e_sv_sc_tlm/sc_to_e_demo.sh
  $ML_EX_LIB/ex_e_sv_sc_tlm/sc_to_sv_demo.sh
  $ML_EX_LIB/ex_e_sv_sc_tlm/sv_to_sc_demo.sh 
