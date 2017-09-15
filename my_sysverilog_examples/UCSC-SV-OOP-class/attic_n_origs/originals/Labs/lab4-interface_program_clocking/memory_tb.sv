module memory_tb();

   bit         clk;
   logic       reset;

   //Signals for Memory Core
   logic       we_mem;
   logic       ce_mem;
   logic [7:0] addr_mem;
   logic [7:0] datai_mem;
   logic [7:0] datao_mem;

   //Signals for Memory Controller
   logic       we_sys;
   logic       cmd_valid_sys;
   logic [7:0] addr_sys;
   logic       ready_sys;
   logic [7:0] data_sys;

   //Free running clock
   always #5 clk = !clk;


   //DUT is instantiated here
   memory_core 		memcore		(//Inputs
                                         .clk		(clk		),
                                         .reset		(reset		),
                                         .we_mem	(we_mem		),
                                         .ce_mem	(ce_mem		),
                                         .addr_mem	(addr_mem	),
                                         .datai_mem	(datai_mem	),

                                         //Output
                                         .datao_mem	(datao_mem	)
                                     	);

   memory_ctrl 		memctrl		(//Inputs
                                         .clk		(clk		),
                                         .reset		(reset		),
                                         .we_sys	(we_sys		),
                                         .cmd_valid_sys	(cmd_valid_sys	),
                                         .addr_sys	(addr_sys	),
                                         .datao_mem	(datao_mem	),

                                         //Outputs
                                         .we_mem	(we_mem		),
                                         .ce_mem	(ce_mem		),
                                         .addr_mem	(addr_mem	),
                                         .datai_mem	(datai_mem	),
                                         .ready_sys	(ready_sys	),
                                         
                                         //Inout
                                         .data_sys	(data_sys	)
                                	);

   //testcase is instantiated here
   testcase   		itestcase	(//Inputs to Design, Outputs from Program

                                         //Inout to/from Design, inout to/from Program

                                         //Output from Design, Input to Program

                                 	);

endmodule
