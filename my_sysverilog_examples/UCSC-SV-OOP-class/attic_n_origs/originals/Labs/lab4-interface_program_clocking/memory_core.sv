module memory_core (//Inputs
                    input  bit		clk,
                    input  logic 	reset,
                    input  logic	we_mem,
                    input  logic	ce_mem,
                    input  logic [7:0]	addr_mem,
                    input  logic [7:0]	datai_mem,

                    //output
                    output logic [7:0] 	datao_mem
                   );


   // Memory array
   logic [7:0] mem [0:255];

   //=================================================
   // Write Logic
   //=================================================
   always @ (posedge clk)
    if (ce_mem && we_mem) begin
      mem[addr_mem] <= datai_mem;
    end

   //=================================================
   // Read Logic
   //=================================================
   always @ (posedge clk)
    if (ce_mem && ~we_mem)  begin
      datao_mem <= mem[addr_mem];
    end

endmodule

