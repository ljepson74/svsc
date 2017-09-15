module memory_ctrl(//Inputs
                   input bit		clk,
                   input logic 		reset,
                   input logic 		we_sys,
                   input logic 		cmd_valid_sys,
                   input logic [7:0]	addr_sys,
                   input logic [7:0]	datao_mem,

                   //Outputs
                   output logic 	we_mem,
                   output logic 	ce_mem,
                   output logic [7:0]	addr_mem,
                   output logic [7:0]	datai_mem,
                   output logic 	ready_sys,

                   //Inout
                   ref    logic [7:0]	data_sys //VCS workaround. Can't use inout
                  );

typedef enum {IDLE,
              WRITE,
              READ,
              DONE
             }mode_t;

mode_t state;

always @ (posedge clk)
  if (reset) begin
    state     <= IDLE;
    ready_sys <= 0;
    we_mem    <= 0;
    ce_mem    <= 0;
    addr_mem  <= 0;
    datai_mem <= 0;
    data_sys  <= 8'bz;
  end else begin
    case(state)
       IDLE :  begin
         ready_sys <= 1'b0;
         if (cmd_valid_sys && we_sys) begin
           addr_mem   <= addr_sys;
           datai_mem  <= data_sys;
           we_mem     <= 1'b1;
           ce_mem     <= 1'b1;
           state      <= WRITE;
         end
         if (cmd_valid_sys && ~we_sys) begin
           addr_mem   <= addr_sys;
           datai_mem  <= data_sys;
           we_mem     <= 1'b0;
           ce_mem     <= 1'b1;
           state      <= READ;
         end
       end
       WRITE : begin
         ready_sys  <= 1'b1;
         if (~cmd_valid_sys) begin
           addr_mem   <= 8'b0;
           datai_mem  <= 8'b0;
           we_mem     <= 1'b0;
           ce_mem     <= 1'b0;
           state      <= IDLE;
         end
       end 
       READ : begin
         ready_sys  <= 1'b1;
         data_sys   <= datao_mem;
         if (~cmd_valid_sys) begin
           addr_mem   <= 8'b0;
           datai_mem  <= 8'b0;
           we_mem     <= 1'b0;
           ce_mem     <= 1'b0;
           ready_sys  <= 1'b1;
           state      <= IDLE;
           data_sys   <= 8'bz;
         end 
       end 
    endcase
  end

endmodule
