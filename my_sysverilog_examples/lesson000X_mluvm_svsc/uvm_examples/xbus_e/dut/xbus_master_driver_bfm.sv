// Xbus Master driver BFM modules on PDXP

`ifdef MULTIPLE_MS
// Module definition when multiple masters and slaves are instantiated in testbench

module xbus_master_driver_bfm (sig_request, sig_addr, sig_data, sig_size, sig_read, sig_write, sig_bip, sig_grant, sig_wait, sig_reset, sig_clock, slave_ctrl, active);
`else

// Module definition when single master and slave is instantiated in testbench

module xbus_master_driver_bfm (sig_request, sig_addr, sig_data, sig_size, sig_read, sig_write, sig_bip, sig_grant, sig_wait, sig_reset, sig_clock, slave_ctrl);
`endif

output reg sig_request;
output reg [15:0] sig_addr;
output reg [7:0] sig_data;
output reg [1:0] sig_size;
output reg sig_read;
output reg sig_write;
output reg sig_bip;
input sig_grant;
input sig_wait;
input sig_reset;
input sig_clock;


`ifdef MULTIPLE_MS
output reg active = 0;
`endif


// scemi input pipe instance
scemi_input_pipe #(11,1,1) ipipe();

// scemi output pipe instance
scemi_output_pipe #(11,1,1) opipe();

// input and output data buffers to receive/ send data through pipes
bit [87:0] idata;
bit [87:0] odata;

// control variables for output pipe
int num_valid_ele;
int eom;

reg [15:0] i_addr;
reg [1:0] i_size;
reg i_read;
reg i_write;
reg [3:0] i_wait_state;
reg [7:0] [7:0] i_data;
reg [3:0] i_data_size;
int n=0;





reg [3:0] state=0;

output reg slave_ctrl=0;

`ifdef AXIS
initial
begin
  //$ixc_ctrl("tb_import","$display");

end
`endif


int word_cnt=0;
int i=0;


always @(posedge sig_clock )
begin
  case(state)
    4'd0: begin
          if(sig_reset)
          begin
            sig_request  = '0;
            sig_addr     = 'h0;
            sig_data = 'h0;
            sig_size     = 'b0;
            sig_read     = 'b0;
            sig_write    = 'b0;
            sig_bip      = 'b0;
          end
          else if(ipipe.can_receive())
          begin
            ipipe.receive(1,num_valid_ele,idata, eom);
	     // $display("got from ipipe num_valid_ele %d ", num_valid_ele);
	     
            i_addr = idata[15:0];
	   //  $display("iaddr %h ", i_addr);

            i_size = idata[17:16];
           //  $display("isize %h ", i_size);
	     i_read = idata[18];
           //  $display("i_read %h ", i_read);
	     i_write = idata[19];
	    // $display("iwrite %h ", i_write);
            i_wait_state = idata[23:20];
	    // $display("iwait state %h ", i_wait_state);
	    // $display("  idata[31:24]  %x  idata[39:32] %x",  idata[31:24], idata[39:32]);
            i_data[0] = idata[31:24];i_data[1] = idata[39:32];i_data[2] = idata[47:40];i_data[3] = idata[55:48];
            i_data[4] = idata[63:56];i_data[5] = idata[71:64];i_data[6] = idata[79:72];i_data[7] = idata[87:80];
            case(i_size)
              2'b00: begin i_data_size = 4'b0001;end
              2'b01: begin i_data_size = 4'b0010;end
              2'b10: begin i_data_size = 4'b0100;end
              default: begin i_data_size = 4'b1000;end
            endcase
            //$display("Delay = %d", i_wait_state);
            if(i_wait_state > 0)
              state = 4'd5;
            else
            begin
              sig_request = 1'b1;
              state = 4'd1;
            end
          end
          end
    4'd5: begin
          i_wait_state = i_wait_state - 1;
          if(i_wait_state < 1)
          begin
            sig_request = 1'b1;
            state = 4'd1;
          end
          end
    4'd1: begin
          if(sig_grant)
          begin


`ifdef MULTIPLE_MS
            active = 1'b1;
`endif
	     
            sig_request = 1'b0;
            sig_addr = i_addr;
            sig_size = i_size;
            sig_read = i_read;
            sig_write = i_write;
            word_cnt = i_data_size;
            state = 4'd2;
            if(i_read) slave_ctrl = 1'b1;
          end
          end
    4'd2: begin
       
          sig_addr = 16'b0;
          sig_size = 2'b0;
          sig_read = 1'b0;
          sig_write = 1'b0;
          if ({i_read,i_write} == 2'b01)
            begin
	       
            n = 0;
            word_cnt = word_cnt -1;
            if (word_cnt == 0)
              sig_bip = 0;
            else
              sig_bip = 1;
            sig_data = i_data[n];
	       
            n = n+1;
            //$display("MD BFM @ %0t: data = %0x", $time, sig_data);
            if(word_cnt > 0)
              state = 4'd3;
            else
              state = 4'd4;
          end
          else 
            begin
	       
            odata = idata;
            i = 0;
            state = 4'd3;
          end
          end
    4'd3: begin

          if(!sig_wait && word_cnt > 0)
          begin
            if ({i_read,i_write} == 2'b01)
            begin 
              word_cnt = word_cnt - 1;
              if (word_cnt == 0)
                sig_bip = 0;
              else
                sig_bip = 1;
           
              //$display("MD BFM @ %0t: data = %0x", $time, sig_data);
              sig_data = i_data[n];
              n = n+1;
              if(word_cnt == 0)
              begin
                state = 4'd4;
              end
            end
            else 
            begin
              
              word_cnt = word_cnt -1;
              case(i)
                0: begin odata[31:24] = sig_data; end
                1: begin odata[39:32] = sig_data; end
                2: begin odata[47:40] = sig_data; end
                3: begin odata[55:48] = sig_data; end
                4: begin odata[63:56] = sig_data; end
                5: begin odata[71:64] = sig_data; end
                6: begin odata[79:72] = sig_data; end
                default: begin odata[87:80] = sig_data; end
              endcase
              //$display("MD BFM @ %0t: data = %0x", $time, sig_data);
              i = i+1;
              if(word_cnt == 0)
              begin
                sig_data = 8'b0;
                sig_bip = 1'b0;		 
                 opipe.send(1,odata,1);
		 slave_ctrl = 1'b0;
                state = 4'd0;
`ifdef MULTIPLE_MS
                active = 1'b0;
`endif

              end
            end
          end
          end
    4'd4: begin
          if(!sig_wait)
          begin
            sig_data = 8'b0;
            sig_bip = 1'b0;
            slave_ctrl = 1'b0;
            state = 4'd0;
`ifdef MULTIPLE_MS
            active = 1'b0;
`endif

          end
          end
  endcase
end // always @ (posedge sig_clock )
   

   
endmodule
