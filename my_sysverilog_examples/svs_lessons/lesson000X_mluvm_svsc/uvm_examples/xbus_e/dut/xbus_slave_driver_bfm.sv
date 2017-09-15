// Xbus Slave driver BFM modules on PDXP

module xbus_slave_driver_bfm (sig_data, sig_error, sig_wait, sig_read, sig_write, sig_reset, sig_clock);

output reg [7:0] sig_data;
output reg sig_error;
output reg sig_wait;

input sig_read;
input sig_write;
input sig_reset;
input sig_clock;

// scemi input pipe instance
scemi_input_pipe #(11,1,1) ipipe();

// control variables for input pipe
int num_ele_valid;
bit eom;

// input data buffers to receive data through pipes

bit [87:0] idata;
reg [7:0] [7:0] i_data;




`ifdef AXIS
initial begin
//  $ixc_ctrl("tb_import","$display");
end
`endif

reg [3:0] state=0;



reg [3:0]  wait_count=0;
int word_count=0;
int i=0;
   

   
always @(posedge sig_clock )
begin
  case (state)
  4'd0: begin
     if(sig_reset)
        begin
          sig_error      = 1'b0;
          sig_wait       = 1'b0;
        end
        else if(ipipe.can_receive()) 
          begin
	     
          ipipe.receive(1,num_ele_valid,idata,eom);
          i = 0;
         // $display("SD BFM @ %0t: addr = %0x, read = %0b, write = %0b, size = %0b, wait_state = %d", 
	     //	   $time, idata[15:0], idata[18], idata[19], idata[17:16], idata[23:20]);
          //   $display("SD BFM idata[31:24] %x idata[39:32] %x",  idata[31:24], idata[39:32]);
	     wait_count = idata[23:20];
          case(idata[17:16])
            2'b00: begin word_count = 1;i_data[0] = idata[31:24];end
            2'b01: begin word_count = 2;i_data[0] = idata[31:24]; i_data[1] = idata[39:32];end
            2'b10: begin word_count = 4;i_data[0] = idata[31:24]; i_data[1] = idata[39:32];i_data[2] = idata[47:40]; i_data[3] = idata[55:48];end
            2'b11: begin word_count = 8;i_data[0] = idata[31:24]; i_data[1] = idata[39:32];i_data[2] = idata[47:40]; i_data[3] = idata[55:48];i_data[4] = idata[63:56]; i_data[5] = idata[71:64];i_data[6] = idata[79:72]; i_data[7] = idata[87:80];end
          endcase
          if(idata[18])
          begin
           //$display("SD BFM @ %0t: data = %0x", $time, i_data[i]);
            sig_data = i_data[i];
            i=i+1;
          end
          word_count = word_count -1;
          if (wait_count > 0)
          begin
            sig_wait = 1'b1;
            wait_count = wait_count - 1;
            state = 4'd1;
          end
          else
            state = 4'd2;
        end
        end
  4'd1: begin
        if(wait_count > 0)
          wait_count = wait_count-1;
        else
        begin
          sig_wait = 1'b0;
          state = 4'd2;
        end
        end
  4'd2: begin
        if(word_count > 0)
        begin
          if(idata[18])
          begin
            //$display("SD BFM @ %0t: data = %0x", $time, i_data[i]);
            sig_data = i_data[i];
            i = i+1;
          end
          wait_count = idata[23:20];
          word_count = word_count -1;
          if (wait_count > 0)
          begin
            sig_wait = 1'b1;
            wait_count = wait_count - 1;
            state = 4'd1;
          end
          else
            state = 4'd2;
        end
        else
        begin
          sig_wait  = 1'b0;
          sig_error = 1'b0;
          state = 4'd0;
        end
        end
  endcase
end
 

endmodule
