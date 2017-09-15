// Xbus Master monitor BFM modules on PDXP

module xbus_master_monitor_bfm (sig_request, sig_grant, sig_addr, sig_data, sig_size, sig_read, sig_write, sig_clock, sig_reset, sig_wait);


input sig_request;
input sig_grant;
input wire [15:0] sig_addr;
input wire [7:0] sig_data;
input wire [1:0] sig_size;
input sig_read;
input sig_write;
input sig_clock;
input sig_reset;
input sig_wait;

// scemi output pipe instance
scemi_output_pipe #(11,1,1) opipe();



// output data buffers to send data through pipes
bit [87:0] odata;
reg [7:0] [7:0] o_data;


reg temp_grant=0;
always@(posedge sig_grant) temp_grant = sig_grant;



reg [3:0] state=0;

int word_cnt = 0;
int i=0;

`ifdef AXIS
initial
begin
//  $ixc_ctrl("tb_import","$display");
end
`endif



always @(negedge sig_clock)
begin
  case(state)
  4'd0: begin
        if(!sig_reset && sig_request)
        begin
          state = 4'd1;
        end
        end
  4'd1: begin
        if(temp_grant)
        begin
          odata[15:0] = sig_addr;
          odata[17:16] = sig_size;
          odata[18] = sig_read;
          odata[19] = sig_write;
          //$display("MM BFM @ %0t: addr = %0x, read = %0b, write = %0b, size = %0b", $time, sig_addr, sig_read, sig_write, sig_size);
          case(odata[17:16]) 
            2'b00: word_cnt = 1;
            2'b01: word_cnt = 2;
            2'b10: word_cnt = 4;
            2'b11: word_cnt = 8;
          endcase
          //$display("MM BFM: sig_data_size = %0d", word_cnt);
          i= 0;
          temp_grant = 1'b0;
          state = 4'd2;
        end
        end
  4'd2: begin
        if(!sig_wait)
        begin
          word_cnt = word_cnt -1;
          // $display("MM BFM @ %0t: i %d data =  %0x",$time,i, sig_data); //@@
          o_data[i] = sig_data;
          i = i+1;
          if(word_cnt == 0)
          begin
           odata[31:24]=o_data[0]; odata[39:32]=o_data[1];odata[47:40]=o_data[2]; odata[55:48]=o_data[3];odata[63:56]=o_data[4]; odata[71:64]=o_data[5];odata[79:72]=o_data[6]; odata[87:80]=o_data[7]; 

	     opipe.send(1,odata,1);
            state = 4'd0;
          end
        end
        end
  endcase
end

endmodule
