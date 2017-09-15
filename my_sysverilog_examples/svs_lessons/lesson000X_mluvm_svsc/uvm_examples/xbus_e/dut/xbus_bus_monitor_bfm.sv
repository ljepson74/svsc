// Xbus Bus monitor BFM modules on PDXP


module xbus_bus_monitor_bfm (sig_grant, sig_addr, sig_data, sig_size, sig_read, sig_write, sig_clock, sig_reset, sig_wait);


input [15:0] sig_grant;
input wire [15:0] sig_addr;
input wire [7:0] sig_data;
input wire [1:0] sig_size;
input sig_read;
input sig_write;
input sig_clock;
input sig_reset;
input sig_wait;


// scemi output pipe instance for address, read/write and size etc. transfer
scemi_output_pipe #(3,1) opipe_a();
// scemi output pipe instance for grant check
scemi_output_pipe #(2,1) opipe_r();
// scemi output pipe instance for data transfer
scemi_output_pipe #(9,1) opipe_d();
// scemi output pipe instance for reset status transfer
scemi_output_pipe #(1,1) opipe_reset();


// output data buffers to send data through pipes

bit [23:0] odata_a;
bit [15:0] odata_r;
bit [71:0] odata_d;
bit [7:0] odata_reset;
reg [7:0] [7:0] o_data;



reg [15:0] temp_grant=0;
always@(sig_grant[0] or sig_grant[1] or sig_grant[2] or sig_grant[3] or sig_grant[4] or sig_grant[5] or sig_grant[6] or sig_grant[7] or sig_grant[8] or sig_grant[9] or sig_grant[10] or sig_grant[11] or sig_grant[12] or sig_grant[13] or sig_grant[14] or sig_grant[15]) 
begin
  temp_grant = sig_grant;
  odata_r = sig_grant;
  opipe_r.send(1,odata_r,1);
end



reg [3:0] state=0;

int word_cnt = 0;
int i=0;

`ifdef AXIS
initial
begin
  //$ixc_ctrl("tb_import","$display");
end
`endif


always @(negedge sig_reset)  begin odata_reset = 8'h00; opipe_reset.send(1,odata_reset,1); end
always @(posedge sig_reset)  begin odata_reset = 8'h01; opipe_reset.send(1,odata_reset,1); end




always @(negedge sig_clock)
begin
  case(state)
  4'd0: begin
        if(!sig_reset)
        begin
          state = 4'd1;
        end
        end
  4'd1: begin
        if(temp_grant[0] || temp_grant[1] || temp_grant[2] ||  temp_grant[3] || temp_grant[4] || temp_grant[5] || temp_grant[6] || temp_grant[7] || temp_grant[8] || temp_grant[9] || temp_grant[10] || temp_grant[11] || temp_grant[12] || temp_grant[13] || temp_grant[14] || temp_grant[15] )
        begin
          odata_a[15:0] = sig_addr;
          odata_a[17:16] = sig_size;
          odata_a[18] = sig_read;
          odata_a[19] = sig_write;
          odata_a[23:20] = 4'h0;
          //$display("BM BFM @ %0t: addr = %0x, read = %0b, write = %0b, size = %0b", $time, sig_addr, sig_read, sig_write, sig_size);
          case(odata_a[17:16]) 
            2'b00: word_cnt = 1;
            2'b01: word_cnt = 2;
            2'b10: word_cnt = 4;
            2'b11: word_cnt = 8;
          endcase
          //$display("BM BFM: sig_data_size = %0d", word_cnt);
          i= 0;
          temp_grant = 16'b0;
          state = 4'd2;
          opipe_a.send(1,odata_a,1);
        end
        end
  4'd2: begin
        if(!sig_wait)
        begin
          word_cnt = word_cnt -1;
          o_data[i] = sig_data;
          //$display("BM BFM @ %0t: data[%0d] =  %0x",$time,i, o_data[i]);
          i = i+1;
          if(word_cnt == 0)
          begin
            odata_d[7:0] = {6'b000000,odata_a[17:16]};
            odata_d[15:8]=o_data[0];odata_d[23:16]=o_data[1];
            odata_d[31:24]=o_data[2]; odata_d[39:32]=o_data[3];odata_d[47:40]=o_data[4]; odata_d[55:48]=o_data[5];odata_d[63:56]=o_data[6]; odata_d[71:64]=o_data[7];
            //$display("BM BFM @ %0t: odata_d[7:0] = %0x, odata_d[15:8] =  %0x",$time, odata_d[7:0], odata_d[15:8]);
            opipe_d.send(1,odata_d,1);
            state = 4'd0;
          end
        end
        end
  endcase
end

endmodule
