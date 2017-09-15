// Xbus Slave monitor BFM modules on PDXP

module xbus_slave_monitor_bfm (sig_addr, sig_size, sig_read, sig_write, sig_data,sig_reset, sig_clock, sig_wait);

input wire [15:0] sig_addr;
input wire [1:0] sig_size;
input sig_read;
input sig_write;
input sig_reset;
input sig_clock;
input sig_wait;
input wire [7:0] sig_data;

// scemi output pipe instance
scemi_output_pipe #(11,1,1) opipe();


// scemi output pipe channel to communicate data values to slave driver UVC
scemi_output_pipe #(11,1,1) opipe_data();


// output data buffers to send data through pipes

bit [87:0] odata;
reg [7:0] [7:0] o_data;
int sig_data_size;



int word_count;


reg [3:0] state=0;



`ifdef AXIS
initial
begin
   //$ixc_ctrl("tb_import","$display");
end
`endif



always @(negedge sig_clock)
begin
  case(state)
    4'd0: begin
          if(!sig_reset && (sig_read  || sig_write))
          begin
            odata[15:0] = sig_addr;
            odata[17:16] = sig_size;
            odata[18] = sig_read;
            odata[19] = sig_write;
            case(odata[17:16])
              2'b00: sig_data_size = 1;
              2'b01: sig_data_size = 2;
              2'b10: sig_data_size = 4;
              2'b11: sig_data_size = 8;
            endcase // case(odata[17:16])
	  //   $display("SLAVE HW Monitor will send addr %x size %x read %x write %x ",
		    // odata[15:0], odata[17:16],   odata[18] , odata[19] );
	     
            //$display("SM BFM @ %0t: addr = %0x, read = %0b, write = %0b, size = %0b", $time, sig_addr, sig_read, sig_write, sig_size);
            o_data[0]=8'h00;o_data[1]=8'h00;o_data[2]=8'h00;o_data[3]=8'h00;
            o_data[4]=8'h00;o_data[5]=8'h00;o_data[6]=8'h00;o_data[7]=8'h00;
	     
            opipe.send(1,odata,1);
	     state = 4'd1;
          end
          end
    4'd1: begin
            word_count = 0;
            if(!sig_wait)
            begin
              //$display("SM BFM @ %0t: data = %0x", $time, sig_data);
              o_data[word_count] = sig_data;
              word_count = word_count + 1;
              if(word_count == sig_data_size)
              begin
                odata[31:24]=o_data[0]; odata[39:32]=o_data[1];odata[47:40]=o_data[2]; odata[55:48]=o_data[3];odata[63:56]=o_data[4]; odata[71:64]=o_data[5];odata[79:72]=o_data[6]; odata[87:80]=o_data[7];
		// $display("SLAVE HW Monitor will send addr %x size %x read %x write %x ",
		  //    odata[15:0], odata[17:16],   odata[18] , odata[19] );
		 opipe.send(1,odata,1);
                 opipe_data.send(1,odata,1);

		 state = 4'd0;
              end
              else
                state = 4'd2;
            end
            else
              state = 4'd2;
          end 
    4'd2: begin
          if(!sig_wait && word_count < sig_data_size)
          begin
            o_data[word_count] = sig_data;
            //$display("SM BFM @ %0t: data = %0x", $time, sig_data);
            word_count = word_count + 1;
            if(word_count == sig_data_size)
            begin
              odata[31:24]=o_data[0]; odata[39:32]=o_data[1];odata[47:40]=o_data[2]; odata[55:48]=o_data[3];odata[63:56]=o_data[4]; odata[71:64]=o_data[5];odata[79:72]=o_data[6]; odata[87:80]=o_data[7];
	       opipe.send(1,odata,1);
               opipe_data.send(1,odata,1);
	       $display("SMSMSM slave monitor sent on 2");

              state = 4'd0;
            end
          end
          end
  endcase
end


endmodule


