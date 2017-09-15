`include "xbus_if.sv"
`include "clkgen.v"
`include "dut_dummy.v"
`include "xbus_master_driver_bfm.sv"
`include "xbus_master_monitor_bfm.sv"
`include "xbus_slave_driver_bfm.sv"
`include "xbus_slave_monitor_bfm.sv"
`include "xbus_bus_monitor_bfm.sv"


module dut_top(rst);

reg clk;
input rst;

wire read_dut, write_dut;

xbus_if xi0();

clkgen C0(clk);

`ifdef MULTIPLE_MS

wire [1:0][15:0] master_address;
wire [1:0] [7:0] master_data;
wire [1:0] [1:0] master_size;
wire [1:0] master_read;
wire [1:0] master_write;
wire [1:0] master_bip;
wire [1:0] slave_ctrl;
wire [1:0] master_active;

reg [7:0] final_master_data;
reg final_master_read;
reg final_master_write;
reg final_slave_ctrl;
reg [15:0] final_address;
reg [1:0] final_size;
reg final_bip;

always @(master_active or master_address or master_data  or master_size or master_read or master_write or master_bip or slave_ctrl)
begin
  if(master_active[0])
  begin
    final_master_data = master_data[0];
    final_address = master_address[0];
    final_size = master_size[0];
    final_master_read = master_read[0];
    final_master_write = master_write[0];
    final_bip = master_bip[0];
    final_slave_ctrl = slave_ctrl[0];
  end
  else if(master_active[1])
  begin
    final_master_data = master_data[1];
    final_address = master_address[1];
    final_size = master_size[1];
    final_master_read = master_read[1];
    final_master_write = master_write[1];
    final_bip = master_bip[1];
    final_slave_ctrl = slave_ctrl[1];
  end
end


xbus_master_driver_bfm master_driver_bfm0(.sig_request(xi0.sig_request[0]),.sig_addr( master_address[0]),.sig_data(master_data[0]), .sig_size(master_size[0]), .sig_read(master_read[0]), .sig_write(master_write[0]), .sig_bip(master_bip[0]), .sig_grant(xi0.sig_grant[0]), .sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset),.sig_clock(xi0.sig_clock), .slave_ctrl(slave_ctrl[0]),.active(master_active[0]));

xbus_master_monitor_bfm master_monitor_bfm0(.sig_request(xi0.sig_request[0]), .sig_grant(xi0.sig_grant[0]), .sig_addr(xi0.sig_addr), .sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write), .sig_clock(xi0.sig_clock), .sig_reset(xi0.sig_reset), .sig_wait(xi0.sig_wait));

xbus_master_driver_bfm master_driver_bfm1(.sig_request(xi0.sig_request[1]),.sig_addr( master_address[1]),.sig_data(master_data[1]), .sig_size(master_size[1]), .sig_read(master_read[1]), .sig_write(master_write[1]), .sig_bip(master_bip[1]), .sig_grant(xi0.sig_grant[1]), .sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset),.sig_clock(xi0.sig_clock), .slave_ctrl(slave_ctrl[1]),.active(master_active[1]));

xbus_master_monitor_bfm master_monitor_bfm1(.sig_request(xi0.sig_request[0]), .sig_grant(xi0.sig_grant[0]), .sig_addr(xi0.sig_addr), .sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write), .sig_clock(xi0.sig_clock), .sig_reset(xi0.sig_reset), .sig_wait(xi0.sig_wait));

assign xi0.sig_read = (read_dut == 1'b0)? read_dut: final_master_read;
assign xi0.sig_write = (write_dut == 1'b0)? write_dut: final_master_write;


assign xi0.sig_addr = final_address;
assign xi0.sig_size = final_size;
assign xi0.sig_bip = final_bip;

`else

wire read_master_bfm, write_master_bfm;

wire [7:0] master_data;

wire slave_ctrl;


xbus_master_driver_bfm driver_bfm(.sig_request(xi0.sig_request[0]),.sig_addr( xi0.sig_addr),.sig_data( master_data), .sig_size(xi0.sig_size), .sig_read(read_master_bfm), .sig_write(write_master_bfm), .sig_bip(xi0.sig_bip), .sig_grant(xi0.sig_grant[0]), .sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset),.sig_clock(xi0.sig_clock), .slave_ctrl(slave_ctrl));

xbus_master_monitor_bfm monitor_bfm(.sig_request(xi0.sig_request[0]), .sig_grant(xi0.sig_grant[0]), .sig_addr(xi0.sig_addr), .sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write), .sig_clock(xi0.sig_clock), .sig_reset(xi0.sig_reset), .sig_wait(xi0.sig_wait));

`endif

`ifdef MULTIPLE_MS

wire [3:0] [7:0] slave_data;
wire [3:0] slave_error;
wire [3:0] slave_wait;
reg [3:0] slave_active=0;
reg [15:0] address;
reg flag = 0;
reg [7:0] final_slave_data;
reg final_slave_wait;
reg final_slave_error;

always @(posedge clk)
  if(xi0.sig_grant[0] || xi0.sig_grant[1])
    flag = 1'b1;

always @(negedge clk)
  if(flag)
  begin
    address = xi0.sig_addr;
    flag = 1'b0;
  end

always @(address)
begin
  if(address < 16'h4000) slave_active = 4'h1;
  else if(address < 16'h8000) slave_active = 4'h2;
  else if(address < 16'hC000) slave_active = 4'h4;
  else slave_active = 4'h8;
end

always @(slave_data or slave_active or slave_wait or slave_error)
begin
  case(slave_active)
    4'h1: begin
          final_slave_data = slave_data[0];
          final_slave_wait = slave_wait[0];
          final_slave_error = slave_error[0];
          end
    4'h2: begin
          final_slave_data = slave_data[1];
          final_slave_wait = slave_wait[1];
          final_slave_error = slave_error[1];
          end
    4'h4: begin
          final_slave_data = slave_data[2];
          final_slave_wait = slave_wait[2];
          final_slave_error = slave_error[2];
          end
    default: begin
          final_slave_data = slave_data[3];
          final_slave_wait = slave_wait[3];
          final_slave_error = slave_error[3];
          end
  endcase
end


assign xi0.sig_data = final_slave_ctrl? final_slave_data:final_master_data;
assign xi0.sig_wait = final_slave_wait;
assign xi0.sig_error = final_slave_error;



xbus_slave_driver_bfm slave_driver_bfm0(.sig_data(slave_data[0]), .sig_error(slave_error[0]), .sig_wait(slave_wait[0]), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock),.sig_read(xi0.sig_read),.sig_write(xi0.sig_write));

xbus_slave_monitor_bfm slave_monitor_bfm0(.sig_addr(xi0.sig_addr),.sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write),.sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock));

xbus_slave_driver_bfm slave_driver_bfm1(.sig_data(slave_data[1]), .sig_error(slave_error[1]), .sig_wait(slave_wait[1]), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock),.sig_read(xi0.sig_read),.sig_write(xi0.sig_write));

xbus_slave_monitor_bfm slave_monitor_bfm1(.sig_addr(xi0.sig_addr),.sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write),.sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock));

xbus_slave_driver_bfm slave_driver_bfm2(.sig_data(slave_data[2]), .sig_error(slave_error[2]), .sig_wait(slave_wait[2]), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock),.sig_read(xi0.sig_read),.sig_write(xi0.sig_write));

xbus_slave_monitor_bfm slave_monitor_bfm2(.sig_addr(xi0.sig_addr),.sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write),.sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock));

xbus_slave_driver_bfm slave_driver_bfm3(.sig_data(slave_data[3]), .sig_error(slave_error[3]), .sig_wait(slave_wait[3]), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock),.sig_read(xi0.sig_read),.sig_write(xi0.sig_write));

xbus_slave_monitor_bfm slave_monitor_bfm3(.sig_addr(xi0.sig_addr),.sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write),.sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock));




`else

wire [7:0] slave_data;

assign xi0.sig_data = slave_ctrl?slave_data: master_data;


xbus_slave_driver_bfm slave_driver_bfm(.sig_data(slave_data), .sig_error(xi0.sig_error), .sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock),.sig_read(xi0.sig_read),.sig_write(xi0.sig_write));

xbus_slave_monitor_bfm slave_monitor_bfm(.sig_addr(xi0.sig_addr),.sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write),.sig_wait(xi0.sig_wait), .sig_reset(xi0.sig_reset), .sig_clock(xi0.sig_clock));

assign xi0.sig_read = (read_dut == 1'b0)? read_dut: read_master_bfm;
assign xi0.sig_write = (write_dut == 1'b0)? write_dut: write_master_bfm;



`endif

xbus_bus_monitor_bfm bus_monitor_bfm( .sig_grant(xi0.sig_grant), .sig_addr(xi0.sig_addr), .sig_data(xi0.sig_data), .sig_size(xi0.sig_size), .sig_read(xi0.sig_read), .sig_write(xi0.sig_write), .sig_clock(xi0.sig_clock), .sig_reset(xi0.sig_reset), .sig_wait(xi0.sig_wait));


  dut_dummy dut0(
    xi0.sig_request[0],
    xi0.sig_grant[0],
    xi0.sig_request[1],
    xi0.sig_grant[1],
    xi0.sig_clock,
    xi0.sig_reset,
    xi0.sig_addr,
    xi0.sig_size,
    read_dut,
    write_dut,
    xi0.sig_start,
    xi0.sig_bip,
    xi0.sig_data,
    xi0.sig_wait,
    xi0.sig_error
  );



assign xi0.sig_clock = clk;
assign xi0.sig_reset = rst;

endmodule
