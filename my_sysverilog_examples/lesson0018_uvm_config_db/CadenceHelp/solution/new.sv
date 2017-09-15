module svs_top ();

logic clk, resetn;
logic [31:0] outbus;


initial begin
clk <= 1'b0;
resetn <= 1'b1;
#40;
$finish;
end

always begin
#5;
clk <= ~clk;
$display("hi");
end


svs_dut svs_dut(
.clk(clk),
.resetn(resetn),

//.inbus[3](),
//.inbus[2](),
//.inbus[1](),
//.inbus[0](),

.p3(),
.p2(),
.p1(),
.p0(),
.outbus(outbus)
);

endmodule


module svs_dut(clk, resetn, outbus, .p3(inbus[3]),.p2(inbus[2]),.p1(inbus[1]),.p0(inbus[0]));

input  logic clk ;
input  logic resetn;
input  logic [31:0] inbus [3:0];
output logic [31:0] outbus;

always@(posedge clk) begin
if (!resetn) 
outbus <= 32'd0;
else 
outbus <= inbus[3]|inbus[2]|inbus[1]|inbus[0];
end

endmodule

