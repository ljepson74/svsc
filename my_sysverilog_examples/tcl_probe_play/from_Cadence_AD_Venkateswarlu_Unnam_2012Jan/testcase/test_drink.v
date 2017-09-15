
module test_drink;

 wire   [3:0]nickel_out;
 wire  [3:0] sd1_rd_en_io;    
 reg  clk, reset;

drink_machine_top top(.clk(clk), .reset(reset), .sd1_rd_en_io(sd1_rd_en_io), .nickel_out(nickel_out)); 

initial

begin 
clk <= 0;
forever #100 clk <= ~clk;
end

initial
begin 
reset      <= 1;
#200	reset      <= 0;


$finish;
end
     initial 
$dumpports(top , "output.evcd" ,  ,2);
endmodule

