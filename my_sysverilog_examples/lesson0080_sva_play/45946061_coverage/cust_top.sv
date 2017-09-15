module top;
bit clk, sig1, sig2;

always clk = #5 ~clk;

initial begin
$monitor($time," sig1=%1b sig2=%1b",sig1,sig2);
clk =0;
sig1=0;sig2=0;
repeat (11) @(posedge clk);
sig1=1;
repeat (11) @(posedge clk);
sig1=0;sig2=0;
$finish;
end

my1_cp : cover property (@(posedge clk) sig1);
my2_cp : cover property (@(posedge clk) sig2);
endmodule : top
