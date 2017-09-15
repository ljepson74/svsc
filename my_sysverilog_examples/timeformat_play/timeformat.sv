`timescale 1ns / 100ps

`define cgdsp "%g",$time," %m:"




module timeformat();

   integer cntr;

   initial
     begin
	cntr  =5;	
	$timeformat(-12,1," SCALE", 1);	
//	$monitor("%g",$time," %m:","   %t    cntr=%0d",$time,cntr);	
	$monitor(`cgdsp,"   %t    cntr=%0d",$time,cntr);	
	#4;
	cntr  =4;
	#4;
	cntr  =3;
	#4;
	cntr  =2;
	#4;
	cntr  =1;
	
     end // initial begin

//   `cgdisp("");   


endmodule

