module lkj_duv(
	       input logic [2:0] duv_in_a,
	       input logic [2:0] duv_in_b,
	       output logic [2:0] duv_out
	       );
	       
   assign duv_out  = duv_in_a & duv_in_b;

    
endmodule // lkj_duv



module lkj_tb();
   
   logic [2:0] tb_in_a;
   logic [2:0] tb_in_b;
   logic [2:0] tb_out_1;
   logic [2:0] tb_out_2;

   lkj_duv lkj_duv_1(
		   .duv_in_a(tb_in_a),
		   .duv_in_b(tb_in_b),
		   .duv_out(tb_out_1)
		   );

   lkj_duv lkj_duv_2(
		   .duv_in_a(~tb_in_a),
		   .duv_in_b(tb_in_b),
		   .duv_out(tb_out_2)
		   );


   initial
     begin
	$display(" ************************   STARTING NOW");
	$monitor(" tb_in_a=%3b  tb_in_b=%3b    tb_out_1=%3b  tb_out_2=%3b",  tb_in_a, tb_in_b, tb_out_1, tb_out_2);	
	#40;	
	tb_in_a  = 3'b111;
	tb_in_b  = 3'b000;
	#40;
	tb_in_a  = 3'b111;
	tb_in_b  = 3'b100;
	#40;
	tb_in_a  = 3'b101;
	tb_in_b  = 3'b101;
     end // initial
  
  
endmodule // lkj_tb




