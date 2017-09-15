


module mod_wants_assoc_array;

   initial
     begin
	$display("STARTING OUR EXAMPLE NOW");

	//CAN SEE INT
	$display("%m: I can see the # %d",top.mod_w_assoc_array.icansee_int);

	//CANT SEE STRING
	//$display("%m: I can't see the value %s",top.mod_w_assoc_array.icansee_string);

	//CANT SEE INT OF ASSOC ARRAY
	//$display("%m: I can't see the value %d",top.mod_w_assoc_array.aa_int.aa_int[3]);

	//CANT SEE STRING OF ASSOC ARRAY
	//$display("%m: I can't see the value %s",top.mod_w_assoc_array.aa_int.aa_string[3]);
     end
   
endmodule // mod_wants_assoc_array
