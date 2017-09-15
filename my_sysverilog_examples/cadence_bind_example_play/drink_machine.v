module drink_machine ( 
              		nickel_in, dime_in, quarter_in, reset, clk,
              		nickel_out, dime_out, two_dime_out, dispense
            		);
    

    input nickel_in, dime_in, quarter_in, reset, clk;
    output nickel_out, dime_out, two_dime_out, dispense;
 
 
    reg [3:0] current_state;  

    reg nickel_out, dime_out, two_dime_out, dispense;

// drink machine states
`define idle                    4'd0
`define five                    4'd1
`define ten                     4'd2
`define fifteen                 4'd3
`define twenty                  4'd4
`define twenty_five             4'd5
`define thirty                  4'd6
`define thirty_five             4'd7
`define forty                   4'd8
`define forty_five              4'd9
`define fifty                   4'd10
`define nickel_out              4'd11
`define dime_out                4'd12
`define nickel_dime_out         4'd13
`define two_dime_out            4'd14

initial
 begin
                       nickel_out <= 0;
                        dime_out <= 0;
                        two_dime_out <= 0;
                        dispense <= 0;
 end
  
	always @(reset)
		if (reset)
			assign current_state = `idle; 
		else
			deassign current_state;
 
    always @(posedge clk)
 
        begin : state_machine
 
//
// state transitions and output logic
//
//// pragma assert wrongChange at (posedge clk) after (current_state == `fifty) next (quarter_in, current_state != `idle);
//
                case (current_state)
 
                    `idle :                   //4'd0
                    begin
                        nickel_out <= 0;
                        dime_out <= 0;
                        two_dime_out <= 0;
                        dispense <= 0;
                        if (nickel_in == 1)
                            begin
                                current_state <= `five;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `ten;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `twenty_five;
                            end
                    end
 
                    `five :                   //4'd1
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `ten;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `fifteen;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `thirty;
                            end
                    end
 
 
                    `ten :                   //4'd2
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `fifteen;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `twenty;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `thirty_five;
                            end
                    end
 
                    `fifteen :                    //4'd3
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `twenty;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `twenty_five;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `forty;
                            end
                    end
 
                    `twenty :                   //4'd4
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `twenty_five;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `thirty;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `forty_five;
                            end
                    end
 
                    `twenty_five :                    //4'd5
                    begin
                        if(nickel_in == 1)
                            begin
                                current_state <= `thirty;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `thirty_five;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `fifty;
                            end
                    end
 
                    `thirty :                    //4'd6
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `thirty_five;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `forty;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `nickel_out;
                            end
                    end
					
                    `thirty_five :                    //4'd7
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `forty;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `forty_five;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `dime_out;
                            end
                    end
					
                    `forty :                    //4'd8 
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `forty_five;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `fifty;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `nickel_dime_out;
                            end
                    end

                    `forty_five :                    //4'd9
                    begin
                        if (nickel_in == 1)
                            begin
                                current_state <= `fifty;
                            end
                        else if (dime_in == 1)
                            begin
                                current_state <= `nickel_out;
                            end
                        else if (quarter_in == 1)
                            begin
                                current_state <= `two_dime_out;
                            end
                    end
					
		    `fifty:                              //4'd10
		    begin
		        dispense <= 1;
		        current_state <= `idle;
			current_state <= 1;
			current_state <= `idle;
		    end
	
                    `nickel_out :                    //4'd11
                    begin
                        dispense <= 1;
                        nickel_out <= 1;  
                       	current_state <= `idle;		
                    end
					
                    `dime_out :                    //4'd12
                    begin
                        dispense <= 1;
                        dime_out <= 1;  
                        current_state <= `idle;		
                    end
					
                    `nickel_dime_out :                    //4'd13
                    begin
                        dispense <= 1;
                        nickel_out <= 1;  
                        dime_out <= 1;  
                        current_state <= `idle;		
                    end

                    `two_dime_out :                    //4'd14
                    begin
                        dispense <= 1; 
                        two_dime_out <= 1;  
			current_state <= `idle;
		    end
		    default : ;	

             endcase       

        end
 
endmodule

