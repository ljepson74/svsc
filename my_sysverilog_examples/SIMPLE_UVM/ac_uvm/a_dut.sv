
module a_dut(
	   input logic clk,
	   input logic reset,
	   input logic my_input
	   );
  
   logic [63:0] my_count;

   always@(posedge clk) begin
      if (reset) begin
	 my_count  = 'b0;	 
	 $display($time," %m: JEPSON  my_count=%0x (and we did a reset)",my_count);  //use `uvm_info	 
      end
      else begin
	 my_count  = my_count + my_input;	 
	 $display($time," %m: JEPSON  my_count=%0x my_input_2=%0b", my_count, my_input);  //use `uvm_info	 
      end
   end   
   
endmodule // a_dut
