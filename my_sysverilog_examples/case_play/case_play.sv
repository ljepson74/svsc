//stolen & modified from http://www.asic-world.com/verilog/vbehave2.html 
/*
module case_play;
   
   reg sel;
   
   initial begin
      #1  $display ("\n     Driving 0");
      sel = 0;
      #1  $display ("\n     Driving 1");
      sel = 1;
      #1  $display ("\n     Driving x");
      sel = 1'bx;
      #1  $display ("\n     Driving z");
      sel = 1'bz;
      #1  $finish;
   end
   
   always @ (sel)
     case (sel)
       1'b0 : $display("Normal : Logic 0 on sel");
       1'b1 : $display("Normal : Logic 1 on sel");
       1'bx : $display("Normal : Logic x on sel");
       1'bz : $display("Normal : Logic z on sel");
     endcase
   
   always @ (sel)
     casex (sel)
       1'b0 : $display("CASEX  : Logic 0 on sel");
       1'b1 : $display("CASEX  : Logic 1 on sel");
       1'bx : $display("CASEX  : Logic x on sel");
       1'bz : $display("CASEX  : Logic z on sel");
     endcase
   
   always @ (sel)
     casez (sel)
       1'b0 : $display("CASEZ  : Logic 0 on sel");
       1'b1 : $display("CASEZ  : Logic 1 on sel");
       1'bx : $display("CASEZ  : Logic x on sel");
       1'bz : $display("CASEZ  : Logic z on sel");
     endcase
   
endmodule
*/

/*
module case_play;
   
   reg [1:0] sel;
   
   initial begin
      #1  $display ("\n     Driving 00");
      sel = 2'b00;
      #1  $display ("\n     Driving 01");
      sel = 2'b01;
      #1  $display ("\n     Driving 10");
      sel = 2'b10;
      #1  $display ("\n     Driving 11");
      sel = 2'b11;
      #1  $display ("\n     Driving 0z");
      sel = 2'b0z;
      #1  $finish;
   end
   
   always @ (sel)
     case (sel)
       2'b00 : $display("Normal : Logic 00 on sel");
       2'b0z : $display("Normal : Logic 01 on sel");
       2'b10 : $display("Normal : Logic 10 on sel");
       2'b11 : $display("Normal : Logic 11 on sel");
       default : $display("Normal : select is default case");
     endcase
   
endmodule
*/

module casez_example();
   reg [3:0] opcode;
   reg [1:0] a,b,c;
   reg [1:0] out;
   
   always @ (opcode or a or b or c)
     case(opcode)
       4'b111? : begin // Don't care about lower 2:1 bit, bit 0 match with x
          out = a; 
          $display("@%0dns FIRST is selected, opcode %b",$time,opcode);
       end
       4'b01?? : begin
          out = b; // bit 1:0 is don't care
          $display("@%0dns SECOND is selected, opcode %b",$time,opcode);
       end
       4'b001? : begin  // bit 0 is don't care
          out = c;
          $display("@%0dns THIRD is selected, opcode %b",$time,opcode);
       end
       default : begin
          $display("@%0dns DEFAULT is selected, opcode %b",$time,opcode);
       end
     endcase
   
   // Testbench code goes here
   always  #2  a = $random;
   always  #2  b = $random;
   always  #2  c = $random;
   
   initial begin
      opcode = 0;
      #2  opcode = 4'b1110;
      #2  opcode = 4'b0001;
      #2  opcode = 4'b1111;
      #2  opcode = 4'b0000;
      #2  $finish;
   end
   
endmodule
