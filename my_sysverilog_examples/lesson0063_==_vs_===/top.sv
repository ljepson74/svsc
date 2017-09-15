
class a_class;
   rand bit   a_bit;
   rand logic a_logic;

   //constraint an_x {a_logic==1'bX;}  //illegal
endclass

module top();
   a_class a;

   initial begin
      a=new();

      $monitor("a_bit, a_logic: (%0b==%0b) is %0b.   (%0b===%0b) is %0b.",
               a.a_bit,a.a_logic,(a.a_bit==a.a_logic),  a.a_bit,a.a_logic,(a.a_bit===a.a_logic));

      //a.randomize();
      a.a_bit=0;
      a.a_logic=0;
      #1;
      a.a_logic=1;
      #1;
      a.a_logic=1'bX;
      #1;
      a.a_logic=1'bZ;
      #1;
      
      a.a_bit=1;
      a.a_logic=0;
      #1;
      a.a_logic=1;
      #1;
      a.a_logic=1'bX;
      #1;
      a.a_logic=1'bZ;
      #1;      
      $finish;
    end
 
endmodule
