module top;
   import ladies::*;
   
   initial begin

      //handles
      grandma gr_h;
      momma   mo_h;
      girl    gi_h;

      grandma gr1;
      momma   mo1; 
      girl    gi1;
      
      gr1= new();
      mo1= new();
      gi1= new();

      gr1.sayhi;
      mo1.sayhi;      mo1.sayhi2;
      gi1.sayhi;      gi1.sayhi2;
      separate(">>>>>");
      gr_h = gr1; gr_h.sayhi;
      gr_h = mo1; gr_h.sayhi;
      gr_h = gi1; gr_h.sayhi;
      separate(">>>>>");
//    mo_h = gr1; mo_h.sayhi;
      mo_h = mo1; mo_h.sayhi;
      mo_h = gi1; mo_h.sayhi;
      separate(">>>>>");            
//    gi_h = gr1; gi_h.sayhi;
//    gi_h = mo1; gi_h.sayhi;
      gi_h = gi1; gi_h.sayhi;      
      separate(">>>>>");   

    end
endmodule