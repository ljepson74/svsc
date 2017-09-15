module top;

class grandma;
   int age = 9000;

   string title = "grandma";   
   function new(int i); 
      $display("The int i is %0d", i);
   endfunction

//   function new(int i, j); 
//      $display("The int i and j are %0d, %0d", i, j);
//   endfunction
       
   function void show(int i); $display("I am %s, %0d, %0d",title,age, i); endfunction
//   virtual function void show(int i, j); $display("I am %s, %0d, %0d, %0d",title,age, i, j); endfunction
endclass

class momma extends grandma;
   function new(int i); 
      super.new(0);
   endfunction
   int age = 50;
   string title = "momma";
   function void show(int i); $display("I am %s, %0d, %0d",title,age, i); endfunction
endclass

class girl extends momma;
   int age = 20;
   string title = "girl";
   function new();
      super.new(666);
   endfunction
//   virtual function void show(int i); $display("I am %s, %0d",title,age); endfunction
   function void show(int i, j); $display("I am %s, %0d",title,age); endfunction

endclass
   
   initial begin
//      static int i=0;
//      static int j=1;
      
      grandma g1, g_h; momma   m1, m_h;  girl    gi1, gi_h;
      g1 = new(0); m1 = new(1); gi1= new();      
      g1.show(0); m1.show(0); gi1.show(1,0);
      $display("---");
      g_h = g1;  g_h.show(0);
      g_h = m1;  g_h.show(0);
      g_h = gi1; g_h.show(0);
      $display("---");
//      m_h = g1;  m_h.show();
      m_h = m1;  m_h.show(0);
      m_h = gi1; m_h.show(0);
      $display("---");
//      gi_h = g1;  gi_h.show();
//      gi_h = m1;  gi_h.show();
      gi_h = gi1; gi_h.show(1,0);
            
   end

endmodule