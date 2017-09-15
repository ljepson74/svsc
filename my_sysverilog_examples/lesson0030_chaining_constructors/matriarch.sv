// Doulos SystemVerilog Class notes, page 319, Chpt19, Varying the Stimulus: 
//       "The implementation of a non-virtual method is chosen based on the type of the variable that's used to reference the object, possibly invoking a base-class method whe you are in fact operating on a derived-class object.  In most cases this is undesirable."
//
package ladies;

class grandma;
   int age = 90;   
   string title = "grandma";
   function new();
   endfunction

   function void sayhi(); $display("I am %0s. %0d",title,age);  endfunction
endclass // grammie

class momma extends grandma;
   int age = 50;   
   string title = "momma";
   function new();
   endfunction

   function void sayhi(); $display("I am %0s. %0d",title,age);  endfunction
   function void sayhi2(); $display("I am %0s. %0d",title,super.age);  endfunction
endclass // momma

class girl extends momma;
   int age = 22;
   string title = "girl";
   function new();
   endfunction

   function void sayhi(); $display("I am %0s. %0d",title,age);  endfunction
   function void sayhi2(); $display("I am %0s. %0d",title,super.age);  endfunction
endclass // her


   function void separate(input string note="uh duh");
      $display("--------%0s",note);
   endfunction

endpackage // ladies


