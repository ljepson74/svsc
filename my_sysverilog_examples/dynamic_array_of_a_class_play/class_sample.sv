class class_sample;
   integer    some_integer;

   function new();
      this.some_integer  = 0;
   endfunction
   
   function void set_integer();
      input integer input_integer;
      some_integer  = input_integer;      
      //$display(" %m: set some_integer=%0d",some_integer);      
   endfunction

   function void show_all();
      $display(" %m:   some_integer=%0d", this.some_integer);
   endfunction   
endclass

