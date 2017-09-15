class high_class;

   string  identifier;
   integer number;   
   
   function new;
      input string  whoami;
      input integer whoami_number;

      $display("We are creating a new %m.   whoami=%s  whoaminumber=%0d",whoami,whoami_number);

   endfunction


endclass // high_class
