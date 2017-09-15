class student_class extends aclass;

   virtual function void whoami(input string name="noone");
      $display("***** I AM %s!****** ",name);
   endfunction : whoami

   //pure virtual function void sayhello();
   function void sayhello(input string astring="texan");      
      $display(" ciao, you %0s",astring);
   endfunction : sayhello
   

endclass