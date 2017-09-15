module top;

   string str1, str2, str3;
   int aa[string];   

   function void func(input string my1, input string my2);
      string msg  ;
      logic  match;
      int    value;
      
      
      match = (my1==my2);
      msg   = $psprintf("==:%0h:",match);
      msg   = match ? {msg,"Y. "} : {msg,"N. "};

      value = my1.compare(my2);
      msg   = $psprintf("%0s  |  str1.compare(str2):%0d:",msg, value);
      msg   = value ? {msg,"Y. "} : {msg,"N. "};

      /*
      match = uvm_re_match(my1,my2);
      msg   = $psprintf("%0s  |  uvm_re_match:%0h",msg, match);
      msg   = match ? {msg,"Y. "} : {msg,"N. "};      
*/

      $display("%0s",msg);

      value=12;
      match=value;
      $display("+match=%0d, %0b",match, match);
      
      value=-12;
      match=value;
      $display("-match=%0d, %0b",match, match);

   endfunction


   initial begin
      aa["one"]   = 1;
      aa["two"]   = 2;
      aa["three"] = 3;

      str1="big:nasty.hier.archy.path1";
      str2="big:nasty.friendly.hier-archical.path2";
      str3=str1;
      
      $display("**********************************BEGIN");
      func(str1,str2);
      func(str1,str3);
      func("fred","fred");
      $display("**********************************END");

   end

endmodule