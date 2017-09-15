class class_mine;

   integer abc, def, ghi;
      
   function new();
      abc  = 55;
      def  = 66;
      ghi  = 77;      
   endfunction // new

   extern function void display_me;

   extern function void   tell_me_smthg;
   extern function string tell_me_smthg_else;

endclass


function void class_mine::display_me;
   string  closing_remarks;

   tell_me_smthg;
   $display(" This is it:  %0d %0d %0d",abc, def, ghi);

   //PROBLEM:  WHY DON'T EITHER OF THESE WORK?   
   //optionA. closing_remarks  = tell_me_smthg_else;   
   //optionB. closing_remarks  = class_mine::tell_me_smthg_else;
   //SOLUTION FROM CADENCE: PUT "()" at the end.
   closing_remarks  = tell_me_smthg_else();     //both this and below work
   closing_remarks  = class_mine::tell_me_smthg_else(); //both this and above work
   $display(" <<%0s>>",closing_remarks);

endfunction //


function void class_mine::tell_me_smthg;
   $display("I HAVE THIS TO TELL YOU");     
endfunction //


function string class_mine::tell_me_smthg_else;
   return " THIS WAS ALL, PATRONS.";
endfunction //

