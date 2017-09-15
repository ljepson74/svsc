//1 - NOT WORKING
`define showme(arg1,arg2) $display("Showing you, %0s & %0s",'"arg1'",'"arg2'");

//2 - WORKING
//`define showme(arg1,arg2) $display("Showing you, %0s & %0s",arg1,arg2);

`define twoargs "reign","plane"

module macro_play;

   initial begin

//1
//    `showme(cats,dogs);
      `showme(cats,dogs);
   
//2
//      `showme("cats","dogs");

//3
//      `showme(`twoargs);  //how to get two args handled as multiple args.
                          //if only we could get `twoargs to be expanded first
   end
endmodule // macro_play
