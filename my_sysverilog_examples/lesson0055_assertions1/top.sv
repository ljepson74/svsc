module top;
   string str1;
   string line="**** *** ** *";
   int anumber=2;
   bit clk;
   
   initial begin
      clk=0;
      #1;
   end
   always #1 clk <= ~clk;

   initial begin 
      $monitor($time," %0s: str1 is now %0s",line, str1);
      str1="blue";
      //@(posedge clk);      
      str1="red"; 
      #1;
      $finish();
   end

   //as_continuous : assert property(@(str1) str1=="red") else $display("cliff diver");

/*
   as_robot1 : assert property(@(str1) 
                              (str1=="red" && (anumber==2))) begin
      $display($time," %0s: ONE IF",line);
   end else begin 
      $display($time," %0s: ONE ELSE: %0s",line,str1);
   end
*/

   as_robot2 : assert property(@(str1)
                               (str1=="red" |-> (anumber==2))) begin
      $display($time," %0s: TWO IF",line);
   end else begin
      $display($time," %0s: TWO ELSE: %0s",line,str1);
   end
endmodule


//notes:
//1. monitor and continuous assertions need time. They dont just trigger based upon
//    changes.
//1a. monitor only shows initialization of str1 if str1 is never again set, 
// or time elapses before it is set again.
//1b. continuous assertions need time too, even if trigger has no time 

// assert (str1!="blue") else $warning("sean is king");