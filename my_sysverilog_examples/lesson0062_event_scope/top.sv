// From SVSC meetup, 2015 July 20
// Some code we hacked around with.
// Trying to get event to trigger between module and class.
// Play: 
//   Swap A1 and A2. 
//   Switch the locations of the initial blocks, so order compiler
//    encounters them differs.
//   Comment out/in B1, to adjust the triggering of the event

class event_holder;
   event class_e;

   function new();
      $display(" pre trigger.");      
      ->$root.top.top_e;    //or even just ->top.top_e;
      $display(" post trigger.");      
   endfunction
endclass : event_holder


module top;
   event top_e;

   initial begin
      event_holder m_event_holder;
      $display(" Start ** ** **.");
      #1;  //B1
      m_event_holder=new();      
      #55;
      //->top_e;
   end

   initial begin
      $display(" pre event.");
      @top_e;                   //A1
      //wait(top_e.triggered);  //A2
      $display(" post event.");
   end
endmodule
