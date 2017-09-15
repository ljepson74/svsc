//Interface, clocking blocks, and waiting for clock edge

interface play_if(input bit clock);
   clocking cb1 @(posedge clock);
      default input #2 output #2; //clocking_skew is irrelevant to interface inputs, right?
   endclocking
endinterface


module top;
   bit      clk;
   play_if  my_play_if(.clock(clk));

   always #5 clk=~clk;

   initial begin
      $monitor($time," clk=%1b",clk);
      clk=1;
      #100 $finish;
   end

   task tclk();
      $display($time,"     pre-clk");
      @(posedge my_play_if.clock);
      $display($time,"     post-clk");
   endtask

   task tcb1();
      $display($time,"     pre-cb1");
      @(my_play_if.cb1);
      $display($time,"     post-cb1");
   endtask

   initial begin
      #23;
      $display($time," --------------START");
      tclk();
      @(posedge my_play_if.clock);
      tclk();
      #3;
      tcb1();
      tcb1();
      @(posedge my_play_if.clock);
      tcb1();
      tclk();
      tcb1();
      #3;
      @(posedge my_play_if.clock);
      $display($time," --------------FINISH");
   end
endmodule : top
