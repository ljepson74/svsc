module top;
   bit   clk;
   logic valid, new_data;
   logic [1:0] data;

   property new_data_1_works;
      logic [1:0] prev_data;
      (valid, prev_data = data) ##1 ~valid[*0:$] ##1 (new_data && valid)  |-> (data !== prev_data);
   endproperty

   property new_data_0_works;
      logic [1:0] prev_data;
      (valid, prev_data = data) ##1 ~valid[*0:$] ##1 (!new_data && valid) |-> (data === prev_data);
   endproperty
   
   always begin  #5 clk = ~clk;  end

   new_data_yes : assert property (@(posedge clk) new_data_1_works) else begin
      $warning("OUR ASSERTION new_data_1_works FAILED.");
   end

   new_data_no  : assert property (@(posedge clk) new_data_0_works) else begin
      $warning("OUR ASSERTION new_data_0_works FAILED.");
   end

   initial begin
      clk = 1;  valid=0;   new_data=0;
      #14;
      //Here I showed to myself that I must must qualify the 3rd stage of the above assertions
      // with valid being true. (ex: new_data && valid)
      //This is done by trying to make new_data_yes fail on a non-valid cycle here.
      //
      // Two cycles of 'good' data is generated.
      // Then valid is dropped to 0 (entering the 2nd stage of the assertion - I don't know correct terminology for this).
      // Then without raising valid to 1, we can move to the 3rd stage.
      // I suppose I has focused on the "~valid[*0:$]" going false before we move on, but realize now that what is happening is that it can stay true (i.e. valid=0) for as long as it will, but each clock we are just looking for what is after the "##1" to move on to the next stage.

      @(posedge clk); #2; valid=1'b1;     new_data=1'b1;      data=2'b10;
      @(posedge clk); #2; valid=1'b1;     new_data=1'b1;      data=2'b01;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b0;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b0;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b0;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b1;    //error will fire now.
      @(posedge clk); #2; valid=1'b0;     new_data=1'b1;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b1;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b1;
      @(posedge clk); #2; valid=1'b0;     new_data=1'b1;
      

      $finish;
      repeat (10) begin  clock(1);  end
      repeat (10) begin  clock(2);  end
      repeat (10) begin  clock(3);  end
      repeat (10) begin  clock(4);  end
      $finish;
   end

   task clock(input int my_type);
      @(posedge clk);
      #2;
      case (my_type)
	1 : begin valid=1'b1;     new_data=1'b1;      data=$urandom;  end
	2 : begin valid=1'b1;     new_data=1'b0;      data=$urandom;  end
	3 : begin valid=1'b1;     new_data=$urandom;  data=$urandom;  end
	4 : begin valid=$urandom; new_data=$urandom;  data=$urandom;  end
	default : begin valid=1'bX; end
      endcase
   endtask

   always@(posedge clk) begin
      //if (valid) $display($time, "   valid=%1b, new_data=%1b, data=%1x",valid,new_data,data);
      $display($time, "   valid=%1b, new_data=%1b, data=%1x",valid,new_data,data);
   end
endmodule : top

