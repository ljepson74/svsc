`define SIZE 3

module top;
   //parameter SIZE=3;
   bit clk;
   logic [2:0] rreqs, wreqs,   rgnts;

   always clk=#5 ~clk;
   initial begin
      $monitor($time,": wreqs=%3b rreqs=%3b   rgnts=%3b",wreqs,rreqs, rgnts);
      #5;
      clk=0;
      rreqs={`SIZE{1'b0}}; rgnts={`SIZE{1'b0}};  wreqs={`SIZE{1'b0}};

      repeat (25) begin
	 rreqs=$urandom; wreqs=$urandom; rgnts=$urandom;
	 @(posedge clk); #1; //#1 added to offset next stimulus change from clk edge
      end
      $finish;
   end

   //Consider we just have 3 read and 3 write requestors to a single arbiter (no banks).
   //Grants are returned immeditatly (thru combo logic) in response to the requests
   //We want to make sure that if there are read and write requests on a clk cycle,
   //there are no read grants.
   as_sva : assert property (@(posedge clk) (rreqs && wreqs) |-> !rgnts ) else begin
      $display($time,
	       "ERROR.RB4W.|->. wreqs=%3b rreqs=%3b   rgnts=%3b",
	       wreqs,rreqs, rgnts);
   end
   
   as_sva2 : assert property (@(posedge clk)  !(rreqs && wreqs && rgnts) ) else begin
      $display($time,
	       "ERROR.RB4W.&&. wreqs=%3b rreqs=%3b   rgnts=%3b",
	       wreqs,rreqs, rgnts);
   end

endmodule : top
