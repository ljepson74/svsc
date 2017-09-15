//Note: "~0" can be replaced by "-1", for same result
class container;
   rand logic [7:0] muggle; 
   //rand logic [31:0] muggle;
endclass

module top;
   initial begin
      container m_con=new();

      $monitor(">>>>  muggle=%4x",m_con.muggle);
      #1 m_con.muggle=~0;  //just showing myself I can set bits to all 1s
      #1 m_con.muggle='h33;
      #1 m_con.muggle=~0;
      #1;

      //Check that all bits are set
      //assert (m_con.randomize() with {muggle==~0;}) begin //BAD unless 32b muggle
      assert (m_con.randomize() with {&muggle;}) begin    //
	 $display("Randomize kosher.  muggle=%4x",m_con.muggle);
      end else begin
	 $display("Randomize failed, senor.");
      end

      assert (m_con.muggle==~0) else $display("Fail.  muggle(%8x)!=%0s", m_con.muggle,"~0");
      $finish;
   end
endmodule
