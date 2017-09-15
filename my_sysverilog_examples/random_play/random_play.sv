//This file is made to experiment with randomness in systemverilog
// *recreate problem we had in lux with getting repeatable random numbers with sysverilog (w/ and w/o waveforming dumping)
// *determine if/how we can use randomize()

class Transaction;
   rand bit [31:0] addr, crc, data[8];

   function void display;
      $display("Transaction: %h", addr);      
   endfunction : display

   function void calc_crc;
      crc = addr ^ 1'b0;  ///junk      
   endfunction : calc_crc   
   
endclass : Transaction




module random_play();

   ///////////////////////////////////////// 
   ////// declare object            //////// 
   /////////////////////////////////////////      
   /////works
   Transaction tr  = new();
   /////doesn't work
   //      Transaction tr;
   //      tr = new();

   initial
     begin

        `ifdef DUMP_WAVES
	 $display("%t %m: dumping for NcVerilog", $time);
	 $recordfile("sandy.trn");
	 $recordvars("depth=0", random_play);
	`endif
	
	repeat(3)
	  begin
	     assert(tr.randomize());
	     $display("You got random addr: %8x", tr.addr);
	  end
     end

endmodule // random_play

