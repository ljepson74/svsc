class aclass;
   //rand logic [29:0] dataline;
   logic [29:0] dataline;
   rand int          count;

   function new();
      dataline=12'h1ACECAFE;
      count   = 99;
   endfunction

endclass


module top;

   aclass singleton;
   aclass queue[$];
   aclass array[];
   int    anumber;

   function void show_stuff();
      $write("array:");
      foreach (array[ee]) begin
	 $write("[%0d]=%0x,%0d,",ee,array[ee].dataline,array[ee].count);
      end
      $display("");
   endfunction

   initial begin
      queue.delete();
      array = new[5];
      singleton = new();

      foreach (array[rr]) begin
	 anumber++;
	 array[rr] = new();
	 array[rr].dataline = anumber;
	 array[rr].count    = anumber;

//	 if (!array[rr].dataline.randomize()) begin  //THIS IS NOT THE WAY TO DO IT.
	 if (!array[rr].randomize(dataline)) begin
	    $finish("WE DIED");
	 end
       end

      show_stuff();
   end
endmodule