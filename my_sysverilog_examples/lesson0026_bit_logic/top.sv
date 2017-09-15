task yyy(input logic [31:0] a, output [2:0] y);
//   $display("[BBQ %x]",a);
   y = 3;

   #5;

   
//   ret = a+1;
endtask  



module abby;
   bit [2:0] y;
   
   initial
     begin
	yyy(1,y);
	
       $display("yyy result %d", y);
       $display("y value %x", y);
    end 

endmodule : abby
