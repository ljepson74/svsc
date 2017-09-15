module top;

class aclass;
   rand logic [3:0] bus0;
   rand logic [3:0] bus1;
   logic      [3:0] bus2;

   function void show();
      $display("** bus0/1/2=%1h/%1h/%1h",bus0,bus1,bus2);
   endfunction
endclass

   initial begin
      aclass aclass=new();

      repeat(3) begin
         aclass.randomize();
         aclass.show();
      end
      $display("** ** ** ** ** ** **");

      repeat(3) begin
         aclass.randomize(bus1);
         aclass.show();
      end
      $display("** ** ** ** ** ** **");

      repeat(13) begin
         aclass.randomize() with {bus0==4'hB;
                                  bus1 dist {4'hE:=1, 4'hF:=1};
                                  };
         aclass.show();
      end

      $finish;
   end

endmodule