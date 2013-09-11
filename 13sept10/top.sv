module top;

// `define drive_this_display_that(drive_me="bus1",drive_me_value=0,display_me="bus1") \

   `define drive_this_display_that(drive_me="bus1") \
   function void drive_me``_check();\
     $display("Hi, bus1=%0d",bus1);\
       bus1 = 5;\
              $display("Now bus1=%0d",bus1);\
              endfunction

   logic [31:0] bus1 = 32'h12345678;
   logic [31:0] bus2 = 32'h99995678;

   initial begin
      bar();
      bus1=32'd888;
      somebus_check();
   end

   `drive_this_display_that()

//   `drive_this_display_that("bus2");


   function void bar();
      $display(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
   endfunction
endmodule
