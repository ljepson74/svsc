
task init;
  reset            = 1;
  enable           = 0;
  preload          = 0;
  mode             = 0;
  detect_asserted  = 0;
  preload_asserted = 0;
  preload_value    = $urandom_range(0,{SIZE{1'b1}});
  preload_data     = $urandom_range(0,{SIZE{1'b1}});
  $display("t=%3t: Selected random values - preload_value = %2d, preload_data = %2d", $time, preload_value, preload_data);
endtask
