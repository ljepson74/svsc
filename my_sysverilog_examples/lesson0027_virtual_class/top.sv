module top;

// aclass h_aclass;  virtual class cannot be instantiated
   student_class h_sclass;

   initial begin
      h_sclass = new();
      h_sclass.whoami();
      h_sclass.sayhello();
   end

  
endmodule